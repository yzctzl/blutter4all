#include "pch.h"
#include "ObjectPool.h"
#include "CodeAnalyzer.h"
#include "DartApp.h"
#include "DartThreadInfo.h"
#include <cstdio>
#include <cstring>
#include <map>
#include <unordered_map>
#include <unordered_set>
#include <vm/stack_frame.h>

#ifndef NO_CODE_ANALYSIS
// SDK paths below are relative to dartsdk/<version>/runtime/. The recognizers
// describe Dart AOT operations, not byte signatures from an individual app.
// Unrecognized instructions remain in the assembly output.
namespace {
using Reg = X64::Register;
enum class BarrierKind { Object, Array };

bool isRegisterOperand(const cs_x86_op& op, x86_reg value)
{
	return op.type == X86_OP_REG && op.reg == value;
}

bool isRegisterOfSize(const cs_x86_op& op, uint8_t size)
{
	return op.type == X86_OP_REG && op.size == size;
}

bool isTaggedRegister(const cs_x86_op& op)
{
	return isRegisterOfSize(op, dart::kWordSize) || isRegisterOfSize(op, dart::kCompressedWordSize);
}

bool isImmediateOperand(const cs_x86_op& op, int64_t value)
{
	return op.type == X86_OP_IMM && op.imm == value;
}

bool isLowByteRegister(const cs_x86_op& op)
{
	if (!isRegisterOfSize(op, 1))
		return false;
	switch (op.reg) {
	case X86_REG_AH:
	case X86_REG_BH:
	case X86_REG_CH:
	case X86_REG_DH:
		return false; // The following SHR32 must consume the loaded low byte.
	default:
		return Reg{op.reg}.IsSet();
	}
}

bool isMemoryOperand(const cs_x86_op& op, x86_reg base)
{
	return op.type == X86_OP_MEM && op.mem.base == base &&
		op.mem.index == X86_REG_INVALID && op.mem.segment == X86_REG_INVALID;
}

bool isMemoryOperand(const cs_x86_op& op, x86_reg base, int64_t displacement)
{
	return isMemoryOperand(op, base) && op.mem.disp == displacement;
}

bool isInGroup(const cs_insn* insn, uint8_t group)
{
	return std::find(insn->detail->groups, insn->detail->groups + insn->detail->groups_count, group) !=
		insn->detail->groups + insn->detail->groups_count;
}

bool isMoveInstruction(unsigned id)
{
	return id == X86_INS_MOV || id == X86_INS_MOVABS;
}

// SDK Assembler::LoadImmediate uses XOR32 for zero; MOV32 zero-extends,
// whereas MOV64 sign-extends an encoded imm32. These are native integer bits,
// not proof of a tagged Dart object or a declaration type.
std::optional<int64_t> integerConstant(const cs_insn& insn)
{
	const auto& x = insn.detail->x86;
	if (x.op_count != 2 || x.operands[0].type != X86_OP_REG)
		return std::nullopt;
	const auto& dst = x.operands[0];
	if (!isRegisterOfSize(dst, 4) && !isRegisterOfSize(dst, 8))
		return std::nullopt;
	if (isMoveInstruction(insn.id) && x.operands[1].type == X86_OP_IMM)
		return dst.size == 4 ? int64_t(uint32_t(x.operands[1].imm)) : x.operands[1].imm;
	if (insn.id == X86_INS_XOR && isRegisterOperand(x.operands[1], dst.reg))
		return 0;
	return std::nullopt;
}

// SDK flow_graph_compiler_x64.cc, ParallelMoveEmitter::EmitSwap.
// A full-width register exchange preserves both values. Partial-register and
// memory XCHG have different semantics and do not propagate parameter sources.
bool isRegisterSwap(const cs_insn& insn)
{
	const auto& x = insn.detail->x86;
	if (insn.id != X86_INS_XCHG || x.op_count != 2)
		return false;
	return isRegisterOfSize(x.operands[0], dart::kWordSize) &&
		isRegisterOfSize(x.operands[1], dart::kWordSize);
}

// Decode direct edges once per function. Matchers share instruction boundaries
// and predecessor checks; this is an index, not a control-flow analysis.
class BranchTargets {
public:
	explicit BranchTargets(AsmInstructions& instructions) : instructions{instructions} {
		for (size_t i = 0; i < instructions.Count(); ++i) {
			const auto* insn = instructions.Ptr(i);
			const auto& x = insn->detail->x86;
			if (isInGroup(insn, CS_GRP_JUMP) && x.op_count == 1 && x.operands[0].type == X86_OP_IMM)
				incoming[x.operands[0].imm].push_back(i);
		}
	}
	bool contains(uint64_t address) const { return incoming.contains(address); }
	std::optional<size_t> Index(uint64_t address) const {
		if (!instructions.Count())
			return std::nullopt;
		const auto* first = instructions.FirstPtr();
		const auto* end = instructions.LastPtr() + 1;
		const auto* found = std::lower_bound(first, end, address,
			[](const cs_insn& insn, uint64_t value) { return insn.address < value; });
		if (found == end || found->address != address)
			return std::nullopt;
		return found - first;
	}
	std::optional<size_t> Destination(const cs_insn& insn) const {
		const auto& x = insn.detail->x86;
		if (x.op_count != 1 || x.operands[0].type != X86_OP_IMM)
			return std::nullopt;
		return Index(x.operands[0].imm);
	}
	bool HasOnlyIncoming(size_t first, size_t last,
		const std::vector<std::pair<size_t, size_t>>& allowed) const {
		// Inclusive end: entering a join can bypass one arm's assignments too.
		const auto end = instructions.Ptr(last)->address;
		for (auto it = incoming.lower_bound(instructions.Ptr(first)->address);
			it != incoming.end() && it->first <= end; ++it) {
			for (auto source : it->second) {
				const bool accepted = std::any_of(allowed.begin(), allowed.end(), [&](const auto& edge) {
					return instructions.Ptr(edge.first)->address == it->first && edge.second == source;
				});
				if (!accepted)
					return false;
			}
		}
		return true;
	}
	bool IsSolePredecessor(uint64_t address, uint64_t source) const {
		const auto it = incoming.find(address);
		return it != incoming.end() && it->second.size() == 1 &&
			instructions.Ptr(it->second.front())->address == source;
	}
private:
	AsmInstructions& instructions;
	std::map<uint64_t, std::vector<size_t>> incoming;
};

// Explicit and implicit writes use the same physical-register identity. A
// partial write kills provenance just as a full-width write does.
template <typename Visitor>
void visitWrittenRegisters(const cs_insn& insn, Visitor visit)
{
	const auto& detail = *insn.detail;
	for (unsigned i = 0; i < detail.x86.op_count; ++i) {
		const auto& op = detail.x86.operands[i];
		if (op.type == X86_OP_REG && (op.access & CS_AC_WRITE) && Reg{op.reg}.IsSet())
			visit(Reg{op.reg});
	}
	for (unsigned i = 0; i < detail.regs_write_count; ++i) {
		const Reg reg{static_cast<x86_reg>(detail.regs_write[i])};
		if (reg.IsSet())
			visit(reg);
	}
}

// These predicates describe entry-block boundaries, not parameter patterns.
// Frame aliases stop provenance because later indirect writes may reuse a slot.
bool isFrameRegister(x86_reg reg)
{
	return reg == X86_REG_RBP || reg == X86_REG_RSP;
}

bool isVmStateRegister(Reg reg)
{
	return reg == Reg{dart::THR} || reg == Reg{dart::PP} ||
		reg == Reg{dart::SPREG} || reg == Reg{dart::FPREG};
}

bool isControlTransfer(const cs_insn& insn)
{
	for (auto group : {CS_GRP_CALL, CS_GRP_JUMP, CS_GRP_RET}) {
		if (isInGroup(&insn, group))
			return true;
	}
	return false;
}

bool isTrap(const cs_insn& insn)
{
	return isInGroup(&insn, CS_GRP_INT) || insn.id == X86_INS_INT3 ||
		insn.id == X86_INS_UD2 || insn.id == X86_INS_HLT;
}

// SDK: vm/compiler/backend/il_x64.cc, CheckStackOverflowInstr::EmitNativeCode.
// The following JBE is checked by the IL matcher. Entry provenance stops at
// the comparison itself, before the branch can reach its slow path.
bool isStackLimitCompare(const cs_insn& insn)
{
	if (insn.id != X86_INS_CMP)
		return false;
	const auto& x = insn.detail->x86;
	if (x.op_count != 2)
		return false;
	if (!isRegisterOperand(x.operands[0], X86_REG_RSP))
		return false;
	return isMemoryOperand(x.operands[1], CSREG_DART_THR, dart::Thread::stack_limit_offset());
}

bool escapesFrame(const cs_insn& insn)
{
	const auto& x = insn.detail->x86;
	if (x.op_count != 2) return false;
	const auto& source = x.operands[1];
	if (insn.id == X86_INS_LEA)
		return source.type == X86_OP_MEM && isFrameRegister(source.mem.base);
	return isMoveInstruction(insn.id) && source.type == X86_OP_REG && isFrameRegister(source.reg);
}

// Like ARM64's getArrayOp, decode the memory operation before assigning Dart
// semantics. A MOV between registers or an immediate store is not this shape.
struct MemoryAccess {
	const cs_x86_op& memory;
	const cs_x86_op& value;
	bool isLoad;
};

std::optional<MemoryAccess> getMemoryAccess(const cs_insn& insn)
{
	switch (insn.id) {
	case X86_INS_MOV:
	case X86_INS_MOVSX:
	case X86_INS_MOVZX:
	case X86_INS_MOVSXD:
	case X86_INS_MOVSS:
	case X86_INS_MOVSD:
		break;
	default:
		return std::nullopt;
	}
	const auto& x = insn.detail->x86;
	if (x.addr_size != dart::kWordSize)
		return std::nullopt; // An address-size override truncates the object pointer.
	if (x.op_count != 2)
		return std::nullopt;
	const auto& destination = x.operands[0];
	const auto& source = x.operands[1];
	if (destination.type == X86_OP_REG && source.type == X86_OP_MEM)
		return MemoryAccess{source, destination, true};
	if (destination.type == X86_OP_MEM && (source.type == X86_OP_REG || source.type == X86_OP_IMM))
		return MemoryAccess{destination, source, false};
	return std::nullopt;
}

// SDK: assembler_x64.cc, ElementAddressForIntIndex / ElementAddressForRegIndex;
// il_x64.cc, LoadIndexedInstr / StoreIndexedInstr. Decode an index only
// after the caller proves the payload layout. Register scales distinguish
// native indices from tagged Smis; constant offsets must align to the element.
std::optional<VarStorage> getElementIndex(const cs_x86_op& memory, intptr_t payload,
	ArrayOp& operation)
{
	const auto& address = memory.mem;
	if (address.index == X86_REG_INVALID) {
		const auto bytes = address.disp + dart::kHeapObjectTag - payload;
		if (bytes < 0 || bytes % operation.size || bytes / operation.size > INT32_MAX)
			return std::nullopt;
		return VarStorage::NewSmallImm(bytes / operation.size);
	}
	if (address.disp + dart::kHeapObjectTag != payload || !Reg{address.index}.IsSet())
		return std::nullopt;
	if (address.scale == operation.size)
		operation.indexUnboxed = true;
	else if (operation.size == 1 || address.scale != operation.size / 2)
		return std::nullopt;
	return VarStorage{Reg{address.index}};
}

// SDK LoadIndexedInstr (ARM64 and x64) chooses the access from the element
// representation. Keep integer extension separate from ordinary MOV fields;
// a signed table entry, for example, is not a compressed object reference.
std::optional<ArrayOp> getTypedIntegerLoad(int cid)
{
	switch (cid) {
	case dart::kTypedDataInt8ArrayCid: return ArrayOp{1, true, ArrayOp::TypedSigned};
	case dart::kTypedDataUint8ArrayCid:
	case dart::kTypedDataUint8ClampedArrayCid: return ArrayOp{1, true, ArrayOp::TypedUnsigned};
	case dart::kTypedDataInt16ArrayCid: return ArrayOp{2, true, ArrayOp::TypedSigned};
	case dart::kTypedDataUint16ArrayCid: return ArrayOp{2, true, ArrayOp::TypedUnsigned};
	case dart::kTypedDataInt32ArrayCid: return ArrayOp{4, true, ArrayOp::TypedSigned};
	case dart::kTypedDataUint32ArrayCid: return ArrayOp{4, true, ArrayOp::TypedUnsigned};
	case dart::kTypedDataInt64ArrayCid: return ArrayOp{8, true, ArrayOp::TypedSigned};
	case dart::kTypedDataUint64ArrayCid: return ArrayOp{8, true, ArrayOp::TypedUnsigned};
	default: return std::nullopt; // External data, views and FP need other paths.
	}
}

bool isTypedIntegerLoad(const cs_insn& insn, const ArrayOp& operation)
{
	const auto& x = insn.detail->x86;
	const auto& value = x.operands[0];
	if (x.operands[1].size != operation.size)
		return false;
	if (operation.size == 8)
		return insn.id == X86_INS_MOV && value.size == 8;
	if (operation.arrType == ArrayOp::TypedSigned) {
		if (value.size != 8)
			return false;
		return insn.id == (operation.size == 4 ? X86_INS_MOVSXD : X86_INS_MOVSX);
	}
	if (operation.size == 4)
		return insn.id == X86_INS_MOV && value.size == 4; // Zero-extends to 64 bits.
	if (value.size != 4 && value.size != 8)
		return false;
	return insn.id == X86_INS_MOVZX;
}

bool poolOffset(DartApp& app, const cs_x86_op& op, intptr_t& offset)
{
	// SDK: vm/compiler/assembler/assembler_x64.cc,
	// Assembler::LoadWordFromPoolIndex / StoreWordToPoolIndex.
	// PP is a tagged ObjectPool pointer on x64. Internal pool offsets use
	// element_offset(), so add the tag back before looking up the entry.
	// Alignment matters: IndexFromOffset alone would truncate a bad offset.
	if (!isMemoryOperand(op, CSREG_DART_PP))
		return false;
	offset = op.mem.disp + dart::kHeapObjectTag;
	const auto first = dart::ObjectPool::element_offset(0);
	if (offset < first)
		return false;
	if ((offset - first) % dart::kWordSize != 0)
		return false;
	return PoolIndexFromOffset(offset) < app.GetObjectPool().Length();
}

std::unique_ptr<VarValue> threadConstant(const cs_x86_op& operand)
{
	if (!isMemoryOperand(operand, CSREG_DART_THR)) return nullptr;
	if (operand.mem.disp == dart::Thread::object_null_offset()) return std::make_unique<VarNull>();
	if (operand.mem.disp == dart::Thread::bool_true_offset()) return std::make_unique<VarBoolean>(true);
	if (operand.mem.disp == dart::Thread::bool_false_offset()) return std::make_unique<VarBoolean>(false);
	return nullptr;
}

#ifdef HAS_INIT_ASYNC
// SDK history: bf4bb953081f11fbec9a1c0ea08b428c744b369e introduced the
// suspend/resume async implementation and InitSuspendableFunctionStubABI.
// SDK: vm/compiler/backend/il.cc, Call1ArgStubInstr; compiler/stub_code_compiler.cc,
// GenerateInitSuspendableFunctionStub. Recognize the actual InitAsync stub,
// not a function name or all suspendable-function initializers.
// Reuse LoadValue IL, like ARM64; null denotes erased type arguments here,
// not the Dart type Null. Runtime-computed type arguments remain an ordinary call.
static std::unique_ptr<InitAsyncInstr> processInitAsyncInstr(
	DartApp& app, DartFnBase* function, const LoadValueInstr* load, AddrRange callRange)
{
	if (!function || !function->IsStub())
		return nullptr;
	if (function->AsStub()->kind != DartStub::InitAsyncStub)
		return nullptr;
	if (!load || load->End() != callRange.start)
		return nullptr;
	if (load->dstReg != Reg{dart::InitSuspendableFunctionStubABI::kTypeArgsReg})
		return nullptr;

	const DartTypeArguments* arguments = nullptr;
	if (load->val.ValueTypeId() == dart::kNullCid)
		arguments = &DartTypeArguments::Null;
	else if (load->val.ValueTypeId() == dart::kTypeArgumentsCid)
		arguments = &load->val.Get<VarTypeArgument>()->typeArgs;
	else
		return nullptr;

	auto* returnType = app.TypeDb()->FindOrAdd(app.DartFutureCid(), arguments);
	return std::make_unique<InitAsyncInstr>(AddrRange(load->Start(), callRange.end), returnType);
}
#endif
// The entry frame bounds incoming stack slots and local spills. Optional
// stack allocation is not a parameter operation.
// Capstone reports XMM register width as 16 even for scalar MOVSD. Only the
// low word is a parameter value; a memory operand must still be exactly 8 bytes.
// SDK flow_graph_compiler_x64.cc, FlowGraphCompiler::EmitMove:
// MOVAPS is the normal FPU register copy, including unboxed Doubles.
// Accept vector copies only between XMM registers, never vector stack spills.
bool isParameterValueMove(const cs_insn& insn)
{
	const auto& x = insn.detail->x86;
	if (x.op_count != 2 || x.addr_size != dart::kWordSize)
		return false;
	// MOVQ preserves the complete scalar bits across CPU/XMM registers. It
	// proves a source transfer, not a Dart double/integer declaration type.
	if (insn.id == X86_INS_MOVQ && x.operands[0].type == X86_OP_REG && x.operands[1].type == X86_OP_REG) {
		const Reg dst{x.operands[0].reg}, src{x.operands[1].reg};
		return dst.IsSet() && src.IsSet() && dst.IsDecimal() != src.IsDecimal() &&
			x.operands[dst.IsDecimal() ? 1 : 0].size == dart::kWordSize;
	}
	if (insn.id == X86_INS_MOVAPS || insn.id == X86_INS_MOVAPD) {
		for (const auto& op : {x.operands[0], x.operands[1]})
			if (op.type != X86_OP_REG || !Reg{op.reg}.IsDecimal())
				return false;
		return true;
	}
	if (insn.id != X86_INS_MOVSD)
		return isMoveInstruction(insn.id) && x.operands[0].size == dart::kWordSize &&
			x.operands[1].size == dart::kWordSize;
	for (const auto& op : {x.operands[0], x.operands[1]}) {
		if (op.type == X86_OP_MEM && op.size == 8)
			continue;
		if (op.type != X86_OP_REG || !Reg{op.reg}.IsDecimal())
			return false;
	}
	return true;
}

bool endsParameterEntry(const cs_insn& insn, const BranchTargets& targets)
{
	if (targets.contains(insn.address))
		return true;
	if (isControlTransfer(insn) || isTrap(insn))
		return true;
	if (isStackLimitCompare(insn) || escapesFrame(insn))
		return true;

	bool writesFrame = false;
	visitWrittenRegisters(insn, [&](Reg reg) {
		writesFrame |= reg == Reg{dart::FPREG} || reg == Reg{dart::SPREG};
	});
	return writesFrame;
}

// A matcher gets its own cursor. Failure discards that cursor; only a complete
// match advances the main loop. Unlike ARM64, x64 has variable-size instructions,
// so all movement uses the decoded array, never byte arithmetic or a sentinel.
class InsnCursor
{
public:
	InsnCursor(AsmInstructions& instructions, const BranchTargets& targets, size_t start)
		: instructions{instructions}, targets{targets}, start{start}, index{start} {}

	bool Is(unsigned id, unsigned operands) const {
		if (!IsAvailable() || Current()->id != id)
			return false;
		return Current()->detail->x86.op_count == operands;
	}
	// Primitive instruction shapes, not Dart pattern alternatives. Semantic
	// matchers still prove their registers, layouts, edges and VM metadata.
	bool RegOp(unsigned id, uint8_t width = dart::kWordSize) const {
		return Is(id, 2) && isRegisterOfSize(Op(0), width);
	}
	bool Branch(unsigned id) const {
		return Is(id, 1) && Op(0).type == X86_OP_IMM;
	}
	bool Immediate(unsigned id, x86_reg reg, int64_t value) const {
		return Is(id, 2) && isRegisterOperand(Op(0), reg) && isImmediateOperand(Op(1), value);
	}
	bool Move(x86_reg destination, x86_reg source) const {
		return Is(X86_INS_MOV, 2) && isRegisterOperand(Op(0), destination) && isRegisterOperand(Op(1), source);
	}
	bool Load(x86_reg base, uint8_t width = dart::kWordSize) const {
		return RegOp(X86_INS_MOV, width) && Op(1).size == width &&
			isMemoryOperand(Op(1), base) && Current()->detail->x86.addr_size == dart::kWordSize;
	}
	bool LoadFrom(x86_reg base, intptr_t offset, uint8_t width = dart::kWordSize) const {
		return Load(base, width) && Op(1).mem.disp == offset;
	}
	bool IsAvailable() const {
		if (index >= instructions.Count())
			return false;
		return index == start || !targets.contains(Current()->address) || localTargets.contains(Current()->address);
	}
	// A compound operation may contain its own diamond. Admit that join only
	// when the declared branch is its sole decoded incoming direct edge.
	bool AcceptLocalTarget(uint64_t address, uint64_t branchAddress) {
		if (address <= instructions.Ptr(start)->address || !targets.Index(address) ||
			!targets.IsSolePredecessor(address, branchAddress))
			return false;
		localTargets.insert(address);
		return true;
	}
	const cs_x86_op& Op(size_t operand) const { return Current()->detail->x86.operands[operand]; }
	cs_insn* Current() const { return instructions.Ptr(index); }
	void Next() { ++index; }
	size_t Position() const { return index; }
	void SetPosition(size_t position) { index = position; }
	AddrRange Range() const {
		const auto end = Current()->address + Current()->size;
		return AddrRange(instructions.Ptr(start)->address, end);
	}

private:
	AsmInstructions& instructions;
	const BranchTargets& targets;
	std::unordered_set<uint64_t> localTargets;
	size_t start;
	size_t index;
};

bool readEntryFrame(AsmInstructions& instructions, const BranchTargets& targets,
	size_t& begin, int64_t& frameSize)
{
	InsnCursor cursor{instructions, targets, 0};
	if (!cursor.Is(X86_INS_PUSH, 1) || !isRegisterOperand(cursor.Op(0), X86_REG_RBP) ||
		targets.contains(cursor.Current()->address))
		return false;
	cursor.Next();
	if (!cursor.Move(X86_REG_RBP, X86_REG_RSP))
		return false;
	cursor.Next();
	begin = cursor.Position();
	frameSize = 0;
	if (cursor.Is(X86_INS_SUB, 2) && isRegisterOperand(cursor.Op(0), X86_REG_RSP) &&
		cursor.Op(1).type == X86_OP_IMM && cursor.Op(1).imm > 0 && cursor.Op(1).imm <= INT32_MAX) {
		frameSize = cursor.Op(1).imm;
		++begin;
	}
	return true;
}

// SDK CallCFunction reserves target-ABI shadow space. Its optional immediate
// restoration uses the same size; by default the surrounding scope restores
// RSP instead. SysV reserves no shadow space.
bool consumeNativeShadowSpace(InsnCursor& insn, unsigned operation)
{
	constexpr auto size = dart::CallingConventions::kShadowSpaceBytes;
	if constexpr (size == 0)
		return true;
	if (!insn.Is(operation, 2) || !isRegisterOperand(insn.Op(0), X86_REG_RSP))
		return false;
	if (!isImmediateOperand(insn.Op(1), size))
		return false;
	insn.Next();
	return true;
}

struct RegisterSaveScope {
	size_t allocation, release;
	std::vector<std::pair<size_t, Reg>> saves, restores;
};

struct TaggedPoolLoad { intptr_t offset; dart::ObjectPtr object; };
std::optional<TaggedPoolLoad> readTaggedPoolLoad(DartApp& app, const InsnCursor& insn)
{
	intptr_t offset;
	if (!insn.RegOp(X86_INS_MOV) || insn.Op(1).size != dart::kWordSize ||
		insn.Current()->detail->x86.addr_size != dart::kWordSize || !poolOffset(app, insn.Op(1), offset))
		return std::nullopt;
	const auto& pool = app.GetObjectPool();
	const auto index = PoolIndexFromOffset(offset);
	if (pool.TypeAt(index) != dart::ObjectPool::EntryType::kTaggedObject) return std::nullopt;
	return TaggedPoolLoad{offset, pool.ObjectAt(index)};
}

struct CodePoolCallTarget { DartFnBase* function; uint64_t address; };
std::optional<CodePoolCallTarget> readCodePoolCall(DartApp& app, InsnCursor& insn);

class FunctionAnalyzer
{
public:
	FunctionAnalyzer(DartApp& app, DartFunction& function, AsmInstructions& instructions)
		: app{app}, function{function}, data{*function.GetAnalyzedData()}, instructions{instructions}, targets{instructions} {}
	void asm2il();

private:
	std::unique_ptr<ILInstr> processEnterFrameInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processLeaveFrameInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processAllocateStackInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processCheckStackOverflowInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processReturnInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processGdtCallInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processTryAllocateObject(InsnCursor& insn);
	std::unique_ptr<ILInstr> processBoxInt64Instr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processUnboxIntInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processClosureCallInstr(InsnCursor& insn);
#ifndef NO_INIT_LATE_STATIC_FIELD
	std::unique_ptr<ILInstr> processInitLateStaticFieldInstr(InsnCursor& insn);
#endif
	std::unique_ptr<ILInstr> processCallInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processLeafRuntimeCallInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processRegisterCallInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processBranchIfSmiInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processLoadFieldTableInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processLoadStore(InsnCursor& insn);
	std::unique_ptr<ILInstr> processClassIdMayBeSmiInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processTailCallInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processTypeTestInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processRegisterSaveInstr(InsnCursor& insn);
	std::optional<RegisterSaveScope> readRegisterSaveScope(size_t start);
	bool readRegisterSaveCall(InsnCursor& cursor, const RegisterSaveScope& scope);
	std::optional<ArrayOp> elementOperation(const MemoryAccess& access, const cs_insn& insn);
	std::unique_ptr<ILInstr> fieldAccess(InsnCursor& insn, const MemoryAccess& access,
		uint32_t offset, FieldAccessEvidence evidence);
	bool isObjectBase(x86_reg base) const;
	void updatePointerExclusions(const cs_insn& insn);
	std::pair<Reg, Reg> readBarrierHeaderTests(InsnCursor& insn);
	std::optional<BarrierKind> writeBarrierCallKind(const cs_x86_op& target, Reg object);
	std::unique_ptr<ILInstr> processWriteBarrierInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processBarrierStore(InsnCursor& insn);
	std::unique_ptr<ILInstr> processLoadDoubleInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processLoadValueInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processStorePoolInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processMoveRegInstr(InsnCursor& insn);
#if defined(DART_COMPRESSED_POINTERS)
	std::unique_ptr<ILInstr> processDecompressPointerInstr(InsnCursor& insn);
#endif
	std::unique_ptr<ILInstr> processLoadClassIdInstr(InsnCursor& insn);

	using Matcher = std::unique_ptr<ILInstr> (FunctionAnalyzer::*)(InsnCursor&);
	static const Matcher matcherFns[];

	void prepareInstructions();
	void emit(std::unique_ptr<ILInstr> il, size_t begin, size_t end);
	std::pair<Reg, DartClass*> objectResult(ILInstr& il);
	std::pair<Reg, DartClass*> classOnFallthrough(size_t branchIndex);
	LoadValueInstr* previousLoad(uint64_t address);
	DartFnBase* resolveCallTarget(const cs_x86_op& target);

	DartApp& app;
	DartFunction& function;
	AnalyzedFnData& data;
	AsmInstructions& instructions;
	BranchTargets targets;
	std::optional<RegisterSaveScope> registerSave;
	// Only concrete pool objects and allocation/call results justify classes.
	// Facts stop at branch targets, control transfers and register writes.
	std::array<DartClass*, Reg::kNumberOfRegisters> objects{};
	std::array<bool, Reg::kNumberOfRegisters> nonObjects{};
};

// SDK: vm/compiler/assembler/assembler_x64.cc, EnterFrame / LeaveFrame.
// Stack allocation is a separate operation, as in the ARM64 analyzer.
std::unique_ptr<ILInstr> FunctionAnalyzer::processEnterFrameInstr(InsnCursor& insn)
{
	if (!insn.Is(X86_INS_PUSH, 1) || !isRegisterOperand(insn.Op(0), X86_REG_RBP))
		return nullptr;
	insn.Next();
	if (!insn.Move(X86_REG_RBP, X86_REG_RSP))
		return nullptr;

	return std::make_unique<EnterFrameInstr>(insn.Range());
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processLeaveFrameInstr(InsnCursor& insn)
{
	if (!insn.Move(X86_REG_RSP, X86_REG_RBP))
		return nullptr;
	insn.Next();
	if (!insn.Is(X86_INS_POP, 1) || !isRegisterOperand(insn.Op(0), X86_REG_RBP))
		return nullptr;

	return std::make_unique<LeaveFrameInstr>(insn.Range());
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processAllocateStackInstr(InsnCursor& insn)
{
	if (!insn.Is(X86_INS_SUB, 2) || !isRegisterOperand(insn.Op(0), X86_REG_RSP))
		return nullptr;
	const auto& size = insn.Op(1);
	if (size.type != X86_OP_IMM)
		return nullptr;
	if (size.imm <= 0 || size.imm >= 0x100000)
		return nullptr;

	return std::make_unique<AllocateStackInstr>(insn.Range(), static_cast<uint32_t>(size.imm));
}

// SDK: vm/compiler/backend/il_x64.cc, CheckStackOverflowInstr::EmitNativeCode.
//   cmp rsp, [THR + stack_limit]; jbe slow_path
std::unique_ptr<ILInstr> FunctionAnalyzer::processCheckStackOverflowInstr(InsnCursor& insn)
{
	if (!isStackLimitCompare(*insn.Current()))
		return nullptr;
	insn.Next();
	if (!insn.Branch(X86_INS_JBE))
		return nullptr;

	return std::make_unique<CheckStackOverflowInstr>(insn.Range(), insn.Op(0).imm);
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processReturnInstr(InsnCursor& insn)
{
	if (!insn.Is(X86_INS_RET, 0) && !insn.Is(X86_INS_RET, 1))
		return nullptr;
	return std::make_unique<ReturnInstr>(insn.Range());
}

// SDK: vm/compiler/backend/flow_graph_compiler_x64.cc,
// FlowGraphCompiler::EmitDispatchTableCall; assembler_x64.cc, LoadDispatchTable.
// Checked in 2.19.6, 3.5.4, 3.10.8, 3.11.5 and sdk/main:
//   mov table, [THR + dispatch_table_array_offset()]
//   call [table + class_id * kWordSize + selector_displacement]
// The table's origin is biased: the displacement can be negative. Its IL
// offset is in entries (like ARM64), not bytes. ClassId and descriptor setup
// need not be adjacent. Require the proven table source, not just scaled memory.
std::unique_ptr<ILInstr> FunctionAnalyzer::processGdtCallInstr(InsnCursor& insn)
{
	if (!insn.LoadFrom(CSREG_DART_THR, dart::Thread::dispatch_table_array_offset()))
		return nullptr;
	const auto& destination = insn.Op(0);

	const auto table = destination.reg;
	const Reg tableReg{table};
	const Reg classIdReg{dart::DispatchTableNullErrorABI::kClassIdReg};
	if (!tableReg.IsSet() || int(tableReg) >= dart::kNumberOfCpuRegisters)
		return nullptr;
	// The table load needs a scratch register; it cannot destroy VM state
	// or the class id used by the following indexed call.
	if (isVmStateRegister(tableReg))
		return nullptr;
	if (tableReg == classIdReg)
		return nullptr;

	insn.Next();
	if (!insn.Is(X86_INS_CALL, 1))
		return nullptr;
	const auto& target = insn.Op(0);
	if (target.type != X86_OP_MEM || target.size != dart::kWordSize)
		return nullptr;
	if (target.mem.base != table || Reg{target.mem.index} != classIdReg)
		return nullptr;
	if (target.mem.segment != X86_REG_INVALID)
		return nullptr;
	if (target.mem.scale != dart::kWordSize || target.mem.disp % dart::kWordSize != 0)
		return nullptr;

	return std::make_unique<GdtCallInstr>(insn.Range(), target.mem.disp / dart::kWordSize);
}

// SDK: vm/compiler/assembler/assembler_x64.cc,
// TryAllocateObject / InitializeHeader / AddImmediate.
// Follow the allocation steps rather than comparing an entire GC tag word.
// Only the fast path is folded; the slow path and register saves remain visible.
std::unique_ptr<ILInstr> FunctionAnalyzer::processTryAllocateObject(InsnCursor& insn)
{
	// Load allocation top and bump it by the instance size.
	if (!insn.LoadFrom(CSREG_DART_THR, dart::Thread::top_offset()))
		return nullptr;
	const auto instance = insn.Op(0).reg;
	insn.Next();
	if (!insn.Is(X86_INS_ADD, 2))
		return nullptr;
	if (!isRegisterOperand(insn.Op(0), instance) || insn.Op(1).type != X86_OP_IMM)
		return nullptr;
	const auto size = insn.Op(1).imm;
	if (size <= 0 || size > INT32_MAX)
		return nullptr;
	if (size % dart::kObjectAlignment != 0)
		return nullptr;

	// Check the candidate top against end, with a forward slow-path edge.
	insn.Next();
	if (!insn.Is(X86_INS_CMP, 2) || !isRegisterOperand(insn.Op(0), instance))
		return nullptr;
	if (!isMemoryOperand(insn.Op(1), CSREG_DART_THR, dart::Thread::end_offset()))
		return nullptr;
	insn.Next();
	if (!insn.Branch(X86_INS_JAE))
		return nullptr;
	const auto failure = static_cast<uint64_t>(insn.Op(0).imm);

	// Commit top, then convert the candidate end into the tagged object start.
	insn.Next();
	if (!insn.Is(X86_INS_MOV, 2) || !isMemoryOperand(insn.Op(0), CSREG_DART_THR))
		return nullptr;
	if (insn.Op(0).mem.disp != dart::Thread::top_offset() ||
		!isRegisterOperand(insn.Op(1), instance))
		return nullptr;
	insn.Next();
	if (!insn.Immediate(X86_INS_SUB, instance, size - dart::kHeapObjectTag))
		return nullptr;

	// Initialize the header. The size tag must agree with the allocation bump.
	insn.Next();
	if (!insn.Is(X86_INS_MOV, 2) || !isMemoryOperand(insn.Op(0), instance))
		return nullptr;
	if (insn.Op(0).size != 8 || insn.Op(0).mem.disp != -dart::kHeapObjectTag)
		return nullptr;
	if (insn.Op(1).type != X86_OP_IMM)
		return nullptr;
	const auto tags = static_cast<uint64_t>(insn.Op(1).imm);
	const auto cid = (tags >> kUntaggedObjectClassIdTagPos) &
		((1u << dart::UntaggedObject::kClassIdTagSize) - 1);
	auto* cls = app.FindClass(cid);
	if (tags > UINT32_MAX || !cls)
		return nullptr;
	const auto expectedSizeTag = dart::UntaggedObject::SizeTag::SizeFits(size) ? size : 0;
	if (dart::UntaggedObject::SizeTag::decode(tags) != expectedSizeTag)
		return nullptr;
	if (failure < insn.Current()->address + insn.Current()->size || !targets.Index(failure).has_value())
		return nullptr;

	return std::make_unique<AllocateObjectInstr>(insn.Range(), Reg{instance}, *cls);
}

// SDK: vm/compiler/backend/il_x64.cc, BoxInt64Instr::EmitNativeCode;
// assembler_x64.h, SmiTag. ADD alone does not prove Smi tagging.
//   mov rax, value; add rax, rax; jno done
//   [enter frame]; call AllocateMintShared*; [leave frame]
//   mov [rax + Mint::value_offset() - kHeapObjectTag], value
// A temporary frame is present in the checked 3.5.4/3.10.8/3.11.5 sources;
// the checked 2.19.6 shared slow path does not emit that frame.
std::unique_ptr<ILInstr> FunctionAnalyzer::processBoxInt64Instr(InsnCursor& insn)
{
#if defined(DART_COMPRESSED_POINTERS)
	// Compressed Smis carry 30 value bits. LEA tags without flags; the
	// shifted source must be in [-1, 0], proven by the unsigned range test.
	if (!insn.RegOp(X86_INS_LEA) || !isRegisterOperand(insn.Op(0), X86_REG_RAX))
		return nullptr;
	const auto& address = insn.Op(1);
	if (address.type != X86_OP_MEM || insn.Current()->detail->x86.addr_size != 8)
		return nullptr;
	const auto source = address.mem.base;
	if (!Reg{source}.IsSet() || source == X86_REG_RAX || address.mem.index != source)
		return nullptr;
	if (address.mem.scale != 1 || address.mem.disp != 0 || address.mem.segment != X86_REG_INVALID)
		return nullptr;
	insn.Next();
	if (!insn.RegOp(X86_INS_MOV) || !isRegisterOperand(insn.Op(1), source))
		return nullptr;
	const auto temporary = insn.Op(0).reg;
	if (temporary == source || temporary == X86_REG_RAX)
		return nullptr;
	insn.Next();
	for (const auto& [operation, immediate] : {std::pair{X86_INS_SAR, dart::kSmiBits},
		std::pair{X86_INS_ADD, intptr_t{1}}, std::pair{X86_INS_CMP, intptr_t{2}}}) {
		if (!insn.RegOp(operation) || !insn.Immediate(operation, temporary, immediate))
			return nullptr;
		insn.Next();
	}
	if (!insn.Branch(X86_INS_JB))
		return nullptr;
#else
	if (!insn.Is(X86_INS_MOV, 2) || !isRegisterOperand(insn.Op(0), X86_REG_RAX))
		return nullptr;
	if (insn.Op(0).size != 8 || !isRegisterOfSize(insn.Op(1), 8))
		return nullptr;
	if (insn.Op(1).reg == X86_REG_RAX)
		return nullptr;
	const auto source = insn.Op(1).reg;
	insn.Next();
	if (!insn.Is(X86_INS_ADD, 2) || insn.Op(0).size != 8)
		return nullptr;
	if (!isRegisterOperand(insn.Op(0), X86_REG_RAX) || !isRegisterOperand(insn.Op(1), X86_REG_RAX))
		return nullptr;
	insn.Next();
	if (!insn.Branch(X86_INS_JNO))
		return nullptr;
#endif
	const auto join = static_cast<uint64_t>(insn.Op(0).imm);
	insn.Next();

	auto frameCursor = insn;
	const bool frame = bool(processEnterFrameInstr(frameCursor));
	if (frame) {
		insn.SetPosition(frameCursor.Position());
		insn.Next();
	}
	if (!insn.Is(X86_INS_CALL, 1))
		return nullptr;
	auto* fn = resolveCallTarget(insn.Op(0));
	if (!fn || !fn->IsStub())
		return nullptr;
	const auto kind = fn->AsStub()->kind;
	if (kind != DartStub::AllocateMintSharedWithFPURegsStub &&
		kind != DartStub::AllocateMintSharedWithoutFPURegsStub)
		return nullptr;
	insn.Next();
	if (frame) {
		if (!processLeaveFrameInstr(insn))
			return nullptr;
		insn.Next();
	}

	if (!insn.Is(X86_INS_MOV, 2) || !isMemoryOperand(insn.Op(0), X86_REG_RAX))
		return nullptr;
	if (insn.Op(0).size != 8 || insn.Op(0).mem.disp != dart::Mint::value_offset() - dart::kHeapObjectTag)
		return nullptr;
	if (!isRegisterOperand(insn.Op(1), source) || insn.Op(1).size != 8)
		return nullptr;
	if (join != insn.Current()->address + insn.Current()->size)
		return nullptr;

	return std::make_unique<BoxInt64Instr>(insn.Range(), Reg{dart::RAX}, Reg{source});
}

// SDK 3.5.4+: vm/compiler/assembler/assembler_x64.cc, LoadInt32/64FromBoxOrSmi.
// In 2.19.6 this sequence lives in il_x64.cc, UnboxInstr::EmitLoadInt32/64FromBoxOrSmi.
// The carry branch and reconstructed Mint address distinguish this from a SAR.
std::unique_ptr<UnboxIntInstr> readUnboxInt(InsnCursor& insn)
{
	Reg source;
	x86_reg destination = X86_REG_INVALID;
	if (insn.Is(X86_INS_MOV, 2)) {
		if (!isRegisterOfSize(insn.Op(0), 8) || !isRegisterOfSize(insn.Op(1), 8))
			return nullptr;
		destination = insn.Op(0).reg;
		source = Reg{insn.Op(1).reg};
		insn.Next();
	}
#if defined(DART_COMPRESSED_POINTERS)
	// Keep the full heap pointer alive while sign-extending the 32-bit Smi.
	// A same-register result is first copied to TMP by the SDK helper.
	if (!insn.RegOp(X86_INS_MOVSXD) || !isRegisterOfSize(insn.Op(1), 4))
		return nullptr;
	const Reg boxed{insn.Op(1).reg};
	if (boxed == Reg{insn.Op(0).reg} ||
		(destination != X86_REG_INVALID && boxed != Reg{destination}))
		return nullptr;
	if (!source.IsSet())
		source = boxed;
	destination = insn.Op(0).reg;
	insn.Next();
#endif
	if (!insn.RegOp(X86_INS_SAR))
		return nullptr;
	if (!isImmediateOperand(insn.Op(1), dart::kSmiTagSize))
		return nullptr;
	if (destination != X86_REG_INVALID && destination != insn.Op(0).reg)
		return nullptr;
	destination = insn.Op(0).reg;
	if (!source.IsSet())
		source = Reg{destination};
	insn.Next();
	if (!insn.Branch(X86_INS_JAE))
		return nullptr;
	const auto join = static_cast<uint64_t>(insn.Op(0).imm);
	insn.Next();
	const bool narrow = insn.Is(X86_INS_MOVSXD, 2);
	if (!narrow && !insn.Is(X86_INS_MOV, 2))
		return nullptr;
	if (!isRegisterOperand(insn.Op(0), destination) || insn.Op(0).size != 8)
		return nullptr;
	const auto& value = insn.Op(1);
	if (value.type != X86_OP_MEM || insn.Current()->detail->x86.addr_size != dart::kWordSize)
		return nullptr;
#if defined(DART_COMPRESSED_POINTERS)
	if (Reg{value.mem.base} != boxed || !isMemoryOperand(value, value.mem.base,
		dart::Mint::value_offset() - dart::kHeapObjectTag))
		return nullptr;
#else
	if (value.mem.base != destination || value.mem.index != destination)
		return nullptr;
	if (value.mem.scale != 1 || value.mem.segment != X86_REG_INVALID)
		return nullptr;
	if (value.mem.disp != dart::Mint::value_offset())
		return nullptr;
#endif
	if (join != insn.Current()->address + insn.Current()->size)
		return nullptr;

	return std::make_unique<UnboxIntInstr>(insn.Range(), Reg{destination}, source, narrow ? 32 : 64);
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processUnboxIntInstr(InsnCursor& insn)
{
	return readUnboxInt(insn);
}

// SDK: vm/compiler/backend/il_x64.cc, ClosureCallInstr::EmitNativeCode;
// vm/dart_entry.h, ArgumentsDescriptor. Reuse preceding LoadValue IL like ARM64.
std::unique_ptr<ILInstr> FunctionAnalyzer::processClosureCallInstr(InsnCursor& insn)
{
	auto* load = previousLoad(insn.Current()->address);
	if (!load || load->dstReg != Reg{dart::ARGS_DESC_REG})
		return nullptr;
	if (load->val.storage.kind != VarStorage::Pool || load->val.ValueTypeId() != dart::kArrayCid)
		return nullptr;
	if (!insn.LoadFrom(X86_REG_RAX, dart::Closure::entry_point_offset() - dart::kHeapObjectTag) ||
		!isRegisterOperand(insn.Op(0), X86_REG_RCX))
		return nullptr;
	insn.Next();
	if (!insn.Is(X86_INS_CALL, 1) || !isRegisterOperand(insn.Op(0), X86_REG_RCX))
		return nullptr;

	const auto& args = dart::Array::Handle(load->val.Get<VarArray>()->ptr);
	const auto header = (dart::ArgumentsDescriptor::first_named_entry_offset() - dart::Array::data_offset()) /
		dart::kCompressedWordSize;
	if (args.Length() <= header)
		return nullptr;
	for (intptr_t j = 0; j < header; ++j) {
		if (!dart::Object::Handle(args.At(j)).IsSmi())
			return nullptr;
	}
	dart::ArgumentsDescriptor descriptor(args);
	if (descriptor.Count() <= 0 || descriptor.Count() > INT32_MAX)
		return nullptr;
	if (descriptor.PositionalCount() < 0 || descriptor.PositionalCount() > descriptor.Count())
		return nullptr;
	if (descriptor.TypeArgsLen() < 0 || descriptor.TypeArgsLen() > INT32_MAX)
		return nullptr;
	if ((args.Length() - header - 1) % 2 != 0 ||
		descriptor.NamedCount() != (args.Length() - header - 1) / 2)
		return nullptr;

	const auto start = load->Start();
	const auto range = insn.Range();
	data.RemoveLastIL();
	return std::make_unique<ClosureCallInstr>(AddrRange(start, range.end), descriptor.Count(), descriptor.TypeArgsLen());
}

#ifndef NO_INIT_LATE_STATIC_FIELD
// SDK: vm/compiler/backend/il.cc, LoadStaticFieldInstr::EmitNativeCode;
// vm/constants_x64.h, InitStaticFieldABI. Only the initializer call is folded,
// not its preceding sentinel check or late-initialization error path.
std::unique_ptr<ILInstr> FunctionAnalyzer::processInitLateStaticFieldInstr(InsnCursor& insn)
{
	if (!insn.Branch(X86_INS_CALL))
		return nullptr;
	auto* load = previousLoad(insn.Current()->address);
	if (!load || load->dstReg != Reg{dart::InitStaticFieldABI::kFieldReg})
		return nullptr;
	if (load->val.storage.kind != VarStorage::Pool)
		return nullptr;
	auto* fn = app.GetFunction(insn.Op(0).imm);
	if (!fn || !fn->IsStub())
		return nullptr;
	const auto kind = fn->AsStub()->kind;
	if (kind != DartStub::InitLateStaticFieldStub && kind != DartStub::InitLateFinalStaticFieldStub)
		return nullptr;
	const auto index = PoolIndexFromOffset(load->val.storage.offset);
	if (app.GetObjectPool().TypeAt(index) != dart::ObjectPool::EntryType::kTaggedObject)
		return nullptr;
	const auto& object = dart::Object::Handle(app.GetObjectPool().ObjectAt(index));
	if (!object.IsField())
		return nullptr;
	const auto& field = dart::Field::Cast(object);
	auto* staticField = app.FindStaticField(field.TargetOffset());
	if (!field.is_static() || !staticField)
		return nullptr;

	const auto start = load->Start();
	const auto range = insn.Range();
	data.RemoveLastIL();
	return std::make_unique<InitLateStaticFieldInstr>(AddrRange(start, range.end),
		VarStorage{Reg{dart::InitStaticFieldABI::kResultReg}}, *staticField);
}
#endif

// Direct AOT calls and immediate pool entrypoints. Code objects are not raw
// entrypoints; Assembler::CallCodeThroughPool remains a separate, unhandled case.
DartFnBase* FunctionAnalyzer::resolveCallTarget(const cs_x86_op& target)
{
	// Thread caches these VM stub entrypoints in every supported SDK. Resolve
	// only an exact stub already registered in the loaded snapshot image.
	if (target.size == dart::kWordSize && isMemoryOperand(target, CSREG_DART_THR)) {
		const auto offset = target.mem.disp;
		for (const auto& [fpu, kind] : {std::pair{false, DartStub::StackOverflowSharedWithoutFPURegsVMStub},
			std::pair{true, DartStub::StackOverflowSharedWithFPURegsVMStub}}) {
			if (offset != dart::Thread::stack_overflow_shared_stub_entry_point_offset(fpu))
				continue;
			const auto& code = fpu ? dart::StubCode::StackOverflowSharedWithFPURegs()
				: dart::StubCode::StackOverflowSharedWithoutFPURegs();
			auto* targetStub = app.FindFunctionExact(code.EntryPoint() - app.base());
			if (targetStub && targetStub->IsStub() && targetStub->AsStub()->kind == kind)
				return targetStub;
		}
	}

	if (target.type == X86_OP_IMM)
		return app.GetFunction(target.imm);
	intptr_t offset;
	if (!poolOffset(app, target, offset))
		return nullptr;
	const auto& pool = app.GetObjectPool();
	const auto index = PoolIndexFromOffset(offset);
	if (pool.TypeAt(index) != dart::ObjectPool::EntryType::kImmediate)
		return nullptr;
	return app.GetFunction(pool.RawValueAt(index) - app.base());
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processCallInstr(InsnCursor& insn)
{
	if (!insn.Is(X86_INS_CALL, 1))
		return nullptr;
	const auto& target = insn.Op(0);
	if (target.type == X86_OP_IMM)
		return std::make_unique<CallInstr>(insn.Range(), app.GetFunction(target.imm), target.imm);
	if (auto* fn = resolveCallTarget(target))
		return std::make_unique<CallInstr>(insn.Range(), fn, fn->Address());
	if (isMemoryOperand(target, CSREG_DART_THR) && GetThreadLeafFunction(target.mem.disp))
		return std::make_unique<CallLeafRuntimeInstr>(insn.Range(), target.mem.disp);
	return nullptr;
}

// SDK: assembler_x64.cc, LeafRuntimeScope::Call / CallCFunction. The known
// Thread entry and matching VMTag bracket prove this native leaf invocation.
// Surrounding frames, alignment and register saves remain separate operations.
std::unique_ptr<ILInstr> FunctionAnalyzer::processLeafRuntimeCallInstr(InsnCursor& insn)
{
	// LeafRuntimeCallInstr can load the entry through a Thread temporary,
	// then save FP and EnterCFrame before the same VMTag-bracketed call used
	// by LeafRuntimeScope. Follow only these transfers, never skip a body.
	auto thread = CSREG_DART_THR;
	if (insn.Move(X86_REG_RAX, CSREG_DART_THR)) {
		thread = X86_REG_RAX;
		insn.Next();
	}
	if (!insn.Load(thread))
		return nullptr;
	const auto entry = insn.Op(1).mem.disp;
	if (!GetThreadLeafFunction(entry))
		return nullptr;
	const auto target = insn.Op(0).reg;
	if (isVmStateRegister(Reg{target}))
		return nullptr;
	insn.Next();
	if (target != X86_REG_RAX) {
		if (!insn.Move(X86_REG_RAX, target))
			return nullptr;
		insn.Next();
	}
	bool nativeFrame = false;
	if (insn.Is(X86_INS_MOV, 2) && isRegisterOperand(insn.Op(1), X86_REG_RBP)) {
		const auto saved = Reg{dart::CallingConventions::kSecondNonArgumentRegister};
		if (!isRegisterOfSize(insn.Op(0), 8) || Reg{insn.Op(0).reg} != saved)
			return nullptr;
		insn.Next();
		if (!processEnterFrameInstr(insn))
			return nullptr;
		insn.Next();
		// EnterCFrame(0): all supported x64 target ABIs align to 16 bytes.
		if (!insn.Immediate(X86_INS_AND, X86_REG_RSP, -16))
			return nullptr;
		insn.Next();
		nativeFrame = true;
	}
	if (!insn.Is(X86_INS_MOV, 2))
		return nullptr;
	const auto tag = dart::Thread::vm_tag_offset();
	if (!isMemoryOperand(insn.Op(0), CSREG_DART_THR, tag) || insn.Op(0).size != 8)
		return nullptr;
	if (!isRegisterOperand(insn.Op(1), X86_REG_RAX))
		return nullptr;
	insn.Next();
	if (!consumeNativeShadowSpace(insn, X86_INS_SUB))
		return nullptr;
	if (!insn.Is(X86_INS_CALL, 1) || !isRegisterOperand(insn.Op(0), X86_REG_RAX))
		return nullptr;
	insn.Next();
	if (insn.Is(X86_INS_ADD, 2)) {
		if (!consumeNativeShadowSpace(insn, X86_INS_ADD))
			return nullptr;
	}
	if (!insn.Is(X86_INS_MOV, 2))
		return nullptr;
	if (!isMemoryOperand(insn.Op(0), CSREG_DART_THR, tag) || insn.Op(0).size != 8)
		return nullptr;
	if (!isImmediateOperand(insn.Op(1), dart::VMTag::kDartTagId))
		return nullptr;
	if (nativeFrame) {
		insn.Next();
		if (!processLeaveFrameInstr(insn))
			return nullptr;
	}
	return std::make_unique<CallLeafRuntimeInstr>(insn.Range(), entry);
}

// SDK: vm/compiler/backend/flow_graph_compiler_x64.cc, EmitInstanceCallAOT;
// assembler_x64.cc, LeafRuntimeScope::Call / Assembler::CallCFunction.
// VMTag-bracketed leaf calls have their own matcher above. Here only adjacent,
// complete
// entry-load/call sequences are resolved, never arbitrary register calls.
std::unique_ptr<ILInstr> FunctionAnalyzer::processRegisterCallInstr(InsnCursor& insn)
{
	auto code = insn;
	if (auto target = readCodePoolCall(app, code)) {
		insn.SetPosition(code.Position());
		return std::make_unique<CallInstr>(insn.Range(), target->function, target->address);
	}
	if (!insn.RegOp(X86_INS_MOV))
		return nullptr;
	const auto entry = insn.Op(0).reg;
	const auto source = insn.Op(1);
	insn.Next();
	bool callData = false;
	if (entry == X86_REG_RCX && insn.Is(X86_INS_MOV, 2)) {
		if (isRegisterOperand(insn.Op(0), X86_REG_RBX) && isMemoryOperand(insn.Op(1), CSREG_DART_PP)) {
			callData = true;
			insn.Next();
		}
	}
	if (!insn.Is(X86_INS_CALL, 1) || !isRegisterOperand(insn.Op(0), entry))
		return nullptr;
	if (source.type == X86_OP_MEM) {
		if (auto* fn = resolveCallTarget(source))
			return std::make_unique<CallInstr>(insn.Range(), fn, fn->Address());
	}
	if (callData || !isMemoryOperand(source, CSREG_DART_THR))
		return nullptr;
	if (GetThreadLeafFunction(source.mem.disp))
		return std::make_unique<CallLeafRuntimeInstr>(insn.Range(), source.mem.disp);
	return nullptr;
}

// SDK: vm/compiler/assembler/assembler_x64.h, BranchIfSmi.
// Other TEST masks do not establish a Smi check.
std::unique_ptr<ILInstr> FunctionAnalyzer::processBranchIfSmiInstr(InsnCursor& insn)
{
	if (!insn.Is(X86_INS_TEST, 2) || insn.Op(0).type != X86_OP_REG)
		return nullptr;
	if (!isImmediateOperand(insn.Op(1), dart::kSmiTagMask))
		return nullptr;
	const Reg value{insn.Op(0).reg};
	insn.Next();
	if (!insn.Branch(X86_INS_JE))
		return nullptr;
	return std::make_unique<BranchIfSmiInstr>(insn.Range(), value, insn.Op(0).imm);
}

// SDK: vm/compiler/backend/il.cc, LoadStaticFieldInstr::EmitNativeCode;
// il_x64.cc, StoreStaticFieldInstr::EmitNativeCode. The field table holds
// native words even on compressed-pointer targets; it has no heap-object tag.
std::unique_ptr<ILInstr> FunctionAnalyzer::processLoadFieldTableInstr(InsnCursor& insn)
{
	if (!insn.LoadFrom(CSREG_DART_THR, AOT_Thread_field_table_values_offset))
		return nullptr;
	const auto table = insn.Op(0).reg;
	insn.Next();
	if (!insn.Is(X86_INS_MOV, 2))
		return nullptr;
	const auto access = getMemoryAccess(*insn.Current());
	if (!access || access->value.size != 8)
		return nullptr;
	if (!isMemoryOperand(access->memory, table))
		return nullptr;
	const auto offset = access->memory.mem.disp;
	if (offset < 0 || offset % dart::kWordSize != 0)
		return nullptr;
	const Reg value{access->value.reg};
	if (access->isLoad)
		return std::make_unique<LoadStaticFieldInstr>(insn.Range(), value, offset);
	return std::make_unique<StoreStaticFieldInstr>(insn.Range(), value, offset);
}

// SDK StoreBarrier / ArrayStoreBarrier share these header tests. Read the low
// byte, shift the same 32-bit register, apply Thread's barrier mask, then test
// the value header. The intrinsic register-shuffle path is deliberately separate.
std::pair<Reg, Reg> FunctionAnalyzer::readBarrierHeaderTests(InsnCursor& insn)
{
	static_assert(dart::kWriteBarrierValueReg == dart::RAX);
	if (!insn.Is(X86_INS_MOV, 2) || !isLowByteRegister(insn.Op(0)))
		return {};
	if (insn.Current()->detail->x86.addr_size != dart::kWordSize)
		return {};
	const Reg scratch{insn.Op(0).reg};
	const auto& header = insn.Op(1);
	if (header.type != X86_OP_MEM || header.size != 1)
		return {};
	if (!isMemoryOperand(header, header.mem.base, -dart::kHeapObjectTag))
		return {};
	const Reg object{header.mem.base};
	if (!object.IsSet() || int(object) >= dart::kNumberOfCpuRegisters)
		return {};
	if ((dart::kDartAvailableCpuRegs & (1 << int(object))) == 0)
		return {};
	if (object == Reg{dart::kWriteBarrierValueReg} || object == scratch || isVmStateRegister(scratch))
		return {};
	if (scratch == Reg{dart::kWriteBarrierValueReg})
		return {};
	insn.Next();
	if (!insn.RegOp(X86_INS_SHR, 4))
		return {};
	if (Reg{insn.Op(0).reg} != scratch || !isImmediateOperand(insn.Op(1), dart::UntaggedObject::kBarrierOverlapShift))
		return {};
	insn.Next();
	if (!insn.RegOp(X86_INS_AND, 4))
		return {};
	if (Reg{insn.Op(0).reg} != scratch || insn.Op(1).size != 4)
		return {};
	if (!isMemoryOperand(insn.Op(1), CSREG_DART_THR, dart::Thread::write_barrier_mask_offset()))
		return {};
	insn.Next();
	if (!insn.Is(X86_INS_TEST, 2) || !isLowByteRegister(insn.Op(1)))
		return {};
	if (Reg{insn.Op(1).reg} != scratch || insn.Op(0).size != 1)
		return {};
	if (!isMemoryOperand(insn.Op(0), X86_REG_RAX, -dart::kHeapObjectTag))
		return {};
	return {object, scratch};
}

// Direct wrapper calls must identify the *object register's* entry, not merely
// any address within WriteBarrierWrappers. Use immutable VM code metadata;
// GetFunction can split that aggregate stub while resolving interior entries.
std::optional<BarrierKind> FunctionAnalyzer::writeBarrierCallKind(const cs_x86_op& target, Reg object)
{
	const auto reg = static_cast<dart::Register>(int(object));
	if (target.type == X86_OP_MEM && target.size == dart::kWordSize) {
		if (isMemoryOperand(target, CSREG_DART_THR, dart::Thread::write_barrier_wrappers_thread_offset(reg)))
			return BarrierKind::Object;
		if (object == Reg{dart::kWriteBarrierObjectReg} &&
			isMemoryOperand(target, CSREG_DART_THR, dart::Thread::array_write_barrier_entry_point_offset()))
			return BarrierKind::Array;
	}
	if (target.type != X86_OP_IMM)
		return std::nullopt;
	auto* store = dart::IsolateGroup::Current()->object_store();
	const auto& wrappers = dart::Code::Handle(store->write_barrier_wrappers_stub());
	const auto wrapper = wrappers.EntryPoint() - app.base() + dart::Thread::WriteBarrierWrappersOffsetForRegister(reg);
	if (target.imm == wrapper)
		return BarrierKind::Object;
	const auto& array = dart::Code::Handle(store->array_write_barrier_stub());
	if (object == Reg{dart::kWriteBarrierObjectReg} && target.imm == array.EntryPoint() - app.base())
		return BarrierKind::Array;
	return std::nullopt;
}

// SDK StoreBarrier: optional BranchIfSmi and header-mask branch converge
// immediately after the exact barrier call. No control-flow interior is hidden.
std::unique_ptr<ILInstr> FunctionAnalyzer::processWriteBarrierInstr(InsnCursor& insn)
{
	auto smiCursor = insn;
	auto smi = processBranchIfSmiInstr(smiCursor);
	if (smi) {
		if (static_cast<BranchIfSmiInstr*>(smi.get())->objReg != Reg{dart::kWriteBarrierValueReg})
			return nullptr;
		insn.SetPosition(smiCursor.Position());
		insn.Next();
	}
	const auto [object, scratch] = readBarrierHeaderTests(insn);
	if (!object.IsSet())
		return nullptr;
	insn.Next();
	if (!insn.Branch(X86_INS_JE))
		return nullptr;
	const auto join = static_cast<uint64_t>(insn.Op(0).imm);
	insn.Next();
	if (!insn.Is(X86_INS_CALL, 1))
		return nullptr;
	const auto kind = writeBarrierCallKind(insn.Op(0), object);
	if (!kind || join != insn.Current()->address + insn.Current()->size)
		return nullptr;
	if (*kind == BarrierKind::Array && scratch == Reg{dart::kWriteBarrierSlotReg})
		return nullptr; // Array barrier must preserve the proven slot address.
	if (!targets.Index(join).has_value())
		return nullptr;
	if (smi && static_cast<BranchIfSmiInstr*>(smi.get())->branchAddr != join)
		return nullptr;
	return std::make_unique<WriteBarrierInstr>(insn.Range(), object, Reg{dart::kWriteBarrierValueReg}, *kind == BarrierKind::Array);
}

// Both stores use the same complete StoreBarrier proof. An Array store first
// proves its slot with LEA; an ordinary store retains a generic field offset.
// Neither displacement alone nor the barrier's name establishes an element.
std::unique_ptr<ILInstr> FunctionAnalyzer::processBarrierStore(InsnCursor& insn)
{
	const bool array = insn.Is(X86_INS_LEA, 2);
	cs_x86_op address{};
	if (array) {
		if (!insn.RegOp(X86_INS_LEA) || insn.Current()->detail->x86.addr_size != dart::kWordSize ||
			Reg{insn.Op(0).reg} != Reg{dart::kWriteBarrierSlotReg}) return nullptr;
		address = insn.Op(1);
		if (address.type != X86_OP_MEM || address.mem.segment != X86_REG_INVALID ||
			Reg{address.mem.base} != Reg{dart::kWriteBarrierObjectReg}) return nullptr;
		insn.Next();
	}
	if (!insn.IsAvailable()) return nullptr;
	const auto access = getMemoryAccess(*insn.Current());
	if (!access || access->isLoad || access->value.type != X86_OP_REG ||
		access->memory.size != dart::kCompressedWordSize) return nullptr;
	const auto base = array ? address.mem.base : access->memory.mem.base;
	const auto offset = access->memory.mem.disp + dart::kHeapObjectTag;
	ArrayOp operation{access->memory.size, false, ArrayOp::List};
	std::optional<VarStorage> index;
	if (array) {
		if (Reg{access->memory.mem.base} != Reg{dart::kWriteBarrierSlotReg} ||
			!isMemoryOperand(access->memory, access->memory.mem.base, 0) || !app.FindClass(dart::kArrayCid))
			return nullptr;
		address.size = access->memory.size; // LEA itself is always native-width.
		index = getElementIndex(address, dart::Array::data_offset(), operation);
		if (!index) return nullptr;
	} else if (!isMemoryOperand(access->memory, base) || offset < dart::kWordSize ||
		offset > UINT32_MAX || offset % dart::kCompressedWordSize) return nullptr;
	insn.Next();
	auto barrierIL = processWriteBarrierInstr(insn);
	if (!barrierIL) return nullptr;
	const auto& barrier = static_cast<const WriteBarrierInstr&>(*barrierIL);
	if (barrier.isArray != array || barrier.objReg != Reg{base} || barrier.valReg != Reg{access->value.reg})
		return nullptr;
	if (array)
		return std::make_unique<StoreArrayElementInstr>(insn.Range(), barrier.valReg, barrier.objReg, *index, operation);
	return std::make_unique<StoreFieldInstr>(insn.Range(), barrier.valReg, barrier.objReg, offset,
		FieldAccessEvidence::WriteBarrier);
}

// SDK LoadIndexed/StoreIndexed: decode the layout and index once for both
// directions. Known layouts retain their type; shape-only evidence stays inferred.
std::optional<ArrayOp> FunctionAnalyzer::elementOperation(const MemoryAccess& access, const cs_insn& insn)
{
	const auto id = insn.id;
	const auto& memory = access.memory;
	const auto payload = memory.mem.disp + dart::kHeapObjectTag;
	auto* cls = objects[Reg{memory.mem.base}];
	const int cid = cls ? cls->Id() : dart::kIllegalCid;
	if (cid == dart::kArrayCid || cid == dart::kImmutableArrayCid) {
		if (id != X86_INS_MOV || memory.size != dart::kCompressedWordSize)
			return std::nullopt;
		return ArrayOp{memory.size, access.isLoad, ArrayOp::List};
	}
	// StoreIndexed/LoadIndexed use scalar FP moves for internal float arrays.
	// The receiver layout, not a payload-looking displacement, proves this;
	// external data, views and SIMD layouts need different address contracts.
	if (cid == dart::kTypedDataFloat32ArrayCid || cid == dart::kTypedDataFloat64ArrayCid) {
		const auto size = cid == dart::kTypedDataFloat32ArrayCid ? 4 : 8;
		if (id != (size == 4 ? X86_INS_MOVSS : X86_INS_MOVSD) || memory.size != size ||
			access.value.type != X86_OP_REG || !Reg{access.value.reg}.IsDecimal())
			return std::nullopt;
		return ArrayOp{memory.size, access.isLoad, ArrayOp::TypedUnknown};
	}
	if (cls && access.isLoad) {
		if (auto typed = getTypedIntegerLoad(cid)) {
			if (isTypedIntegerLoad(insn, *typed))
				return typed;
			return std::nullopt;
		}
	}
	// Without a proven layout, only register-indexed payloads have enough
	// evidence. Constant offsets remain fields rather than invented elements.
	const Reg index{memory.mem.index};
	if (!isObjectBase(memory.mem.base) || !index.IsSet() || isVmStateRegister(index) ||
		int(index) >= dart::kNumberOfCpuRegisters)
		return std::nullopt;
	const bool string = payload == dart::OneByteString::data_offset() &&
		id == X86_INS_MOVZX && (memory.size == 1 || memory.size == 2);
	if (!string && payload != dart::Array::data_offset() && payload != dart::UntaggedTypedData::payload_offset())
		return std::nullopt;
	if (cls) {
		if (cid == dart::kOneByteStringCid || cid == dart::kTwoByteStringCid) {
			if (!string || memory.size != (cid == dart::kOneByteStringCid ? 1 : 2))
				return std::nullopt;
		}
		else if (string || !dart::IsTypedDataClassId(cid))
			return std::nullopt;
		else {
			const auto typed = getTypedIntegerLoad(cid);
			if (!typed || typed->size != memory.size)
				return std::nullopt;
		}
	}
	ArrayOp operation{memory.size, access.isLoad, ArrayOp::TypedUnknown};
	operation.inferred = true;
	switch (id) {
	case X86_INS_MOVSX: case X86_INS_MOVSXD:
		if (!access.isLoad || access.value.size != 8) return std::nullopt;
		operation.arrType = ArrayOp::TypedSigned;
		break;
	case X86_INS_MOVZX:
		if (!access.isLoad || access.value.size < 4) return std::nullopt;
		operation.arrType = ArrayOp::TypedUnsigned;
		break;
	case X86_INS_MOV:
		if (memory.size == dart::kCompressedWordSize) operation.arrType = ArrayOp::Unknown;
		break;
	case X86_INS_MOVSS: case X86_INS_MOVSD:
		break;
	default: return std::nullopt;
	}
	return operation;
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processLoadStore(InsnCursor& insn)
{
	const auto access = getMemoryAccess(*insn.Current());
	if (!access || access->memory.mem.segment != X86_REG_INVALID)
		return nullptr;
	const auto& memory = access->memory;
	const Reg base{memory.mem.base}, value{access->value.type == X86_OP_REG ? access->value.reg : X86_REG_INVALID};
	if (!base.IsSet())
		return nullptr;
	auto* cls = objects[base];
	if (auto operation = elementOperation(*access, *insn.Current())) {
		const auto payload = operation->arrType == ArrayOp::List ? dart::Array::data_offset() :
			!operation->inferred ? dart::UntaggedTypedData::payload_offset() : memory.mem.disp + dart::kHeapObjectTag;
		if (auto index = getElementIndex(memory, payload, *operation)) {
			if (access->isLoad)
				return std::make_unique<LoadArrayElementInstr>(insn.Range(), value, base, *index, *operation);
			if (access->value.type == X86_OP_IMM)
				return std::make_unique<StoreArrayElementInstr>(insn.Range(), access->value.imm, base, *index, *operation);
			return std::make_unique<StoreArrayElementInstr>(insn.Range(), value, base, *index, *operation);
		}
	}
	if (!isMemoryOperand(memory, memory.mem.base) ||
		(memory.size != 8 && memory.size != dart::kCompressedWordSize))
		return nullptr;
	const auto offset = memory.mem.disp + dart::kHeapObjectTag;
	if (offset < dart::kWordSize || offset > UINT32_MAX)
		return nullptr;
	if (cls && offset < cls->Size() && cls->FindField(offset))
		return fieldAccess(insn, *access, offset, FieldAccessEvidence::ReceiverLayout);
	// ARM64's fixed-offset fallback: a slot, not a declaration. A known
	// layout may veto it; native values and VM state cannot be receivers.
	if (insn.Current()->id != X86_INS_MOV && insn.Current()->id != X86_INS_MOVSD)
		return nullptr;
	if (!isObjectBase(memory.mem.base) || offset % dart::kCompressedWordSize)
		return nullptr;
	if (cls) {
		// Native VM classes may have a negative next-field sentinel (_Map,
		// _Set). Only their fixed instance extent is a valid fallback bound;
		// variable-size/unknown extents still cannot justify a field access.
		const auto size = cls->Size() >= 0 ? cls->Size() :
			dart::Class::Handle(cls->Ptr()).host_instance_size();
		if (size <= 0 || offset >= size || cls->Id() == dart::kSmiCid) return nullptr;
	}
	return fieldAccess(insn, *access, offset, FieldAccessEvidence::TaggedAddress);
}

std::unique_ptr<ILInstr> FunctionAnalyzer::fieldAccess(InsnCursor& insn, const MemoryAccess& access,
	uint32_t offset, FieldAccessEvidence evidence)
{
	const Reg base{access.memory.mem.base};
	if (access.isLoad) {
		auto load = std::make_unique<LoadFieldInstr>(insn.Range(), Reg{access.value.reg}, base, offset, evidence);
		load->accessSize = access.memory.size;
		return load;
	}
	std::unique_ptr<StoreFieldInstr> store;
	if (access.value.type == X86_OP_IMM)
		store = std::make_unique<StoreFieldInstr>(insn.Range(), access.value.imm, base, offset, evidence);
	else
		store = std::make_unique<StoreFieldInstr>(insn.Range(), Reg{access.value.reg}, base, offset, evidence);
	store->accessSize = access.memory.size;
	return store;
}

bool FunctionAnalyzer::isObjectBase(x86_reg base) const
{
	const Reg reg{base};
	if (!reg.IsSet() || int(reg) >= dart::kNumberOfCpuRegisters)
		return false;
	if (isVmStateRegister(reg) || nonObjects[reg])
		return false;
	return (dart::kDartAvailableCpuRegs & (1 << int(reg))) != 0;
}



// SDK: vm/compiler/backend/il_x64.cc, UnboxedConstantInstr::EmitNativeCode.
// MOVSS/MOVSD proves the scalar width. XORPS/XORPD alone also occurs in vector
// code and does not establish a Dart double constant.
std::unique_ptr<ILInstr> FunctionAnalyzer::processLoadDoubleInstr(InsnCursor& insn)
{
	const bool single = insn.Is(X86_INS_MOVSS, 2);
	if (!single && !insn.Is(X86_INS_MOVSD, 2))
		return nullptr;
	if (insn.Op(0).type != X86_OP_REG || !Reg{insn.Op(0).reg}.IsDecimal())
		return nullptr;
	intptr_t offset;
	if (!poolOffset(app, insn.Op(1), offset))
		return nullptr;
	const auto index = PoolIndexFromOffset(offset);
	if (app.GetObjectPool().TypeAt(index) != dart::ObjectPool::EntryType::kImmediate)
		return nullptr;
	const auto bits = app.GetObjectPool().RawValueAt(index);
	double value;
	if (single) {
		float scalar;
		std::memcpy(&scalar, &bits, sizeof(scalar));
		value = scalar;
	} else {
		static_assert(sizeof(bits) == sizeof(value));
		std::memcpy(&value, &bits, sizeof(value));
	}
	return std::make_unique<LoadValueInstr>(insn.Range(), Reg{insn.Op(0).reg},
		VarItem{VarStorage::NewPool(offset), new VarDouble(value, VarValue::NativeDouble)});
}

// SDK: vm/compiler/assembler/assembler_x64.cc, LoadObject / LoadWordFromPoolIndex;
// vm/thread.h, cached null/bool objects. Immediate integers remain distinct from
// tagged pool objects. Register moves are handled separately, as in ARM64.
std::unique_ptr<ILInstr> FunctionAnalyzer::processLoadValueInstr(InsnCursor& insn)
{
	if (auto value = integerConstant(*insn.Current()))
		return std::make_unique<LoadValueInstr>(insn.Range(), Reg{insn.Op(0).reg},
			VarItem{VarStorage::Immediate, new VarInteger(*value, VarValue::NativeInt)});
	if (!insn.Is(X86_INS_MOV, 2) && !insn.Is(X86_INS_MOVABS, 2))
		return nullptr;
	const auto& destination = insn.Op(0);
	if (!isRegisterOfSize(destination, dart::kWordSize))
		return nullptr;
	const Reg dst{destination.reg};
	if (!dst.IsSet())
		return nullptr;
	const auto& source = insn.Op(1);
	if (auto value = threadConstant(source))
		return std::make_unique<LoadValueInstr>(insn.Range(), dst,
			VarItem{VarStorage::NewThread(source.mem.disp), value.release()});
	intptr_t offset;
	if (!poolOffset(app, source, offset) || source.size != dart::kWordSize)
		return nullptr;
	const auto type = app.GetObjectPool().TypeAt(PoolIndexFromOffset(offset));
	if (type != dart::ObjectPool::EntryType::kTaggedObject && type != dart::ObjectPool::EntryType::kImmediate)
		return nullptr;
	return std::make_unique<LoadValueInstr>(insn.Range(), dst,
		VarItem{VarStorage::NewPool(offset), getPoolObject(app, offset, dst)});
}

#if defined(DART_COMPRESSED_POINTERS)
// Assembler::LoadCompressed restores the heap base after a zero-extending load.
bool isDecompression(const cs_insn& insn)
{
	const auto& x = insn.detail->x86;
	return insn.id == X86_INS_ADD && x.op_count == 2 && x.addr_size == dart::kWordSize &&
		isRegisterOfSize(x.operands[0], dart::kWordSize) && x.operands[1].size == dart::kWordSize &&
		isMemoryOperand(x.operands[1], CSREG_DART_THR, AOT_Thread_heap_base_offset);
}
#endif

// StoreWordToPoolIndex uses the same tagged PP displacement convention as its
// load counterpart. Keep a distinct IL kind; this is not a LoadValue object.
std::unique_ptr<ILInstr> FunctionAnalyzer::processStorePoolInstr(InsnCursor& insn)
{
	if (!insn.Is(X86_INS_MOV, 2) || insn.Current()->detail->x86.addr_size != dart::kWordSize)
		return nullptr;
	if (!isRegisterOfSize(insn.Op(1), dart::kWordSize) || insn.Op(0).size != dart::kWordSize)
		return nullptr;
	intptr_t offset;
	if (!poolOffset(app, insn.Op(0), offset))
		return nullptr;
	return std::make_unique<StoreObjectPoolInstr>(insn.Range(), Reg{insn.Op(1).reg}, offset);
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processMoveRegInstr(InsnCursor& insn)
{
	if (!insn.Is(X86_INS_MOV, 2) && !insn.Is(X86_INS_MOVABS, 2))
		return nullptr;
	if (!isRegisterOfSize(insn.Op(0), dart::kWordSize) || insn.Op(1).type != X86_OP_REG)
		return nullptr;
	const Reg destination{insn.Op(0).reg};
	const Reg source{insn.Op(1).reg};
	if (!destination.IsSet() || !source.IsSet())
		return nullptr;
	return std::make_unique<MoveRegInstr>(insn.Range(), destination, source);
}

#if defined(DART_COMPRESSED_POINTERS)
std::unique_ptr<ILInstr> FunctionAnalyzer::processDecompressPointerInstr(InsnCursor& insn)
{
	if (!insn.IsAvailable() || !isDecompression(*insn.Current()))
		return nullptr;
	return std::make_unique<DecompressPointerInstr>(insn.Range(), VarStorage{Reg{insn.Op(0).reg}});
}
#endif

// SDK: vm/compiler/assembler/assembler_x64.cc, LoadClassId.
//   mov result32, [object - kHeapObjectTag]
//   shr result32, ClassIdTagPos
// The complete tags-load/shift pair proves the operation. MayBeSmi variants
// remain separate patterns; an isolated header load is not classified.
std::unique_ptr<ILInstr> FunctionAnalyzer::processLoadClassIdInstr(InsnCursor& insn)
{
	if (!insn.RegOp(X86_INS_MOV, 4))
		return nullptr;
	const auto destination = insn.Op(0).reg;
	const auto& tags = insn.Op(1);
	if (tags.type != X86_OP_MEM || !Reg{tags.mem.base}.IsSet())
		return nullptr;
	if (!isMemoryOperand(tags, tags.mem.base, -dart::kHeapObjectTag))
		return nullptr;
	const Reg object{tags.mem.base};
	insn.Next();
	if (!insn.Immediate(X86_INS_SHR, destination, kUntaggedObjectClassIdTagPos))
		return nullptr;

	return std::make_unique<LoadClassIdInstr>(insn.Range(), object, Reg{destination});
}

void FunctionAnalyzer::prepareInstructions()
{
	for (size_t i = 0; i < instructions.Count(); ++i) {
		const auto* insn = instructions.Ptr(i);
		const auto& x = insn->detail->x86;
		for (unsigned j = 0; j < x.op_count; ++j) {
			intptr_t offset;
			if (poolOffset(app, x.operands[j], offset)) {
				auto& text = data.asmTexts.AtAddr(insn->address);
				text.dataType = AsmText::PoolOffset;
				text.poolOffset = offset;
			}
		}
	}
}

LoadValueInstr* FunctionAnalyzer::previousLoad(uint64_t address)
{
	if (targets.contains(address) || data.il_insns.empty())
		return nullptr;
	auto* previous = data.LastIL();
	if (previous->End() != address || previous->Kind() != ILInstr::LoadValue)
		return nullptr;
	return static_cast<LoadValueInstr*>(previous);
}

std::pair<Reg, DartClass*> FunctionAnalyzer::objectResult(ILInstr& il)
{
	if (il.Kind() == ILInstr::MoveReg) {
		const auto& move = static_cast<const MoveRegInstr&>(il);
		return {move.dstReg, objects[move.srcReg]};
	}
	if (il.Kind() == ILInstr::LoadValue) {
		const auto& load = static_cast<const LoadValueInstr&>(il);
		if (load.val.storage.kind == VarStorage::Immediate)
			return {load.dstReg, nullptr}; // Native bits do not establish a heap class.
		auto cid = load.val.Value()->RawTypeId();
		if (load.val.storage.kind == VarStorage::Pool) {
			const auto index = PoolIndexFromOffset(load.val.storage.offset);
			const auto& pool = app.GetObjectPool();
			cid = dart::kIllegalCid;
			if (pool.TypeAt(index) == dart::ObjectPool::EntryType::kTaggedObject) {
				const auto& object = dart::Object::Handle(pool.ObjectAt(index));
				if (!object.IsSmi())
					cid = object.GetClassId();
			}
		}
		return {load.dstReg, cid > 0 ? app.FindClass(cid) : nullptr};
	}
	if (il.Kind() == ILInstr::AllocateObject) {
		const auto& allocation = static_cast<const AllocateObjectInstr&>(il);
		return {allocation.dstReg, &allocation.dartCls};
	}
	if (il.Kind() == ILInstr::Call) {
		auto* fn = static_cast<CallInstr&>(il).GetFunction();
		if (fn && fn->ReturnType() != dart::kIllegalCid)
			return {Reg{dart::CallingConventions::kReturnReg}, app.FindClass(fn->ReturnType())};
		// SDK: stub_code_compiler_x64.cc, GenerateAllocateArrayStub. Both its
		// fast and runtime slow paths return a tagged Array in this ABI register.
		if (fn && fn->IsStub()) {
			if (fn->AsStub()->kind == DartStub::AllocateArrayStub)
				return {Reg{dart::AllocateArrayABI::kResultReg}, app.FindClass(dart::kArrayCid)};
			// GenerateAllocateTypedDataArrayStub returns the tagged internal
			// array on both allocation paths, in AllocateTypedDataArrayABI.
			switch (fn->AsStub()->kind) {
			case DartStub::AllocateFloat32ArrayStub: case DartStub::AllocateFloat32ArrayVMStub:
				return {Reg{dart::AllocateTypedDataArrayABI::kResultReg}, app.FindClass(dart::kTypedDataFloat32ArrayCid)};
			case DartStub::AllocateFloat64ArrayStub: case DartStub::AllocateFloat64ArrayVMStub:
				return {Reg{dart::AllocateTypedDataArrayABI::kResultReg}, app.FindClass(dart::kTypedDataFloat64ArrayCid)};
			default: break;
			}
		}
	}
	return {};
}

// SDK: assembler_x64.cc, CompareClassId / LoadClassId. Reuse LoadClassId IL
// rather than rematching the tags encoding. In the adjacent sequence
//   cid = LoadClassId(object); cmp cid, expected; jne other
// only the fallthrough proves equality. Keep CMP/JNE as assembly, and discard
// this fact at every later control transfer or alternative entry as usual.
std::pair<Reg, DartClass*> FunctionAnalyzer::classOnFallthrough(size_t branchIndex)
{
	if (branchIndex == 0 || data.il_insns.size() < 2)
		return {};
	const auto* branch = instructions.Ptr(branchIndex);
	if (branch->id != X86_INS_JNE || branch->detail->x86.op_count != 1)
		return {};
	if (targets.contains(branch->address))
		return {};
	const auto& target = branch->detail->x86.operands[0];
	if (target.type != X86_OP_IMM)
		return {};
	if (target.imm <= branch->address + branch->size || !targets.Index(target.imm).has_value())
		return {}; // Includes a jump to the fallthrough, which proves nothing.
	const auto* compare = instructions.Ptr(branchIndex - 1);
	if (compare->id != X86_INS_CMP || compare->detail->x86.op_count != 2)
		return {};
	if (targets.contains(compare->address))
		return {}; // An alternative edge may bypass the class-id load.
	const auto* previous = data.il_insns[data.il_insns.size() - 2].get();
	if (previous->Kind() != ILInstr::LoadClassId || previous->End() != compare->address)
		return {};
	const auto* load = static_cast<const LoadClassIdInstr*>(previous);
	if (load->objReg == load->cidReg || isVmStateRegister(load->objReg))
		return {}; // Loading the id must not have destroyed the object pointer.
	const auto& left = compare->detail->x86.operands[0];
	if (!isRegisterOfSize(left, 4) && !isRegisterOfSize(left, 8))
		return {};
	if (Reg{left.reg} != load->cidReg)
		return {};
	const auto& right = compare->detail->x86.operands[1];
	if (right.type != X86_OP_IMM || right.imm <= 0)
		return {};
	return {load->objReg, app.FindClass(right.imm)};
}

// Only negative local facts: an observed integer/untagged address must not be
// reinterpreted as a heap object by the generic fallback. Unknown is not false.
// This is deliberately not a type/alias engine; joins and transfers forget it.
void FunctionAnalyzer::updatePointerExclusions(const cs_insn& insn)
{
	const auto& x = insn.detail->x86;
	Reg result;
	bool excluded = false;
	if (x.op_count == 2 && x.operands[0].type == X86_OP_REG) {
		const auto& dst = x.operands[0];
		const auto& src = x.operands[1];
		if (dst.access & CS_AC_WRITE)
			result = Reg{dst.reg};
		if (isMoveInstruction(insn.id)) {
			if (dst.size == 4 && dart::kCompressedWordSize == 8)
				excluded = true;
			if (src.type == X86_OP_REG) {
				const Reg source{src.reg};
				excluded = (dst.size == 4 && dart::kCompressedWordSize == 8) ||
					(source.IsSet() && (nonObjects[source] || isVmStateRegister(source)));
			}
			if (src.type == X86_OP_IMM)
				excluded = true; // Includes odd native constants; object constants use PP/THR.
		}
		if ((insn.id == X86_INS_XOR || insn.id == X86_INS_SUB) && dst.size >= 4)
			excluded = src.type == X86_OP_REG && src.reg == dst.reg;
		if (insn.id == X86_INS_LEA || insn.id == X86_INS_MOVSX || insn.id == X86_INS_MOVSXD || insn.id == X86_INS_MOVZX)
			excluded = true;
		if (insn.id == X86_INS_SHR || insn.id == X86_INS_SAR || insn.id == X86_INS_SHL || insn.id == X86_INS_SAL)
			excluded = true;
	}
	if (isControlTransfer(insn) || isTrap(insn)) {
		nonObjects.fill(false);
		objects.fill(nullptr);
	}
	visitWrittenRegisters(insn, [&](Reg reg) {
		nonObjects[reg] = false;
		objects[reg] = nullptr;
	});
	if (result.IsSet())
		nonObjects[result] = excluded;
}

void FunctionAnalyzer::emit(std::unique_ptr<ILInstr> il, size_t begin, size_t end)
{
#ifdef HAS_INIT_ASYNC
	if (il->Kind() == ILInstr::Call) {
		auto* load = previousLoad(instructions.Ptr(begin)->address);
		auto* call = static_cast<CallInstr*>(il.get());
		if (auto async = processInitAsyncInstr(app, call->GetFunction(), load, il->Range())) {
			data.returnType = async->ReturnType();
			data.RemoveLastIL();
			il = std::move(async);
		}
	}
#endif
	// Commit metadata only after a complete match. Nested/failed matchers must
	// not leave frame state or object facts behind.
	switch (il->Kind()) {
	case ILInstr::EnterFrame:
		data.useFramePointer = true;
		break;
	case ILInstr::AllocateStack:
		data.stackSize = static_cast<AllocateStackInstr*>(il.get())->AllocSize();
		break;
	case ILInstr::CheckStackOverflow:
		data.firstCheckStackOverflowAddr = il->Start();
		break;
	case ILInstr::Return:
		data.last_ret = instructions.Ptr(begin);
		break;
	default:
		break;
	}
	auto result = objectResult(*il);
	if (il->Kind() == ILInstr::Unknown && end == begin + 1)
		result = classOnFallthrough(begin);
	for (size_t i = begin; i < end; ++i)
		updatePointerExclusions(*instructions.Ptr(i));
	const auto [resultReg, resultClass] = result;
	if (resultReg.IsSet())
		objects[resultReg] = resultClass;
	data.AddIL(std::move(il));
}

// Compound recognizers share the transactional instruction cursor.
// SDK authority: assembler_x64.cc LoadTaggedClassIdMayBeSmi,
// CallCodeThroughPool; flow_graph_compiler_x64.cc EmitJumpToStub and
// GenerateInstantiatedTypeNoArgumentsTest. No app-specific instruction bytes.

namespace {
bool isSmiTagRegister(const cs_x86_op& operand)
{
	if (isRegisterOfSize(operand, 1))
		return isLowByteRegister(operand); // TEST AH,1 does not test RAX's tag.
	return isRegisterOfSize(operand, 4) || isRegisterOfSize(operand, dart::kWordSize);
}

std::unique_ptr<LoadValueInstr> readSmiCid(InsnCursor& insn, int64_t cid = dart::kSmiCid << dart::kSmiTagSize)
{
	if (!insn.Is(X86_INS_MOV, 2) && !insn.Is(X86_INS_MOVABS, 2))
		return nullptr;
	// movq(positive uint32) is deliberately encoded as MOV r32, imm32 by
	// the SDK; x64 zero-extension produces the full CID value.
	if (!isRegisterOfSize(insn.Op(0), 4) && !isRegisterOfSize(insn.Op(0), dart::kWordSize))
		return nullptr;
	if (!isImmediateOperand(insn.Op(1), cid))
		return nullptr;
	return std::make_unique<LoadValueInstr>(insn.Range(), Reg{insn.Op(0).reg},
		VarItem{VarStorage::Immediate, new VarInteger(cid, VarValue::NativeInt)});
}
} // namespace

// SDK LoadClassIdMayBeSmi / LoadTaggedClassIdMayBeSmi share the same
// diamond. Only the optional ADD and Smi constant differ. Validate that
// representation once, retaining the existing distinct IL outputs.
std::unique_ptr<ILInstr> FunctionAnalyzer::processClassIdMayBeSmiInstr(InsnCursor& insn)
{
	if (!insn.Is(X86_INS_TEST, 2) || !isSmiTagRegister(insn.Op(0)) ||
		!isImmediateOperand(insn.Op(1), dart::kSmiTagMask))
		return nullptr;
	const Reg object{insn.Op(0).reg};
	if (!object.IsSet() || isVmStateRegister(object))
		return nullptr;
	const auto start = insn.Current()->address;
	insn.Next();
	const bool inPlace = insn.Is(X86_INS_JE, 1);
	std::unique_ptr<LoadValueInstr> smi;
	if (!inPlace) {
		smi = readSmiCid(insn, dart::kSmiCid);
		if (!smi) smi = readSmiCid(insn);
		if (!smi || smi->dstReg == object || isVmStateRegister(smi->dstReg))
			return nullptr;
		insn.Next();
	}
	if (!insn.Branch(X86_INS_JE))
		return nullptr;
	const uint64_t target = insn.Op(0).imm;
	const auto branchAddress = insn.Current()->address;
	const auto branchEnd = branchAddress + insn.Current()->size;
	insn.Next();
	if (!insn.IsAvailable() || insn.Current()->detail->x86.addr_size != dart::kWordSize)
		return nullptr;
	auto loaded = processLoadClassIdInstr(insn);
	if (!loaded) return nullptr;
	auto cid = std::unique_ptr<LoadClassIdInstr>(static_cast<LoadClassIdInstr*>(loaded.release()));
	const auto result = inPlace ? object : smi->dstReg;
	if (cid->objReg != object || cid->cidReg != result)
		return nullptr;
	const auto loadEnd = insn.Position();
	insn.Next();
	const bool tagged = insn.Is(X86_INS_ADD, 2) &&
		isRegisterOfSize(insn.Op(0), dart::kCompressedWordSize) &&
		Reg{insn.Op(0).reg} == result && isRegisterOperand(insn.Op(1), insn.Op(0).reg);
	if (!tagged) insn.SetPosition(loadEnd);
	const auto expected = dart::kSmiCid << (tagged ? dart::kSmiTagSize : 0);
	if (inPlace) {
		insn.Next();
		if (!insn.Branch(X86_INS_JMP))
			return nullptr;
		const uint64_t join = insn.Op(0).imm;
		const auto jumpAddress = insn.Current()->address;
		insn.Next();
		if (!insn.AcceptLocalTarget(target, branchAddress) || !insn.IsAvailable() || insn.Current()->address != target)
			return nullptr;
		smi = readSmiCid(insn, expected);
		if (!smi || smi->dstReg != object || join != insn.Range().end)
			return nullptr;
		if (!insn.AcceptLocalTarget(join, jumpAddress)) return nullptr;
	} else {
		if (smi->val.Get<VarInteger>()->val != expected || target != insn.Range().end ||
			!insn.AcceptLocalTarget(target, branchAddress))
			return nullptr;
	}
	if (!tagged)
		return std::make_unique<LoadClassIdInstr>(insn.Range(), object, result, true);
	auto branch = std::make_unique<BranchIfSmiInstr>(AddrRange(start, branchEnd), object, target);
	return std::make_unique<LoadTaggedClassIdMayBeSmiInstr>(insn.Range(),
		std::move(smi), std::move(branch), std::move(cid));
}


// A tagged Code pool entry proves the entrypoint's owner; an arbitrary
// object's member at the same offset does not. Shared by call and save scopes.
std::optional<CodePoolCallTarget> readCodePoolCall(DartApp& app, InsnCursor& insn)
{
	const auto load = readTaggedPoolLoad(app, insn);
	if (!load) return std::nullopt;
	const auto codeReg = insn.Op(0).reg;
	const auto& object = dart::Object::Handle(load->object);
	if (!object.IsCode())
		return std::nullopt;
	insn.Next();
	if (!insn.Is(X86_INS_CALL, 1))
		return std::nullopt;
	if (insn.Current()->detail->x86.addr_size != dart::kWordSize)
		return std::nullopt;
	if (!isMemoryOperand(insn.Op(0), codeReg) || insn.Op(0).size != dart::kWordSize)
		return std::nullopt;
	const auto& code = dart::Code::Cast(object);
	for (const auto& [kind, address] : {
		std::pair{dart::CodeEntryKind::kNormal, code.EntryPoint()},
		std::pair{dart::CodeEntryKind::kUnchecked, code.UncheckedEntryPoint()},
		std::pair{dart::CodeEntryKind::kMonomorphic, code.MonomorphicEntryPoint()},
		std::pair{dart::CodeEntryKind::kMonomorphicUnchecked, code.MonomorphicUncheckedEntryPoint()}}) {
		if (insn.Op(0).mem.disp == dart::Code::entry_point_offset(kind) - dart::kHeapObjectTag)
			return CodePoolCallTarget{app.GetFunction(code.EntryPoint() - app.base()), address - app.base()};
	}
	return std::nullopt;
}


// Only known external entries prove an inter-function jump. An unknown branch
// or a local block is retained as assembly, including loops and dispatch edges.
std::unique_ptr<ILInstr> FunctionAnalyzer::processTailCallInstr(InsnCursor& insn)
{
	if (!insn.Branch(X86_INS_JMP))
		return nullptr;
	const uint64_t address = insn.Op(0).imm;
	if (address >= instructions.FirstPtr()->address &&
		address < instructions.LastPtr()->address + instructions.LastPtr()->size)
		return nullptr;
	auto* target = app.FindFunctionExact(address);
	if (!target)
		return nullptr;
	return std::make_unique<CallInstr>(insn.Range(), target, address);
}

// GenerateTTSCall emits an exact Type object and subtype-cache pool load,
// followed by the Type's own cached stub entry. Caller-side numeric/range
// fast paths remain separate IL; they need not be swallowed to name the cast.
std::unique_ptr<ILInstr> FunctionAnalyzer::processTypeTestInstr(InsnCursor& insn)
{
	const auto typeLoad = readTaggedPoolLoad(app, insn);
	if (!typeLoad || Reg{insn.Op(0).reg} != Reg{dart::TypeTestABI::kDstTypeReg}) return nullptr;
	const auto& object = dart::Object::Handle(typeLoad->object);
	if (!object.IsType())
		return nullptr;
	const auto& type = dart::Type::Cast(object);
	if (!type.IsInstantiated())
		return nullptr; // Type parameters require the instantiation path instead.
	insn.Next();
	const auto cacheLoad = readTaggedPoolLoad(app, insn);
	if (!cacheLoad || Reg{insn.Op(0).reg} != Reg{dart::TypeTestABI::kSubtypeTestCacheReg}) return nullptr;
	const auto& cache = dart::Object::Handle(cacheLoad->object);
	if (!cache.IsNull() && !cache.IsSubtypeTestCache())
		return nullptr;
	insn.Next();
	if (!insn.Is(X86_INS_CALL, 1))
		return nullptr;
	const auto& call = insn.Op(0);
	if (call.type == X86_OP_IMM) {
		if (call.imm + app.base() != type.type_test_stub_entry_point())
			return nullptr;
	} else {
		const auto entry = dart::AbstractType::type_test_stub_entry_point_offset() - dart::kHeapObjectTag;
		if (call.type != X86_OP_MEM || Reg{call.mem.base} != Reg{dart::TypeTestABI::kDstTypeReg})
			return nullptr;
		if (!isMemoryOperand(call, call.mem.base, entry))
			return nullptr;
		if (call.size != dart::kWordSize || insn.Current()->detail->x86.addr_size != dart::kWordSize)
			return nullptr;
	}
	std::unique_ptr<VarValue> value{getPoolObject(app, typeLoad->offset, Reg{dart::TypeTestABI::kDstTypeReg})};
	return std::make_unique<TestTypeInstr>(insn.Range(), Reg{dart::TypeTestABI::kInstanceReg}, value->ToString());
}

namespace {

bool readFpuStackMove(InsnCursor& cursor, Reg reg, intptr_t offset, bool store)
{
	if (!cursor.Is(X86_INS_MOVUPS, 2))
		return false;
	if (cursor.Current()->detail->x86.addr_size != dart::kWordSize)
		return false;
	const auto& memory = cursor.Op(store ? 0 : 1);
	const auto& value = cursor.Op(store ? 1 : 0);
	if (!isMemoryOperand(memory, X86_REG_RSP, offset) || memory.size != 16)
		return false;
	return isRegisterOfSize(value, 16) && Reg{value.reg} == reg;
}

// The scope's single register list is also the restore contract. FPU
// stores ascend by register/slot; CPU PUSHes descend by register.
bool readRegisterList(InsnCursor& cursor, intptr_t area, RegisterSaveScope& scope)
{
	for (intptr_t offset = 0; offset < area; offset += 16) {
		if (!cursor.Is(X86_INS_MOVUPS, 2) || cursor.Op(1).type != X86_OP_REG)
			return false;
		const Reg reg{cursor.Op(1).reg};
		if (!reg.IsDecimal() || (!scope.saves.empty() && reg <= scope.saves.back().second))
			return false;
		if (!readFpuStackMove(cursor, reg, offset, true))
			return false;
		scope.saves.emplace_back(cursor.Position(), reg);
		cursor.Next();
	}
	while (cursor.Is(X86_INS_PUSH, 1) && isRegisterOfSize(cursor.Op(0), dart::kWordSize)) {
		const Reg reg{cursor.Op(0).reg};
		if (!reg.IsSet() || isVmStateRegister(reg))
			return false;
		if (!scope.saves.empty() && !scope.saves.back().second.IsDecimal() && reg >= scope.saves.back().second)
			return false;
		scope.saves.emplace_back(cursor.Position(), reg);
		cursor.Next();
	}
	return !scope.saves.empty();
}

// DoubleToIntegerSlowPath moves an unboxed argument if needed, then the
// tagged recognized-kind enum into its ABI register before the stub invocation.
// These are bounded argument preparations, not arbitrary skipped instructions.
bool readDoubleToIntegerArguments(InsnCursor& cursor)
{
	if (cursor.Is(X86_INS_MOVAPS, 2)) {
		if (!isRegisterOfSize(cursor.Op(0), 16) || !isRegisterOfSize(cursor.Op(1), 16))
			return false;
		const auto input = Reg::XMM0 + int(dart::DoubleToIntegerStubABI::kInputReg);
		if (int(Reg{cursor.Op(0).reg}) != input)
			return false;
		cursor.Next();
	}
	if (!cursor.Is(X86_INS_MOV, 2) || !isSmiTagRegister(cursor.Op(0)) || cursor.Op(0).size == 1)
		return false;
	if (Reg{cursor.Op(0).reg} != Reg{dart::DoubleToIntegerStubABI::kRecognizedKindReg})
		return false;
	for (auto kind : {dart::MethodRecognizer::kDoubleToInteger,
		dart::MethodRecognizer::kDoubleFloorToInt, dart::MethodRecognizer::kDoubleCeilToInt}) {
		if (isImmediateOperand(cursor.Op(1), int64_t(kind) << dart::kSmiTagSize)) {
			cursor.Next();
			return true;
		}
	}
	return false;
}

// ThrowErrorSlowPathCode saves live registers for lazy deopt / exceptions,
// even though these zero-argument runtimes never return. A restore is not
// required here. Prove the runtime entry, argc, trampoline and trailing trap;
// argument pushes to other runtimes remain unclassified.
bool readThrowingRuntimeCall(InsnCursor& cursor)
{
	if (!cursor.RegOp(X86_INS_MOV) || !isRegisterOperand(cursor.Op(0), X86_REG_RBX)) return false;
	const auto& entry = cursor.Op(1);
	if (!isMemoryOperand(entry, CSREG_DART_THR) || entry.size != dart::kWordSize ||
		cursor.Current()->detail->x86.addr_size != dart::kWordSize) return false;
	if (entry.mem.disp != dart::Thread::ArgumentErrorUnboxedInt64_entry_point_offset() &&
		entry.mem.disp != dart::Thread::IntegerDivisionByZeroException_entry_point_offset()) return false;
	cursor.Next();
	if (!cursor.IsAvailable() || integerConstant(*cursor.Current()) != 0 ||
		Reg{cursor.Op(0).reg} != Reg{dart::R10}) return false;
	cursor.Next();
	if (!cursor.Is(X86_INS_CALL, 1) || cursor.Op(0).size != dart::kWordSize ||
		cursor.Current()->detail->x86.addr_size != dart::kWordSize ||
		!isMemoryOperand(cursor.Op(0), CSREG_DART_THR, dart::Thread::call_to_runtime_entry_point_offset()))
		return false;
	cursor.Next();
	return cursor.Is(X86_INS_INT3, 0);
}

DartFnBase* readSavedStubCall(DartApp& app, InsnCursor& cursor)
{
	if (!cursor.Is(X86_INS_CALL, 1)) {
		auto target = readCodePoolCall(app, cursor);
		return target ? target->function : nullptr;
	}
	const auto& target = cursor.Op(0);
	if (target.type == X86_OP_IMM)
		return app.FindFunctionExact(target.imm);
	return nullptr;
}

} // namespace

bool FunctionAnalyzer::readRegisterSaveCall(InsnCursor& cursor, const RegisterSaveScope& scope)
{
	const auto start = cursor.Position();
	const bool doubleArguments = readDoubleToIntegerArguments(cursor);
	if (!doubleArguments)
		cursor.SetPosition(start);
	auto leaf = cursor;
	if (!doubleArguments && processLeafRuntimeCallInstr(leaf)) {
		cursor.SetPosition(leaf.Position());
	} else if (cursor.Is(X86_INS_CALL, 1) && isMemoryOperand(cursor.Op(0), CSREG_DART_THR)) {
		if (doubleArguments || !GetThreadLeafFunction(cursor.Op(0).mem.disp))
			return false;
		if (cursor.Current()->detail->x86.addr_size != dart::kWordSize || cursor.Op(0).size != dart::kWordSize)
			return false;
	} else {
		auto* function = readSavedStubCall(app, cursor);
		if (!function || !function->IsStub())
			return false;
		if (doubleArguments && function->AsStub()->kind != DartStub::DoubleToIntegerVMStub)
			return false;
	}
	cursor.Next();
	if (!cursor.Is(X86_INS_MOV, 2) || !isRegisterOfSize(cursor.Op(0), dart::kWordSize))
		return true;
	const Reg result{cursor.Op(0).reg};
	if (!isRegisterOperand(cursor.Op(1), X86_REG_RAX) || isVmStateRegister(result))
		return false;
	if (std::any_of(scope.saves.begin(), scope.saves.end(), [&](const auto& saved) { return saved.second == result; }))
		return false;
	cursor.Next();
	return true;
}

namespace {
bool readSavedRegisters(InsnCursor& cursor, RegisterSaveScope& scope)
{
	// CPU restores reverse the pushes; FPU restores preserve slot order.
	for (auto it = scope.saves.rbegin(); it != scope.saves.rend(); ++it) {
		const auto reg = it->second;
		if (reg.IsDecimal()) continue;
		if (!cursor.Is(X86_INS_POP, 1) || !isRegisterOfSize(cursor.Op(0), dart::kWordSize) || Reg{cursor.Op(0).reg} != reg)
			return false;
		scope.restores.emplace_back(cursor.Position(), reg);
		cursor.Next();
	}
	intptr_t offset = 0;
	for (const auto& [position, reg] : scope.saves) {
		if (!reg.IsDecimal()) break;
		if (!readFpuStackMove(cursor, reg, offset, false)) return false;
		scope.restores.emplace_back(cursor.Position(), reg);
		offset += 16;
		cursor.Next();
	}
	return true;
}

} // namespace

// SDK SaveLiveRegisters / allocation slow paths: verify every slot against
// its restore, the intervening call and the exact stack area release.
std::optional<RegisterSaveScope> FunctionAnalyzer::readRegisterSaveScope(size_t start)
{
	InsnCursor cursor{instructions, targets, start};
	intptr_t area = 0;
	if (cursor.Is(X86_INS_SUB, 2)) {
		if (!isRegisterOperand(cursor.Op(0), X86_REG_RSP) || cursor.Op(1).type != X86_OP_IMM)
			return std::nullopt;
		area = cursor.Op(1).imm;
		if (area <= 0 || area > 16 * 16 || area % 16)
			return std::nullopt;
		cursor.Next();
	} else if (!cursor.Is(X86_INS_PUSH, 1)) {
		return std::nullopt;
	}
	RegisterSaveScope scope{start, 0, {}, {}};
	if (!readRegisterList(cursor, area, scope))
		return std::nullopt;
	auto terminal = cursor;
	if (readThrowingRuntimeCall(terminal)) {
		scope.release = terminal.Position();
		return scope;
	}
	if (!readRegisterSaveCall(cursor, scope) || !readSavedRegisters(cursor, scope))
		return std::nullopt;
	if (!area) {
		scope.release = cursor.Position() - 1;
		return scope;
	}
	if (!cursor.Is(X86_INS_ADD, 2) || !isRegisterOperand(cursor.Op(0), X86_REG_RSP))
		return std::nullopt;
	if (!isImmediateOperand(cursor.Op(1), area))
		return std::nullopt;
	scope.release = cursor.Position();
	return scope;
}

// A complete scope is decoded once at its first instruction, then reused
// while the forward analyzer visits each save/restore. Failed lists cannot
// restart at a suffix. This replaces repeated bounded backward rescans.
std::unique_ptr<ILInstr> FunctionAnalyzer::processRegisterSaveInstr(InsnCursor& insn)
{
	const auto position = insn.Position();
	if (!registerSave || position > registerSave->release) {
		if (!insn.Is(X86_INS_SUB, 2) && !insn.Is(X86_INS_PUSH, 1))
			return nullptr;
		if (position && (instructions.Ptr(position - 1)->id == X86_INS_PUSH ||
			instructions.Ptr(position - 1)->id == X86_INS_MOVUPS))
			return nullptr;
		registerSave = readRegisterSaveScope(position);
	}
	if (!registerSave)
		return nullptr;
	const auto& scope = *registerSave;
	const auto at = position == scope.allocation ? scope.saves.front().first : position;
	for (const auto& [saved, reg] : scope.saves) {
		if (saved != at) continue;
		insn.SetPosition(saved);
		return std::make_unique<SaveRegisterInstr>(insn.Range(), reg);
	}
	for (const auto& [restored, reg] : scope.restores) {
		if (restored != position) continue;
		if (restored == scope.restores.back().first) insn.SetPosition(scope.release);
		return std::make_unique<RestoreRegisterInstr>(insn.Range(), reg);
	}
	return nullptr;
}

// Entry-prologue recovery, deliberately not whole-function type inference.
// SDK authority: frontend/prologue_builder.cc, BuildParameterHandling,
// BuildClosureContextHandling and BuildTypeArgumentsHandling; backend/il_x64.cc
// LoadIndexed/LoadFpRelativeSlot; backend/dart_calling_conventions.cc.
namespace {

class X64ParameterRecovery {
public:
	X64ParameterRecovery(DartApp& app, DartFunction& function, AnalyzedFnData& data,
		AsmInstructions& instructions, const BranchTargets& targets)
		: app(app), function(function), data(data), instructions(instructions), targets(targets) {}
	void Recover();

private:
	enum Kind { Unknown, ZeroIndex, NullValue, Descriptor, Count, OptionalCount, DescriptorSize, TypeArgsLength, DescriptorName, Position, CountMinusPosition, CompressedContext,
		NamedValue, UnboxedNamedValue, IncomingValue, ParameterValue, StackValue, ClosureValue, ContextValue, TypeArgsValue };
	struct Source {
		Kind kind{Unknown};
		int value{0};
		bool operator==(const Source&) const = default;
	};
	using Registers = std::array<Source, Reg::kNumberOfRegisters>;
	struct DefaultConstant { std::unique_ptr<VarValue> value; size_t origin{0}; };
	using DefaultValues = std::array<DefaultConstant, Reg::kNumberOfRegisters>;
	using Locals = std::unordered_map<int64_t, Source>;
	struct LocalScope {
		Locals& state;
		Locals saved;
		explicit LocalScope(Locals& state) : state(state), saved(state) {}
		~LocalScope() { state = std::move(saved); }
	};
	struct NamedResult {
		Registers registers{};
		FnParamInfo parameter;
		size_t join{0};
		bool isNamed{true};
		int optional{-1};
		std::vector<Reg> locations;
	};
	void signature();
	Source source(const cs_x86_op& operand, const Registers& registers, bool incoming = false);
	void transfer(const cs_insn& insn, Registers& registers, bool commit = false);
	void invalidate(const cs_insn& insn, Registers& registers, bool commit);
	void writtenRegister(Reg reg, Registers& registers, bool commit);
	void recordLocation(Source source, Reg reg, int64_t spill = 0);
	std::unique_ptr<VarValue> constant(const cs_x86_op& operand, bool unboxedDouble = false);
	std::optional<std::string> comparedName(const cs_insn& insn, const Registers& registers);
	struct DefaultPath {
		size_t start;
		Registers registers;
		std::string name;
		int optional;
		DefaultValues defaults{};
	};
	std::vector<NamedResult> parameterDefaults(size_t index, const Registers& registers);
	std::vector<NamedResult> defaultResults(std::vector<DefaultPath>& missing, const Registers& supplied, size_t join);
	std::optional<NamedResult> unusedNamed(size_t index, size_t join, const Registers& registers);
	bool unboxParameter(size_t& index, size_t end, Registers& registers,
		std::vector<std::pair<size_t, size_t>>& edges);
	bool traceDefault(size_t index, DefaultPath& path);
	std::optional<NamedResult> typeArguments(size_t index, const Registers& registers);
	int publish(FnParamInfo&& parameter, bool isNamed, int optional);
	void seedIncoming(Registers& registers);
	Source stackSource(int64_t offset, int countBias = -1, int namedEntry = -1);
	void finishIncoming(Registers& registers);
	void bindIncoming(Registers& registers);
	void descriptorTypeArguments(size_t begin);
	void combine(size_t begin, size_t end);
	bool parameterMove(const cs_insn& insn, const Registers& registers);
	bool parameterInstruction(const cs_insn& insn, const Registers& registers) const;

	DartApp& app;
	DartFunction& function;
	AnalyzedFnData& data;
	AsmInstructions& instructions;
	const BranchTargets& targets;
	int64_t frameSize{0};
	int observedStackTop{0};
	bool suspendState{false};
	bool hasDeclaration{false};
	Locals locals;
	// Candidate entry locations are not declaration ordinals. The same Source
	// values follow copies/spills until the first entry boundary; only observed
	// bindings are published, then rebound to explicitly partial parameters.
	struct Binding {
		FnParamInfo info;
		bool observed{false};
		int parameter{-1};
		int countBias{-1};
		int64_t indexedOffset{0};
		int namedEntry{-1};
	};
	std::vector<Binding> bindings;
	Reg receiver;
	int receiverParameter{-1};
	bool observingIncoming{false};
	std::vector<std::pair<int64_t, int64_t>> overwrittenIncoming;
};

void X64ParameterRecovery::seedIncoming(Registers& registers)
{
#if __has_include("vm/compiler/backend/dart_calling_conventions.h")
	// SDK Function::MaxNumberOfParametersInRegisters excludes closures,
	// dispatch helpers and generic functions. Admit ordinary Dart functions
	// only. Do not substitute native Win64/SysV registers.
	const auto& vmFunction = dart::Function::Handle(function.Ptr());
	bool registerConvention = vmFunction.IsRegularFunction() ||
		vmFunction.kind() == dart::UntaggedFunction::kConstructor ||
		function.Kind() == DartFunction::GETTER || function.Kind() == DartFunction::SETTER;
	const auto signature = vmFunction.signature();
	if (signature.IsHeapObject()) {
		if (!dart::FunctionType::Handle(signature).IsNull() && vmFunction.IsGeneric())
			registerConvention = false;
	}
	if (registerConvention) {
		if (!function.IsStatic())
			receiver = Reg{dart::DartCallingConvention::kCpuRegistersForArgs[0]};
		auto addRegister = [&](Reg reg) {
			FnParamInfo info;
			info.paramReg = reg;
			info.name = std::string("arg_") + reg.Name();
			registers[reg] = {IncomingValue, static_cast<int>(bindings.size())};
			bindings.push_back({std::move(info)});
		};
		for (auto reg : dart::DartCallingConvention::kCpuRegistersForArgs)
			addRegister(Reg{reg});
		for (auto reg : dart::DartCallingConvention::kFpuRegistersForArgs)
			addRegister(Reg{static_cast<Reg::Value>(int(Reg::XMM0) + int(reg))});
	}
#endif
}

void X64ParameterRecovery::signature()
{
	if (function.Ptr() == dart::Function::null())
		return;
	const auto& vmFunction = dart::Function::Handle(function.Ptr());
	const auto& sig = dart::FunctionType::Handle(vmFunction.signature());
	const bool accessor = function.Kind() == DartFunction::GETTER || function.Kind() == DartFunction::SETTER;
	if (sig.IsNull() && !accessor) {
		// NumImplicitParameters proves the receiver declaration even when no
		// entry copy survives. It does not prove a complete regular signature.
		if (vmFunction.IsRegularFunction() && !function.IsStatic() && !function.IsClosure()) {
			FnParamInfo parameter{"this"};
			parameter.type = function.Class().DeclarationType();
			receiverParameter = data.params.NumParam();
			data.params.addFixedParam(std::move(parameter));
			data.params.isPartial = true;
		}
		return;
	}
	// Dart accessors have a language-defined arity even when their signature
	// was stripped. This proves the declaration count, not erased names/types
	// or the representation/location of an optimized-away setter value.
	const auto count = sig.IsNull() ? vmFunction.NumImplicitParameters() +
		(function.Kind() == DartFunction::SETTER) : vmFunction.NumParameters();
	if (count < 0 || count > UINT8_MAX)
		return;
	hasDeclaration = true;
	data.params.numFixedParam = sig.IsNull() ? count : vmFunction.num_fixed_parameters();
	data.params.isNamedParam = !sig.IsNull() && vmFunction.HasOptionalNamedParameters();
	for (intptr_t i = 0; i < count; ++i) {
		FnParamInfo parameter;
		if (i < function.NumParam()) {
			const auto& declaration = function.Params()[i];
			parameter.name = declaration.name;
			if (declaration.type && declaration.type->IsType())
				parameter.type = declaration.type->AsType();
		}
		if (!function.IsStatic() && !function.IsClosure() && i == 0) {
			parameter.name = "this";
			parameter.type = function.Class().DeclarationType();
		}
		data.params.add(std::move(parameter));
	}
}

X64ParameterRecovery::Source X64ParameterRecovery::source(
	const cs_x86_op& operand, const Registers& registers, bool incoming)
{
	if (operand.type == X86_OP_REG) {
		const Reg reg{operand.reg};
		return reg.IsSet() ? registers[reg] : Source{};
	}
	if (operand.type != X86_OP_MEM || operand.mem.segment != X86_REG_INVALID)
		return {};
	const auto& address = operand.mem;
	const Reg base{address.base};
	if (!base.IsSet())
		return {};
	if ((function.IsClosure() || (function.IsAsync() && suspendState)) &&
		address.index == X86_REG_INVALID &&
		address.disp == AOT_Closure_context_offset - dart::kHeapObjectTag) {
		const auto owner = registers[base];
		const auto closureSlot = std::max(observedStackTop, data.asmTexts.MaxParamStackOffset());
		const bool incomingClosure = owner.kind == ParameterValue && owner.value >= 0 &&
			owner.value < data.params.NumParam() && closureSlot >= 2 * dart::kWordSize &&
			data.params[owner.value].paramOffset == closureSlot;
		const bool observedClosure = owner.kind == IncomingValue && bindings[owner.value].countBias < 0 &&
			bindings[owner.value].namedEntry < 0 && closureSlot >= 2 * dart::kWordSize &&
			bindings[owner.value].info.paramOffset == closureSlot;
		if (owner.kind == ClosureValue || observedClosure || (owner.kind == StackValue &&
			owner.value == closureSlot) || incomingClosure)
			return {ContextValue};
	}
	if (base == Reg{Reg::RBP} && address.index == X86_REG_INVALID && address.disp < 0) {
		const auto it = locals.find(address.disp);
		return it == locals.end() ? Source{} : it->second;
	}
	if (base == Reg{dart::THR} && isMemoryOperand(operand, CSREG_DART_THR, dart::Thread::object_null_offset()))
		return {NullValue};
	const Reg index{address.index};
	const bool zeroIndex = index.IsSet() && registers[index].kind == ZeroIndex &&
		address.scale == dart::kWordSize / 2;
	if (base == Reg{Reg::RBP} && (address.index == X86_REG_INVALID || zeroIndex) &&
		address.disp >= 2 * dart::kWordSize && address.disp <= INT32_MAX &&
		address.disp % dart::kWordSize == 0) {
		for (const auto& [start, end] : overwrittenIncoming)
			if (address.disp < end && start < address.disp + dart::kWordSize)
				return {};
		if (observingIncoming && address.index == X86_REG_INVALID)
			return stackSource(address.disp);
		for (int i = 0; i < data.params.NumParam(); ++i)
			if (data.params[i].paramOffset == address.disp)
				return {ParameterValue, i};
		return {StackValue, static_cast<int>(address.disp)};
	}
	if (registers[base].kind == Descriptor) {
		if (address.index == X86_REG_INVALID &&
			address.disp == AOT_ArgumentsDescriptor_count_offset - dart::kHeapObjectTag)
			return {Count};
		if (address.index == X86_REG_INVALID &&
			address.disp == AOT_ArgumentsDescriptor_size_offset - dart::kHeapObjectTag)
			return {DescriptorSize};
		if (address.index == X86_REG_INVALID &&
			address.disp == AOT_ArgumentsDescriptor_type_args_len_offset - dart::kHeapObjectTag)
			return {TypeArgsLength};
		const auto entry = address.disp - (AOT_ArgumentsDescriptor_first_named_entry_offset - dart::kHeapObjectTag);
		const auto stride = dart::ArgumentsDescriptor::named_entry_size();
		if (address.index == X86_REG_INVALID && entry >= 0 && entry < UINT8_MAX * stride) {
			if (entry % stride == dart::ArgumentsDescriptor::position_offset())
				return {Position, static_cast<int>(entry / stride)};
			if (entry % stride == dart::ArgumentsDescriptor::name_offset()) return {DescriptorName};
		}
		if (address.index != X86_REG_INVALID && address.scale == dart::kCompressedWordSize / 2 &&
			address.disp == dart::Array::data_offset() - dart::kHeapObjectTag)
			return {Position, -1}; // Dynamic entry: ordinal/name position is not yet proven.
	}
	if (base == Reg{Reg::RBP} && address.index != X86_REG_INVALID) {
		const Reg index{address.index};
		// PrologueBuilder copies mandatory stack arguments after skipping
		// optional_count = argc - fixed_count. This is a symbolic incoming
		// location, not a constant FP offset or a declaration ordinal.
		if (observingIncoming && index.IsSet() && registers[index].kind == OptionalCount &&
			address.scale == dart::kWordSize / 2 && address.disp >= 2 * dart::kWordSize &&
			address.disp <= UINT8_MAX * dart::kWordSize && address.disp % dart::kWordSize == 0)
			return stackSource(address.disp, registers[index].value);
		if (index.IsSet() && registers[index].kind == CountMinusPosition &&
			address.scale == dart::kWordSize / 2 && address.disp == dart::kWordSize) {
			// Required named arguments have no comparison/default diamond.
			// Retain their proven descriptor-entry identity, not an erased name
			// or declaration ordinal. Speculative diamond paths stay NamedValue.
			if (incoming && observingIncoming && registers[index].value >= 0)
				return stackSource(address.disp, -1, registers[index].value);
			return {NamedValue, -1};
		}
		if (index.IsSet() && (registers[index].kind == OptionalCount || registers[index].kind == Count) &&
			address.scale == dart::kWordSize / 2 && address.disp <= dart::kWordSize &&
			address.disp >= -UINT8_MAX * dart::kWordSize && address.disp % dart::kWordSize == 0)
			return {NamedValue, static_cast<int>((dart::kWordSize - address.disp) / dart::kWordSize)};
		if (index.IsSet() && registers[index].kind == DescriptorSize &&
			address.scale == dart::kWordSize / 2 && address.disp == 2 * dart::kWordSize)
			return {TypeArgsValue};
	}
	return {};
}

void X64ParameterRecovery::writtenRegister(Reg reg, Registers& registers, bool commit)
{
	if (!reg.IsSet()) return;
	registers[reg] = {};
	if (commit) for (auto& parameter : data.params.params)
		if (parameter.valReg == reg) parameter.valReg.Clear();
}

void X64ParameterRecovery::invalidate(const cs_insn& insn, Registers& registers, bool commit)
{
	visitWrittenRegisters(insn, [&](Reg reg) { writtenRegister(reg, registers, commit); });
	const auto& x = insn.detail->x86;
	for (unsigned i = 0; i < x.op_count; ++i) {
		const auto& op = x.operands[i];
		if (!(op.access & CS_AC_WRITE))
			continue;
		if (op.type != X86_OP_MEM || op.mem.base != X86_REG_RBP)
			continue;
		const bool exact = isMemoryOperand(op, X86_REG_RBP);
		const int64_t start = exact ? op.mem.disp : INT32_MIN;
		const int64_t end = exact ? op.mem.disp + op.size : INT64_MAX;
		if (commit)
			overwrittenIncoming.emplace_back(start, end);
		const auto overlaps = [&](int64_t offset) { return start < offset + dart::kWordSize && offset < end; };
		if (commit) for (auto& parameter : data.params.params)
			if (parameter.localOffset && overlaps(parameter.localOffset)) parameter.localOffset = 0;
		std::erase_if(locals, [&](const auto& slot) { return overlaps(slot.first); });
	}
}

// Parameter identity comes from the source, never from its new register number.
void X64ParameterRecovery::recordLocation(Source source, Reg reg, int64_t spill)
{
	if (source.kind == IncomingValue) {
		auto& binding = bindings[source.value];
		binding.observed = true;
		if (reg.IsSet()) binding.info.valReg = reg;
		observedStackTop = std::max(observedStackTop, binding.info.paramOffset);
	}
	if (source.kind == StackValue)
		observedStackTop = std::max(observedStackTop, source.value);
	if (source.kind == ParameterValue && source.value >= 0 && source.value < data.params.NumParam()) {
		if (reg.IsSet()) data.params[source.value].valReg = reg;
		if (spill) data.params[source.value].localOffset = spill;
	}
}

void X64ParameterRecovery::transfer(const cs_insn& insn, Registers& registers, bool commit)
{
	const auto& x = insn.detail->x86;
	if (isRegisterSwap(insn)) {
		const Reg left{x.operands[0].reg}, right{x.operands[1].reg};
		std::swap(registers[left], registers[right]);
		if (commit) {
			recordLocation(registers[left], left);
			recordLocation(registers[right], right);
		}
		return;
	}
	Source result;
	Reg dst;
	int64_t spill = 0;
	if (x.op_count == 2 && x.addr_size == dart::kWordSize) {
		const auto& left = x.operands[0];
		const auto& right = x.operands[1];
		if (isParameterValueMove(insn)) {
			result = source(right, registers, commit);
			// The supplied argument is already proven by descriptor arithmetic.
			// Only its exact Double payload load may carry that source to XMM.
			if (insn.id == X86_INS_MOVSD && right.type == X86_OP_MEM) {
				const Reg object{right.mem.base};
				if (object.IsSet() && registers[object].kind == NamedValue &&
					isMemoryOperand(right, right.mem.base, dart::Double::value_offset() - dart::kHeapObjectTag))
					result = registers[object];
			}
			if (left.type == X86_OP_REG)
				dst = Reg{left.reg};
			else if (isMemoryOperand(left, X86_REG_RBP) && left.mem.disp < 0 &&
				left.mem.disp >= -frameSize && left.mem.disp % dart::kWordSize == 0)
				spill = left.mem.disp;
		}
#if defined(DART_COMPRESSED_POINTERS)
		// Descriptor fields use LoadCompressedSmi (MOV32), while names and
		// closure contexts use LoadCompressed (MOV32 + heap base). Limit this
		// transfer to proven VM fields; truncated argument pointers do not pass.
		if (insn.id == X86_INS_MOV && isRegisterOfSize(left, dart::kCompressedWordSize) &&
			right.type == X86_OP_MEM && right.size == dart::kCompressedWordSize) {
			const auto input = source(right, registers);
			if (input.kind == Count || input.kind == DescriptorSize || input.kind == TypeArgsLength ||
				input.kind == Position || input.kind == DescriptorName || input.kind == ContextValue) {
				result = input.kind == ContextValue ? Source{CompressedContext} : input;
				dst = Reg{left.reg};
			}
		}
		// Descriptor arithmetic is on tagged 32-bit counts/positions, then
		// MOVSXD prepares a native-width stack index. This never propagates an
		// arbitrary truncated argument or heap pointer as an intact value.
		if ((insn.id == X86_INS_MOVSXD || insn.id == X86_INS_MOV) &&
			isRegisterOfSize(right, dart::kCompressedWordSize) && isTaggedRegister(left)) {
			const auto input = source(right, registers);
			if (input.kind == Count || input.kind == OptionalCount || input.kind == DescriptorSize ||
				input.kind == TypeArgsLength || input.kind == Position || input.kind == CountMinusPosition) {
				result = input;
				dst = Reg{left.reg};
			}
		}
		if (isDecompression(insn)) {
			const auto input = source(left, registers);
			if (input.kind == DescriptorName || input.kind == CompressedContext || input.kind == Position) {
				result = input.kind == CompressedContext ? Source{ContextValue} : input;
				dst = Reg{left.reg};
			}
		}
#endif
		if (insn.id == X86_INS_SUB && isTaggedRegister(left)) {
			if (source(left, registers).kind == Count && source(right, registers).kind == Position &&
				left.size == dart::kCompressedWordSize) {
				result = {CountMinusPosition, source(right, registers).value};
				dst = Reg{left.reg};
			}
			if (source(left, registers).kind == Count && right.type == X86_OP_IMM &&
				right.imm >= 0 && right.imm <= 2 * UINT8_MAX && (right.imm & 1) == 0) {
				result = {OptionalCount, static_cast<int>(right.imm >> 1)};
				dst = Reg{left.reg};
			}
		}
	}
	// Async entry uses a literal zero optional-count index, then accesses
	// the closure/context parameter through FP + index*4 + slot. Require the
	// exact zero definition; an arbitrary indexed FP access has no fixed slot.
	if (integerConstant(insn) == 0) {
		dst = Reg{x.operands[0].reg};
		result = {ZeroIndex};
	}
	invalidate(insn, registers, commit);
	if (dst.IsSet())
		registers[dst] = result;
	if (commit)
		recordLocation(result, dst, spill);
	if (spill) {
		locals[spill] = result;
		if (commit && function.IsAsync() && result.kind == NullValue && spill == -dart::kWordSize)
			suspendState = true;
		if (commit && result.kind == ContextValue) data.closureContextLocalOffset = spill;
		if (commit && result.kind == TypeArgsValue) data.typeArgumentLocalOffset = spill;
	}
}

bool X64ParameterRecovery::parameterMove(const cs_insn& insn, const Registers& registers)
{
	const auto& x = insn.detail->x86;
	if (x.op_count != 2 || x.addr_size != dart::kWordSize)
		return false;
	const auto& dst = x.operands[0];
	const auto& src = x.operands[1];
	if (!isParameterValueMove(insn))
		return false;
	const auto input = source(src, registers, true);
	// EmitFrameEntry initializes :suspend_state before InitSuspendableFunction
	// so GC/exception handling can inspect it. This is real entry setup even
	// with no surviving argument copies; it does not add a parameter.
	const bool suspendInit = function.IsAsync() && input.kind == NullValue &&
		isMemoryOperand(dst, X86_REG_RBP, -dart::kWordSize);
	if (input.kind != ParameterValue && input.kind != IncomingValue && !suspendInit)
		return false;
	if (dst.type == X86_OP_REG)
		return Reg{dst.reg}.IsSet() && !isVmStateRegister(Reg{dst.reg});
	if (!isMemoryOperand(dst, X86_REG_RBP))
		return false;
	return dst.mem.disp < 0 && dst.mem.disp >= -frameSize && dst.mem.disp % dart::kWordSize == 0;
}

bool X64ParameterRecovery::parameterInstruction(const cs_insn& insn, const Registers& registers) const
{
	switch (insn.id) {
	case X86_INS_MOV: case X86_INS_MOVABS: case X86_INS_MOVSD: case X86_INS_MOVSXD:
	case X86_INS_MOVAPS: case X86_INS_MOVAPD: case X86_INS_MOVQ: case X86_INS_XCHG:
	case X86_INS_XORPS: case X86_INS_XORPD: case X86_INS_LEA:
	case X86_INS_ADD: case X86_INS_SUB: case X86_INS_SHL:
	case X86_INS_SHR: case X86_INS_SAR: case X86_INS_XOR:
	case X86_INS_AND: case X86_INS_OR:
		break;
	default:
		return false;
	}
	const auto& x = insn.detail->x86;
	if (x.addr_size != dart::kWordSize) return false;
	for (unsigned i = 0; i < x.op_count; ++i) {
		const auto& op = x.operands[i];
		if (op.type != X86_OP_MEM) continue;
		if (op.mem.segment != X86_REG_INVALID) return false;
		if (op.access & CS_AC_WRITE) {
			if (!isMemoryOperand(op, X86_REG_RBP) || op.mem.disp >= 0 ||
				op.mem.disp < -frameSize || op.size != dart::kWordSize)
				return false;
			continue;
		}
		const Reg base{op.mem.base};
		if (!base.IsSet()) return false;
		if (base == Reg{Reg::RBP} || base == Reg{dart::THR} || base == Reg{dart::PP}) continue;
		if (insn.id == X86_INS_MOVSD && op.size == 8 && registers[base].kind == NamedValue &&
			isMemoryOperand(op, op.mem.base, dart::Double::value_offset() - dart::kHeapObjectTag))
			continue;
		if (registers[base].kind != Descriptor) return false;
	}
	return true;
}

std::unique_ptr<VarValue> X64ParameterRecovery::constant(const cs_x86_op& operand, bool unboxedDouble)
{
	if (operand.type == X86_OP_IMM) {
		if ((operand.imm & dart::kSmiTagMask) == dart::kSmiTag)
			return std::make_unique<VarInteger>(operand.imm, dart::kSmiCid);
		return nullptr;
	}
	if (auto value = threadConstant(operand)) return value;
	intptr_t offset;
	if (!poolOffset(app, operand, offset))
		return nullptr;
	const auto index = PoolIndexFromOffset(offset);
	const auto& pool = app.GetObjectPool();
	if (index < 0 || index >= pool.Length())
		return nullptr;
	if (unboxedDouble) {
		if (pool.TypeAt(index) != dart::ObjectPool::EntryType::kImmediate)
			return nullptr;
		const auto bits = pool.RawValueAt(index);
		double value;
		std::memcpy(&value, &bits, sizeof(value));
		return std::make_unique<VarDouble>(value);
	}
	if (pool.TypeAt(index) != dart::ObjectPool::EntryType::kTaggedObject)
		return nullptr;
	const auto& object = dart::Object::Handle(pool.ObjectAt(index));
	if (object.IsSmi())
		return std::make_unique<VarInteger>(dart::RawSmiValue(dart::Smi::Cast(object).ptr()), dart::kSmiCid);
	if (object.IsNull())
		return std::make_unique<VarNull>();
	if (object.IsString())
		return std::make_unique<VarString>(dart::String::Cast(object).ToCString());
	if (object.IsBool())
		return std::make_unique<VarBoolean>(dart::Bool::Cast(object).value());
	if (object.IsDouble())
		return std::make_unique<VarDouble>(dart::Double::Cast(object).value());
	// A default constant need not be primitive. Keep its actual snapshot
	// representation without resolving functions or splitting aggregate stubs.
	return std::make_unique<VarExpression>(object.ToCString(), object.GetClassId());
}

std::optional<std::string> X64ParameterRecovery::comparedName(
	const cs_insn& insn, const Registers& registers)
{
	if (insn.id != X86_INS_CMP || insn.detail->x86.op_count != 2)
		return std::nullopt;
	if (insn.detail->x86.addr_size != dart::kWordSize)
		return std::nullopt;
	const auto* ops = insn.detail->x86.operands;
	if (ops[0].size != ops[1].size ||
		(ops[0].size != dart::kWordSize && ops[0].size != dart::kCompressedWordSize))
		return std::nullopt;
	for (int i = 0; i < 2; ++i) {
		const auto entry = source(ops[i], registers);
		if (entry.kind != DescriptorName && !(entry.kind == Position && entry.value < 0)) continue;
		auto value = constant(ops[1 - i]);
		if (value && value->RawTypeId() == dart::kStringCid)
			return static_cast<VarString*>(value.get())->str;
	}
	return std::nullopt;
}

bool X64ParameterRecovery::traceDefault(size_t index, DefaultPath& path)
{
	const auto& insn = *instructions.Ptr(index);
	if (!parameterInstruction(insn, path.registers)) return false;
	const auto& x = insn.detail->x86;
	auto& defaults = path.defaults;
	if (isRegisterSwap(insn)) {
		std::swap(defaults[Reg{x.operands[0].reg}], defaults[Reg{x.operands[1].reg}]);
	} else {
		Reg destination;
		DefaultConstant value;
		if (isParameterValueMove(insn) && x.operands[0].type == X86_OP_REG) {
			destination = Reg{x.operands[0].reg};
			const auto& input = x.operands[1];
			if (input.type == X86_OP_REG && Reg{input.reg}.IsSet())
				value = std::move(defaults[Reg{input.reg}]);
			else
				value = {constant(input, insn.id == X86_INS_MOVSD), index + 1};
		}
		if (auto integer = integerConstant(insn)) {
			destination = Reg{x.operands[0].reg};
			value = {std::make_unique<VarInteger>(*integer, VarValue::NativeInt), index + 1};
		}
		// Only a paired supplied Double payload proves scalar interpretation.
		if ((insn.id == X86_INS_XORPS || insn.id == X86_INS_XORPD) && x.op_count == 2 &&
			isRegisterOfSize(x.operands[0], 16) && isRegisterOfSize(x.operands[1], 16) &&
			x.operands[0].reg == x.operands[1].reg) {
			destination = Reg{x.operands[0].reg};
			value = {std::make_unique<VarDouble>(0.0), index + 1};
		}
		visitWrittenRegisters(insn, [&](Reg reg) { defaults[reg] = {}; });
		if (destination.IsSet()) defaults[destination] = std::move(value);
	}
	transfer(insn, path.registers);
	return true;
}

// PrologueBuilder increments optional_count_vars_processed even if optimization
// eliminates the parameter value. Only a counter update remains on the matched
// name arm. Continue with intersected sources, retaining raw IL and publishing
// no parameter/default for the eliminated value.
std::optional<X64ParameterRecovery::NamedResult> X64ParameterRecovery::unusedNamed(
	size_t index, size_t join, const Registers& registers)
{
	if (join < index + 3 || join > index + 5 ||
		!targets.HasOnlyIncoming(index + 2, join, {{join, index + 1}}))
		return std::nullopt;
	size_t next = index + 2;
	const auto& add = *instructions.Ptr(next++);
	const auto& op = add.detail->x86.operands;
	if (add.id != X86_INS_ADD || add.detail->x86.op_count != 2 || !isRegisterOfSize(op[0], 8))
		return std::nullopt;
	const auto counter = op[0].reg;
	if (isVmStateRegister(Reg{counter}) ||
		(!isImmediateOperand(op[1], 1) && !isImmediateOperand(op[1], 2)))
		return std::nullopt;
	if (next < join && instructions.Ptr(next)->id == X86_INS_SAR) {
		const auto& shift = instructions.Ptr(next++)->detail->x86;
		if (op[1].imm != 2 || shift.op_count != 2 ||
			!isRegisterOperand(shift.operands[0], counter) || !isImmediateOperand(shift.operands[1], 1))
			return std::nullopt;
	}
	if (next < join) {
		const auto& copy = *instructions.Ptr(next++);
		const auto& x = copy.detail->x86;
		if (copy.id != X86_INS_MOV || x.op_count != 2 || !isRegisterOfSize(x.operands[0], 8) ||
			!isRegisterOperand(x.operands[1], counter) || isVmStateRegister(Reg{x.operands[0].reg}))
			return std::nullopt;
	}
	if (next != join)
		return std::nullopt;
	NamedResult result;
	result.join = join;
	result.registers = registers;
	for (size_t i = index + 2; i < join; ++i)
		visitWrittenRegisters(*instructions.Ptr(i), [&](Reg reg) { result.registers[reg] = {}; });
	return result;
}

// Reuse the ordinary Smi/Mint decoder; the proven argument source adds
// identity, not a second machine pattern. Only its own JAE join is admitted.
bool X64ParameterRecovery::unboxParameter(size_t& index, size_t end, Registers& registers,
	std::vector<std::pair<size_t, size_t>>& edges)
{
	InsnCursor cursor{instructions, targets, index};
	auto unbox = readUnboxInt(cursor);
	if (!unbox || cursor.Position() >= end)
		return false;
	const auto input = registers[unbox->srcObjReg];
	if (input.kind != NamedValue)
		return false;
	edges.emplace_back(cursor.Position() + 1, cursor.Position() - 1);
	for (size_t i = index; i <= cursor.Position(); ++i)
		invalidate(*instructions.Ptr(i), registers, false);
	registers[unbox->dstReg] = {UnboxedNamedValue, input.value};
	index = cursor.Position();
	return true;
}

// PrologueBuilder links missing positional arguments through a shared default
// tail; named arguments normally form single diamonds. Decode both using the
// same source/default transfer rules. Only forward entry tests are admitted,
// with complete instruction coverage and no undeclared incoming edges.
std::vector<X64ParameterRecovery::NamedResult> X64ParameterRecovery::parameterDefaults(
	size_t index, const Registers& registers)
{
	const LocalScope localScope{locals};
	std::vector<DefaultPath> missing;
	std::vector<std::pair<size_t, size_t>> edges;
	auto supplied = registers;
	Source count;
	int firstOptional = -1;
	size_t join = 0;
	const auto limit = std::min(index + 64, instructions.Count());
	std::array<bool, 64> visited{};
	for (size_t i = index; i < limit; ++i) {
		visited[i - index] = true;
		if (!missing.empty() && i == missing.front().start) {
			if (missing.size() != 1 || missing.front().optional >= 0) return {};
			auto unused = unusedNamed(index, i, registers);
			std::vector<NamedResult> result;
			if (unused) result.push_back(std::move(*unused));
			return result;
		}
		const auto& insn = *instructions.Ptr(i);
		const auto& x = insn.detail->x86;
		auto name = comparedName(insn, supplied);
		if (name || (insn.id == X86_INS_CMP && x.op_count == 2)) {
			int optional = -1;
			if (name) {
				if (!missing.empty()) return {};
			} else {
				const auto input = source(x.operands[0], supplied);
				const auto& threshold = x.operands[1];
				if (!isTaggedRegister(x.operands[0]) || threshold.type != X86_OP_IMM ||
					threshold.imm < 2 || threshold.imm > 2 * UINT8_MAX || (threshold.imm & 1)) return {};
				optional = threshold.imm / 2 - 1;
				if (missing.empty()) { count = input; firstOptional = optional; }
				if ((count.kind != Count && count.kind != OptionalCount) || input != count ||
					optional != firstOptional + static_cast<int>(missing.size())) return {};
				name = std::format("optional_{}", optional);
			}
			if (i + 1 >= limit) return {};
			const auto& branch = *instructions.Ptr(++i);
			visited[i - index] = true;
			const auto target = targets.Destination(branch);
			if (branch.id != (optional < 0 ? X86_INS_JNE : X86_INS_JL) ||
				!target || *target <= i + 1 || *target >= limit) return {};
			missing.push_back({*target, supplied, *name, optional});
			edges.emplace_back(*target, i);
		} else if (insn.id == X86_INS_JMP) {
			const auto target = targets.Destination(insn);
			if (!target || *target <= i || *target >= limit) return {};
			join = *target;
			edges.emplace_back(join, i);
			break;
		} else {
			if (missing.empty()) return {};
			const auto begin = i;
			if (!unboxParameter(i, limit, supplied, edges)) {
				if (!parameterInstruction(insn, supplied)) return {};
				transfer(insn, supplied);
			}
			std::fill(visited.begin() + (begin - index), visited.begin() + (i - index + 1), true);
		}
	}
	if (missing.empty() || !join) return {};
	for (auto& path : missing) {
		locals = localScope.saved;
		if (path.start >= join) return {};
		for (size_t i = path.start; i < join; ++i) {
			visited[i - index] = true;
			const auto& insn = *instructions.Ptr(i);
			if (insn.id == X86_INS_JMP) {
				const auto target = targets.Destination(insn);
				if (!target || *target <= i || *target > join) return {};
				edges.emplace_back(*target, i);
				i = *target - 1;
			} else if (!traceDefault(i, path)) return {};
		}
	}
	if (!targets.HasOnlyIncoming(index + 2, join, edges) ||
		!std::all_of(visited.begin(), visited.begin() + (join - index), [](bool covered) { return covered; }))
		return {};
	return defaultResults(missing, supplied, join);
}

// A later missing path must preserve earlier supplied arguments. Earlier
// missing paths must reach the exact same constant definition for later ones;
// textual equality of rendered defaults is not sufficient evidence.
std::vector<X64ParameterRecovery::NamedResult> X64ParameterRecovery::defaultResults(
	std::vector<DefaultPath>& missing, const Registers& supplied, size_t join)
{
	std::vector<NamedResult> results(missing.size());
	for (size_t k = 0; k < results.size(); ++k) {
		auto& result = results[k];
		result.join = join;
		result.optional = missing[k].optional;
		result.isNamed = result.optional < 0;
		result.parameter.name = missing[k].name;
		for (int r = 0; r < Reg::kNumberOfRegisters; ++r) {
			bool unchanged = true;
			for (const auto& path : missing) unchanged &= path.registers[r] == supplied[r];
			if (unchanged) result.registers[r] = supplied[r];
			const bool unboxed = supplied[r].kind == UnboxedNamedValue;
			if ((supplied[r].kind != NamedValue && !unboxed) || supplied[r].value != result.optional ||
				!missing[k].defaults[r].value) continue;
			for (size_t path = 0; path < missing.size(); ++path) {
				if (path > k ? missing[path].registers[r] != supplied[r] :
					!missing[path].defaults[r].value || missing[path].defaults[r].origin != missing[k].defaults[r].origin) return {};
			}
			auto& value = missing[k].defaults[r].value;
			if (value->RawTypeId() == dart::kIntegerCid) {
				auto* integer = static_cast<VarInteger*>(value.get());
				if (unboxed && integer->intTypeId != VarValue::NativeInt) return {};
				if (!unboxed && integer->intTypeId == VarValue::NativeInt) {
					if ((integer->val & dart::kSmiTagMask) != dart::kSmiTag) return {};
					integer->intTypeId = dart::kSmiCid;
				}
			} else if (unboxed) return {};
			result.parameter.valReg = Reg{static_cast<Reg::Value>(r)};
			result.parameter.val = std::move(value);
			result.locations.push_back(result.parameter.valReg);
		}
		if (!result.locations.empty()) continue;
		// A name-presence flag is not a parameter: retain raw IL and continue.
		const auto start = missing[k].start;
		if (!result.isNamed || results.size() != 1 || start < 2 || join != start + 1) return {};
		const auto& yes = *instructions.Ptr(start - 2);
		const auto& no = *instructions.Ptr(start);
		if (integerConstant(yes) != 1 || integerConstant(no) != 0 ||
			Reg{yes.detail->x86.operands[0].reg} != Reg{no.detail->x86.operands[0].reg} ||
			isVmStateRegister(Reg{yes.detail->x86.operands[0].reg})) return {};
	}
	return results;
}

std::optional<X64ParameterRecovery::NamedResult> X64ParameterRecovery::typeArguments(
	size_t index, const Registers& registers)
{
	const auto& test = *instructions.Ptr(index);
	const auto& x = test.detail->x86;
	if (test.id != X86_INS_TEST || x.op_count != 2 || index + 1 >= instructions.Count())
		return std::nullopt;
	if (source(x.operands[0], registers).kind != TypeArgsLength)
		return std::nullopt;
	if (x.operands[0].type != X86_OP_REG || x.operands[1].type != X86_OP_REG ||
		x.operands[0].reg != x.operands[1].reg)
		return std::nullopt;
	const auto& branch = *instructions.Ptr(index + 1);
	if (branch.id != X86_INS_JNE)
		return std::nullopt;
	const auto supplied = targets.Destination(branch);
	if (!supplied || *supplied <= index + 2 || *supplied - index > 8)
		return std::nullopt;
	const auto& jump = *instructions.Ptr(*supplied - 1);
	if (jump.id != X86_INS_JMP)
		return std::nullopt;
	const auto join = targets.Destination(jump);
	if (!join || *join <= *supplied || *join - *supplied > 8)
		return std::nullopt;
	if (!targets.HasOnlyIncoming(index + 2, *join,
		{{*supplied, index + 1}, {*join, *supplied - 1}}))
		return std::nullopt;
	const LocalScope localScope{locals};
	Registers absent = registers;
	Reg nullRegister;
	for (size_t i = index + 2; i < *supplied - 1; ++i) {
		const auto& insn = *instructions.Ptr(i);
		const auto& op = insn.detail->x86;
		if (insn.id != X86_INS_MOV || op.op_count != 2 ||
			!isRegisterOfSize(op.operands[0], dart::kWordSize))
			return std::nullopt;
		if (!isMemoryOperand(op.operands[1], CSREG_DART_THR, dart::Thread::object_null_offset()))
			return std::nullopt;
		nullRegister = Reg{op.operands[0].reg};
		transfer(insn, absent);
	}
	auto present = registers;
	for (size_t i = *supplied; i < *join; ++i) {
		const auto& insn = *instructions.Ptr(i);
		if (!parameterInstruction(insn, present)) return std::nullopt;
		transfer(insn, present);
	}
	if (!nullRegister.IsSet() || present[nullRegister].kind != TypeArgsValue)
		return std::nullopt;
	NamedResult result;
	result.join = *join;
	for (int r = 0; r < Reg::kNumberOfRegisters; ++r)
		if (present[r] == absent[r]) result.registers[r] = present[r];
	result.registers[nullRegister] = {TypeArgsValue};
	result.locations.push_back(nullRegister);
	return result;
}

int X64ParameterRecovery::publish(FnParamInfo&& parameter, bool isNamed, int optional)
{
	if (hasDeclaration) {
		for (size_t i = 0; i < data.params.params.size(); ++i) {
			auto& known = data.params.params[i];
			if (isNamed ? known.name != parameter.name : i != data.params.numFixedParam + optional)
				continue;
			known.valReg = parameter.valReg;
			known.localOffset = parameter.localOffset;
			known.val = std::move(parameter.val);
			return i;
		}
		return -1;
	}
	data.params.isPartial = true;
	data.params.isNamedParam = isNamed;
	data.params.add(std::move(parameter));
	return data.params.NumParam() - 1;
}

X64ParameterRecovery::Source X64ParameterRecovery::stackSource(int64_t offset, int countBias, int namedEntry)
{
	for (size_t i = 0; i < bindings.size(); ++i) {
		const auto& binding = bindings[i];
		const auto location = countBias < 0 && namedEntry < 0 ? binding.info.paramOffset : binding.indexedOffset;
		if (binding.countBias == countBias && binding.namedEntry == namedEntry && location == offset)
			return {IncomingValue, static_cast<int>(i)};
	}
	FnParamInfo info;
	if (countBias < 0 && namedEntry < 0) info.paramOffset = offset;
	info.name = namedEntry >= 0 ? std::format("named_slot_{}", namedEntry) :
		countBias < 0 ? std::format("stack_{:#x}", offset) :
		std::format("stack[(argc-{})*{}+{:#x}]", countBias, dart::kWordSize, offset);
	bindings.push_back({std::move(info), false, -1, countBias, offset, namedEntry});
	return {IncomingValue, static_cast<int>(bindings.size() - 1)};
}

void X64ParameterRecovery::bindIncoming(Registers& registers)
{
	auto bind = [&](Source& source) {
		if (source.kind != IncomingValue)
			return;
		const auto index = bindings[source.value].parameter;
		source = index >= 0 ? Source{ParameterValue, index} : Source{};
	};
	for (auto& source : registers) bind(source);
	for (auto& [offset, source] : locals) bind(source);
}

void X64ParameterRecovery::finishIncoming(Registers& registers)
{
	if (!observingIncoming)
		return;
	observingIncoming = false;
	for (size_t i = 0; i < bindings.size(); ++i) {
		auto& binding = bindings[i];
		if (!binding.observed)
			continue;
		auto& info = binding.info;
		const Source owner{IncomingValue, static_cast<int>(i)};
		if (info.valReg.IsSet() && registers[info.valReg] != owner)
			info.valReg.Clear();
		for (int reg = 0; !info.valReg.IsSet() && reg < Reg::kNumberOfRegisters; ++reg)
			if (registers[reg] == owner) info.valReg = Reg{static_cast<Reg::Value>(reg)};
		for (const auto& [offset, source] : locals)
			if (source == owner && (!info.localOffset || offset > info.localOffset))
				info.localOffset = offset;
		if (receiver.IsSet() && info.paramReg == receiver) {
			info.name = "this";
			info.type = function.Class().DeclarationType();
		}
		if (!hasDeclaration) {
			FnParamInfo parameter{info.valReg, info.localOffset, info.type, info.name, nullptr};
			parameter.paramReg = info.paramReg;
			parameter.paramOffset = info.paramOffset;
			binding.parameter = receiver.IsSet() && info.paramReg == receiver ? receiverParameter : -1;
			if (binding.parameter >= 0)
				data.params[binding.parameter] = std::move(parameter);
			else {
				binding.parameter = data.params.NumParam();
				if (binding.namedEntry >= 0) {
					data.params.isNamedParam = true;
					data.params.add(std::move(parameter));
				} else data.params.addFixedParam(std::move(parameter));
			}
			data.params.isPartial = true;
		}
		data.incomingParameters.push_back(std::move(info));
	}
	bindIncoming(registers);
}

void X64ParameterRecovery::combine(size_t begin, size_t end)
{
	if (begin >= end || end >= instructions.Count())
		return;
	const auto start = instructions.Ptr(begin)->address;
	const auto stop = instructions.Ptr(end)->address;
	auto first = std::find_if(data.il_insns.begin(), data.il_insns.end(),
		[&](const auto& il) { return il->Start() == start; });
	if (first == data.il_insns.end())
		return;
	auto last = std::find_if(first, data.il_insns.end(),
		[&](const auto& il) { return il->Start() == stop; });
	if (last == data.il_insns.end())
		return;
	const auto index = first - data.il_insns.begin();
	data.il_insns.erase(first, last);
	data.il_insns.insert(data.il_insns.begin() + index,
		std::make_unique<SetupParametersInstr>(AddrRange{start, stop}, &data.params));
}

// Named-argument counters may prevent the linear source pass from reaching
// the generic-argument diamond. Its descriptor source can still be proven
// independently: no call, no back edge, and no write to ARGS_DESC_REG before
// an adjacent length-load / test. This does not interpret those counters.
void X64ParameterRecovery::descriptorTypeArguments(size_t begin)
{
	if (data.typeArgumentReg.IsSet())
		return;
	size_t limit = begin;
	while (limit < instructions.Count() && !isStackLimitCompare(*instructions.Ptr(limit)))
		++limit;
	if (limit == instructions.Count())
		return;
	for (size_t i = begin; i + 1 < limit; ++i) {
		const auto& insn = *instructions.Ptr(i);
		if (isTrap(insn))
			return;
		if (isControlTransfer(insn)) {
			const auto target = targets.Destination(insn);
			if (!isInGroup(&insn, CS_GRP_JUMP) || !target || *target <= i || *target > limit)
				return;
		}
		bool writesDescriptor = false;
		visitWrittenRegisters(insn, [&](Reg reg) { writesDescriptor |= reg == Reg{dart::ARGS_DESC_REG}; });
		if (writesDescriptor)
			return;
		if (insn.id != X86_INS_MOV || insn.detail->x86.op_count != 2 ||
			!isRegisterOfSize(insn.detail->x86.operands[0], dart::kCompressedWordSize) ||
			targets.contains(instructions.Ptr(i + 1)->address))
			continue;
		Registers registers{};
		registers[Reg{dart::ARGS_DESC_REG}] = {Descriptor};
		if (source(insn.detail->x86.operands[1], registers).kind != TypeArgsLength)
			continue;
		const LocalScope localScope{locals};
		transfer(insn, registers);
		if (auto result = typeArguments(i + 1, registers)) {
			if (result->join > limit)
				return;
			data.typeArgumentReg = result->locations.front();
			combine(i + 1, result->join);
			return;
		}
	}
}

void X64ParameterRecovery::Recover()
{
	size_t begin = 0;
	if (function.IsFfi())
		return;
	signature();
	if (!readEntryFrame(instructions, targets, begin, frameSize))
		return;
	Registers registers{};
	observingIncoming = function.Ptr() != dart::Function::null();
	if (observingIncoming)
		seedIncoming(registers);
	registers[Reg{dart::ARGS_DESC_REG}] = {Descriptor};
	for (int i = 0; i < data.params.NumParam(); ++i) {
		const auto& parameter = data.params[i];
		if (parameter.paramReg.IsSet()) registers[parameter.paramReg] = {ParameterValue, i};
	}
	std::optional<size_t> descriptorBegin;
	std::optional<size_t> provenJoin;
	size_t moveBegin = begin;
	bool moving = false;
	size_t i = begin;
	// A retained arity identifies closure parameter zero exactly. Without it,
	// the largest observed FP argument slot is only a partial convention hint.
	for (; i < instructions.Count(); ++i) {
		const auto& insn = *instructions.Ptr(i);
		// Continue after our own verified diamond. An unrelated incoming edge
		// still ends the linear source pass; the compound decoder proves join predecessors.
		if (targets.contains(insn.address) && provenJoin != i)
			break;
		if (observingIncoming && endsParameterEntry(insn, targets))
			finishIncoming(registers);
		const bool move = !targets.contains(insn.address) && parameterMove(insn, registers);
		if (moving && !move) combine(moveBegin, i);
		if (!moving && move) moveBegin = i;
		moving = move;
		if (isStackLimitCompare(insn) || isTrap(insn))
			break;
		const auto& x = insn.detail->x86;
		if (!descriptorBegin && x.op_count == 2 && insn.id == X86_INS_MOV) {
			const auto input = source(x.operands[1], registers);
			if (input.kind == Count || input.kind == TypeArgsLength || input.kind == Descriptor)
				descriptorBegin = i;
		}
		auto result = typeArguments(i, registers);
		const bool generic = result.has_value();
		std::vector<NamedResult> results;
		if (result) results.push_back(std::move(*result));
		else results = parameterDefaults(i, registers);
		if (!results.empty()) {
			finishIncoming(registers);
			registers = results.front().registers;
			bindIncoming(registers);
			bool published = generic;
			for (auto& recovered : results) {
				int parameter = -1;
				if (generic) data.typeArgumentReg = recovered.locations.front();
				else if (!recovered.locations.empty())
					parameter = publish(std::move(recovered.parameter), recovered.isNamed, recovered.optional);
				if (parameter >= 0) for (auto location : recovered.locations)
					registers[location] = {ParameterValue, parameter};
				published |= parameter >= 0;
			}
			const auto join = results.front().join;
			if (published) combine(i, join);
			provenJoin = join;
			descriptorBegin = join;
			i = join - 1;
			moving = false;
			continue;
		}
		if (isControlTransfer(insn))
			break;
		if (descriptorBegin && !parameterInstruction(insn, registers))
			break;
		transfer(insn, registers, true);
		if (x.op_count == 2 && x.operands[0].type == X86_OP_REG) {
			const Reg destination{x.operands[0].reg};
			if (destination.IsSet() && registers[destination].kind == TypeArgsValue)
				data.typeArgumentReg = destination;
			if (destination.IsSet() && registers[destination].kind == ContextValue)
				data.closureContextReg = destination;
		}
		if (hasDeclaration && function.IsClosure() && insn.id == X86_INS_MOV && x.op_count == 2 &&
			isRegisterOfSize(x.operands[0], dart::kWordSize) &&
			isMemoryOperand(x.operands[1], X86_REG_RBP, function.FirstParamOffset()))
			registers[Reg{x.operands[0].reg}] = {ClosureValue};
	}
	finishIncoming(registers);
	if (moving) combine(moveBegin, i);
	descriptorTypeArguments(begin);
}

}

const FunctionAnalyzer::Matcher FunctionAnalyzer::matcherFns[] = {
	&FunctionAnalyzer::processGdtCallInstr,
	&FunctionAnalyzer::processEnterFrameInstr,
	&FunctionAnalyzer::processLeaveFrameInstr,
	&FunctionAnalyzer::processRegisterSaveInstr,
	&FunctionAnalyzer::processAllocateStackInstr,
	&FunctionAnalyzer::processCheckStackOverflowInstr,
	&FunctionAnalyzer::processReturnInstr,
	&FunctionAnalyzer::processTryAllocateObject,
	&FunctionAnalyzer::processBoxInt64Instr,
	&FunctionAnalyzer::processClosureCallInstr,
#ifndef NO_INIT_LATE_STATIC_FIELD
	&FunctionAnalyzer::processInitLateStaticFieldInstr,
#endif
	&FunctionAnalyzer::processCallInstr,
	&FunctionAnalyzer::processTailCallInstr,
	&FunctionAnalyzer::processLeafRuntimeCallInstr,
	&FunctionAnalyzer::processRegisterCallInstr,
	&FunctionAnalyzer::processTypeTestInstr,
	&FunctionAnalyzer::processBarrierStore,
	&FunctionAnalyzer::processWriteBarrierInstr,
	&FunctionAnalyzer::processClassIdMayBeSmiInstr,
	&FunctionAnalyzer::processBranchIfSmiInstr,
	&FunctionAnalyzer::processLoadFieldTableInstr,
	&FunctionAnalyzer::processUnboxIntInstr,
	&FunctionAnalyzer::processLoadStore,
	&FunctionAnalyzer::processLoadDoubleInstr,
	&FunctionAnalyzer::processStorePoolInstr,
	&FunctionAnalyzer::processLoadValueInstr,
	&FunctionAnalyzer::processMoveRegInstr,
#if defined(DART_COMPRESSED_POINTERS)
	&FunctionAnalyzer::processDecompressPointerInstr,
#endif
	&FunctionAnalyzer::processLoadClassIdInstr,
};

void FunctionAnalyzer::asm2il()
{
	prepareInstructions();
	if (function.Ptr() != dart::Function::null()) {
		const auto& vm = dart::Function::Handle(function.Ptr());
		// FlowGraphCompiler::EmitStaticCall loads ARGS_DESC_REG exactly when
		// PrologueNeedsArgumentsDescriptor. Saved descriptors are excluded.
		if (!dart::FunctionType::Handle(vm.signature()).IsNull() && vm.PrologueNeedsArgumentsDescriptor())
			objects[Reg{dart::ARGS_DESC_REG}] = app.FindClass(dart::kArrayCid);
	}
	for (size_t i = 0; i < instructions.Count();) {
		auto* current = instructions.Ptr(i);
		if (targets.contains(current->address)) {
			objects.fill(nullptr);
			nonObjects.fill(false);
		}
		std::unique_ptr<ILInstr> il;
		size_t end = i + 1;
		for (auto matcher : matcherFns) {
			InsnCursor candidate{instructions, targets, i};
			il = (this->*matcher)(candidate);
			if (il) {
				end = candidate.Position() + 1;
				break;
			}
		}
		if (!il)
			il = std::make_unique<UnknownInstr>(current, data.asmTexts.AtAddr(current->address));
		emit(std::move(il), i, end);
		i = end;
	}
	X64ParameterRecovery{app, function, data, instructions, targets}.Recover();
}

} // namespace

AsmTexts CodeAnalyzer::convertAsm(AsmInstructions& instructions)
{
	std::vector<AsmText> texts(instructions.Count());
	uint64_t stackLimit = 0;
	int maxParamOffset = 0;
	for (size_t i = 0; i < instructions.Count(); ++i) {
		const auto* insn = instructions.Ptr(i);
		auto& text = texts[i];
		text.addr = insn->address;
		text.dataType = AsmText::None;
		std::snprintf(text.text, sizeof(text.text), "%-16s%s", insn->mnemonic, insn->op_str);
		const auto& x = insn->detail->x86;
		for (unsigned j = 0; j < x.op_count; ++j) {
			const auto& op = x.operands[j];
			if (isMemoryOperand(op, CSREG_DART_THR) && op.mem.disp >= 0) {
				text.dataType = AsmText::ThreadOffset;
				text.threadOffset = op.mem.disp;
				if (!stackLimit && op.mem.disp == AOT_Thread_stack_limit_offset)
					stackLimit = insn->address;
			}
			// Pool bounds are checked in asm2il, where the app is available.
			if (isMemoryOperand(op, X86_REG_RBP)) {
				if (op.mem.disp >= 16 && op.mem.disp < 0x10000)
					maxParamOffset = std::max(maxParamOffset, static_cast<int>(op.mem.disp));
			}
		}
		if (insn->id != X86_INS_CALL || x.op_count != 1)
			continue;
		if (x.operands[0].type == X86_OP_IMM) {
			text.dataType = AsmText::Call;
			text.callAddress = x.operands[0].imm;
		}
	}
	return AsmTexts{std::move(texts), stackLimit, maxParamOffset};
}

void CodeAnalyzer::asm2il(DartFunction* dartFn, AsmInstructions& instructions)
{
	FunctionAnalyzer analyzer{app, *dartFn, instructions};
	analyzer.asm2il();
}
#endif
