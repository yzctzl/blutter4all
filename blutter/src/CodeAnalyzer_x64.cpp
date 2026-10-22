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

bool isRegisterOperand(const cs_x86_op& op, x86_reg value)
{
	return op.type == X86_OP_REG && op.reg == value;
}

bool isRegisterOfSize(const cs_x86_op& op, uint8_t size)
{
	return op.type == X86_OP_REG && op.size == size;
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


// These predicates describe entry-block boundaries, not parameter patterns.
// Frame aliases stop provenance because later indirect writes may reuse a slot.

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
#if !defined(DART_COMPRESSED_POINTERS)
	std::unique_ptr<ILInstr> processBoxInt64Instr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processUnboxIntInstr(InsnCursor& insn);
#endif
	std::unique_ptr<ILInstr> processClosureCallInstr(InsnCursor& insn);
#ifndef NO_INIT_LATE_STATIC_FIELD
	std::unique_ptr<ILInstr> processInitLateStaticFieldInstr(InsnCursor& insn);
#endif
	std::unique_ptr<ILInstr> processCallInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processRegisterCallInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processBranchIfSmiInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processLoadFieldTableInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processClassIdMayBeSmiInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processTailCallInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processTypeTestInstr(InsnCursor& insn);
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
	LoadValueInstr* previousLoad(uint64_t address);
	DartFnBase* resolveCallTarget(const cs_x86_op& target);

	DartApp& app;
	DartFunction& function;
	AnalyzedFnData& data;
	AsmInstructions& instructions;
	BranchTargets targets;
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

#if !defined(DART_COMPRESSED_POINTERS)
// SDK: vm/compiler/backend/il_x64.cc, BoxInt64Instr::EmitNativeCode;
// assembler_x64.h, SmiTag. ADD alone does not prove Smi tagging.
//   mov rax, value; add rax, rax; jno done
//   [enter frame]; call AllocateMintShared*; [leave frame]
//   mov [rax + Mint::value_offset() - kHeapObjectTag], value
// A temporary frame is present in the checked 3.5.4/3.10.8/3.11.5 sources;
// the checked 2.19.6 shared slow path does not emit that frame.
std::unique_ptr<ILInstr> FunctionAnalyzer::processBoxInt64Instr(InsnCursor& insn)
{
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
	if (value.type != X86_OP_MEM)
		return nullptr;
	if (value.mem.base != destination || value.mem.index != destination)
		return nullptr;
	if (value.mem.scale != 1 || value.mem.segment != X86_REG_INVALID)
		return nullptr;
	if (value.mem.disp != dart::Mint::value_offset())
		return nullptr;
	if (join != insn.Current()->address + insn.Current()->size)
		return nullptr;

	return std::make_unique<UnboxIntInstr>(insn.Range(), Reg{destination}, source, narrow ? 32 : 64);
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processUnboxIntInstr(InsnCursor& insn)
{
	return readUnboxInt(insn);
}
#endif

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


// SDK: vm/compiler/backend/flow_graph_compiler_x64.cc, EmitInstanceCallAOT;
// assembler_x64.cc, LeafRuntimeScope::Call / Assembler::CallCFunction.
// Resolve only adjacent, complete entry-load/call sequences, never arbitrary
// register calls.
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
	if (!insn.RegOp(X86_INS_ADD))
		return nullptr;
	if (!isMemoryOperand(insn.Op(1), CSREG_DART_THR, AOT_Thread_heap_base_offset))
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

const FunctionAnalyzer::Matcher FunctionAnalyzer::matcherFns[] = {
	&FunctionAnalyzer::processGdtCallInstr,
	&FunctionAnalyzer::processEnterFrameInstr,
	&FunctionAnalyzer::processLeaveFrameInstr,
	&FunctionAnalyzer::processAllocateStackInstr,
	&FunctionAnalyzer::processCheckStackOverflowInstr,
	&FunctionAnalyzer::processReturnInstr,
	&FunctionAnalyzer::processTryAllocateObject,
#if !defined(DART_COMPRESSED_POINTERS)
	&FunctionAnalyzer::processBoxInt64Instr,
#endif
	&FunctionAnalyzer::processClosureCallInstr,
#ifndef NO_INIT_LATE_STATIC_FIELD
	&FunctionAnalyzer::processInitLateStaticFieldInstr,
#endif
	&FunctionAnalyzer::processCallInstr,
	&FunctionAnalyzer::processTailCallInstr,
	&FunctionAnalyzer::processRegisterCallInstr,
	&FunctionAnalyzer::processTypeTestInstr,
	&FunctionAnalyzer::processClassIdMayBeSmiInstr,
	&FunctionAnalyzer::processBranchIfSmiInstr,
	&FunctionAnalyzer::processLoadFieldTableInstr,
#if !defined(DART_COMPRESSED_POINTERS)
	&FunctionAnalyzer::processUnboxIntInstr,
#endif
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
	for (size_t i = 0; i < instructions.Count();) {
		auto* current = instructions.Ptr(i);
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
