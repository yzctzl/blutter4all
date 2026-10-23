#include "pch.h"
#include "ObjectPool.h"
#include "CodeAnalyzer.h"
#include "DartApp.h"
#include "DartThreadInfo.h"
#include <cstdio>
#include <cstring>
#include <optional>
#include <unordered_set>

#ifndef NO_CODE_ANALYSIS
namespace
{
using Reg = ARM::Register;

// Unshifted operands are the default. Patterns which require a shifted
// register (CID dispatch, boxing, barrier overlap) check that shift explicitly.
bool isReg(const cs_arm_op& op, int reg)
{
	return op.type == ARM_OP_REG && op.reg == reg && op.shift.type == ARM_SFT_INVALID;
}
bool isImm(const cs_arm_op& op, int value)
{
	return op.type == ARM_OP_IMM && op.imm == value;
}
bool isMemory(const cs_arm_op& op, int base)
{
	if (op.type != ARM_OP_MEM || op.mem.base != base)
		return false;
	return op.mem.index == ARM_REG_INVALID && !op.subtracted;
}
bool isUnconditional(const cs_insn& insn)
{
	return insn.detail->arm.cc == ARM_CC_AL;
}

// ARM has predicated instructions, so an opcode alone is not evidence that a
// Dart operation occurs. Each compound recognizer validates the conditions too.
// Like ARM64's InsnMarker, a candidate only consumes instructions on success.
class InsnCursor
{
	AsmInstructions& instructions;
	const std::unordered_set<uint64_t>& targets;
	size_t start, index;

  public:
	InsnCursor(AsmInstructions& instructions, const std::unordered_set<uint64_t>& targets, size_t index)
		: instructions(instructions), targets(targets), start(index), index(index)
	{
	}
	cs_insn* Current() const
	{
		return instructions.Ptr(index);
	}
	const cs_arm& detail() const
	{
		return Current()->detail->arm;
	}
	const cs_arm_op& op(int i) const
	{
		return detail().operands[i];
	}
	bool Is(unsigned id, int count, arm_cc cc = ARM_CC_AL) const
	{
		return Current()->id == id && detail().op_count == count && detail().cc == cc;
	}
	bool Next()
	{
		if (index + 1 >= instructions.Count())
			return false;
		if (targets.contains(instructions.Ptr(index + 1)->address))
			return false;
		++index;
		return true;
	}
	size_t End() const
	{
		return index + 1;
	}
	AddrRange Range() const
	{
		return {instructions.Ptr(start)->address, Current()->address + Current()->size};
	}
};

// assembler_arm.cc LoadImmediate: MOV/MVN, or MOVW followed by MOVT.
// These are native bit patterns. Do not guess Smi versus an unboxed integer.
std::optional<uint32_t> readImmediate(InsnCursor& insn, arm_reg& reg)
{
	if (!insn.Is(ARM_INS_MOV, 2) && !insn.Is(ARM_INS_MVN, 2) && !insn.Is(ARM_INS_MOVW, 2))
		return std::nullopt;
	if (insn.op(0).type != ARM_OP_REG || insn.op(1).type != ARM_OP_IMM)
		return std::nullopt;
	reg = static_cast<arm_reg>(insn.op(0).reg);
	uint32_t value = insn.op(1).imm;
	if (insn.Current()->id == ARM_INS_MVN)
		value = ~value;
	// Capstone may expose MOVW as MOV-immediate. MOVT replaces the high
	// halfword after either spelling; prove its destination, not its alias.
	{
		auto next = insn;
		if (next.Next() && next.Is(ARM_INS_MOVT, 2) && isReg(next.op(0), reg) &&
			next.op(1).type == ARM_OP_IMM) {
			value = (value & 0xffff) | (uint32_t(next.op(1).imm) << 16);
			insn.Next();
		}
	}
	return value;
}

bool isArithmeticShift(const InsnCursor& insn, unsigned amount)
{
	if (!isUnconditional(*insn.Current()) || insn.Current()->id != ARM_INS_ASR)
		return false;
	if (insn.op(1).type != ARM_OP_REG)
		return false;
	// Capstone 5 represents the immediate shift on the source operand; some
	// decoders expose a separate immediate. Both describe the same A32 shift.
	if (insn.detail().op_count == 2)
		return insn.op(1).shift.type == ARM_SFT_ASR && insn.op(1).shift.value == amount;
	return insn.detail().op_count == 3 && isImm(insn.op(2), amount);
}

// SDK Push/Pop use STR pre-index / LDR post-index for one register; PushList
// uses STMDB/LDM. Capstone does not give these encodings the same aliases.
Reg singleStackRegister(const cs_insn& instruction, bool load)
{
	if (!isUnconditional(instruction))
		return {};
	const auto& arm = instruction.detail->arm;
	if (instruction.id == (load ? ARM_INS_POP : ARM_INS_PUSH) && arm.op_count == 1 &&
		arm.operands[0].type == ARM_OP_REG)
		return Reg{static_cast<arm_reg>(arm.operands[0].reg)};
	if (instruction.id != (load ? ARM_INS_LDR : ARM_INS_STR) || !arm.writeback)
		return {};
	if (arm.op_count != (load ? 3 : 2) || arm.post_index != load)
		return {};
	if (arm.operands[0].type != ARM_OP_REG || !isMemory(arm.operands[1], CSREG_DART_SP))
		return {};
	if (arm.operands[1].mem.disp != (load ? 0 : -dart::kWordSize))
		return {};
	if (load && !isImm(arm.operands[2], dart::kWordSize))
		return {};
	return Reg{static_cast<arm_reg>(arm.operands[0].reg)};
}

std::vector<CpuRegister> stackRegisters(const cs_insn& insn, bool load)
{
	if (!isUnconditional(insn))
		return {};
	if (auto reg = singleStackRegister(insn, load); reg.IsSet()) {
		if (reg.IsDecimal() || reg == Reg{dart::SPREG} || reg == Reg{dart::FPREG} || reg == Reg{dart::PC})
			return {};
		return {reg};
	}
	const auto& arm = insn.detail->arm;
	unsigned first = 0;
	if (insn.id != (load ? ARM_INS_POP : ARM_INS_PUSH)) {
		if (insn.id != (load ? ARM_INS_LDM : ARM_INS_STMDB) || !arm.writeback)
			return {};
		if (arm.op_count < 2 || !isReg(arm.operands[0], CSREG_DART_SP))
			return {};
		first = 1;
	}
	std::vector<CpuRegister> regs;
	for (unsigned j = first; j < arm.op_count; ++j) {
		if (arm.operands[j].type != ARM_OP_REG)
			return {};
		Reg reg{static_cast<arm_reg>(arm.operands[j].reg)};
		if (!reg.IsSet() || reg.IsDecimal() || reg == Reg{dart::SPREG})
			return {};
		if (reg == Reg{dart::FPREG} || reg == Reg{dart::PC})
			return {};
		regs.push_back(reg);
	}
	return regs;
}

struct MemoryAccess {
	Reg value;
	arm_reg base;
	int32_t offset;
	uint8_t size;
	bool load;
};
std::optional<MemoryAccess> readMemory(const InsnCursor& insn, bool indexed = false)
{
	if (insn.detail().writeback || insn.detail().op_count != 2 || !isUnconditional(*insn.Current()))
		return std::nullopt;
	if (insn.op(0).type != ARM_OP_REG || insn.op(1).type != ARM_OP_MEM)
		return std::nullopt;
	if (!isMemory(insn.op(1), insn.op(1).mem.base)) {
		if (!indexed || insn.op(1).mem.index == ARM_REG_INVALID || insn.op(1).subtracted ||
			insn.op(1).mem.scale != 1)
			return std::nullopt;
	}
	uint8_t size = 0;
	bool load = false;
	switch (insn.Current()->id) {
	case ARM_INS_LDR:
		size = 4;
		load = true;
		break;
	case ARM_INS_STR:
		size = 4;
		break;
	case ARM_INS_LDRB:
	case ARM_INS_LDRSB:
		size = 1;
		load = true;
		break;
	case ARM_INS_STRB:
		size = 1;
		break;
	case ARM_INS_LDRH:
	case ARM_INS_LDRSH:
		size = 2;
		load = true;
		break;
	case ARM_INS_STRH:
		size = 2;
		break;
	case ARM_INS_VLDR:
	case ARM_INS_VSTR:
		size = insn.op(0).reg >= ARM_REG_D0 && insn.op(0).reg <= ARM_REG_D31 ? 8 : 4;
		load = insn.Current()->id == ARM_INS_VLDR;
		break;
	default:
		return std::nullopt;
	}
	Reg value{static_cast<arm_reg>(insn.op(0).reg)};
	if (!value.IsSet() || value == Reg{dart::PC})
		return std::nullopt;
	return MemoryAccess{value, static_cast<arm_reg>(insn.op(1).mem.base), insn.op(1).mem.disp, size, load};
}

class FunctionAnalyzer
{
	DartApp& app;
	AnalyzedFnData& data;
	AsmInstructions& instructions;
	std::unordered_set<uint64_t> targets;
	std::array<DartClass*, Reg::kNumberOfRegisters> objects{};
	std::array<bool, Reg::kNumberOfRegisters> nonObjects{};
	std::array<std::optional<int64_t>, Reg::kNumberOfRegisters> fieldTables{};
	struct SavedFpu {
		uint64_t end;
		std::vector<CpuRegister> regs;
	};
	std::unordered_map<uint64_t, SavedFpu> fpuRestores;

	std::unique_ptr<ILInstr> processEnterFrameInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processLeaveFrameInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processAllocateStackInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processCheckStackOverflowInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processObjectPoolInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processCallInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processPoolCallInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processTailCallInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processReturnInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processMoveRegInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processLoadValueInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> poolLoad(InsnCursor& insn, int64_t displacement, Reg dst, bool store = false);
	std::unique_ptr<ILInstr> processPoolAccess(InsnCursor& insn, bool store);
	void emit(std::unique_ptr<ILInstr> il, size_t start, size_t end);
	using Matcher = std::unique_ptr<ILInstr> (FunctionAnalyzer::*)(InsnCursor&);
	static const Matcher matchers[];

  public:
	FunctionAnalyzer(DartApp& app, DartFunction& function, AsmInstructions& instructions)
		: app(app), data(*function.GetAnalyzedData()), instructions(instructions)
	{
	}
	void asm2il();
};

std::unique_ptr<ILInstr> FunctionAnalyzer::processEnterFrameInstr(InsnCursor& insn)
{
	// EnterDartFrame -> EnterFrame: push {fp, lr}; mov/add fp, sp, #0.
	if (!insn.Is(ARM_INS_PUSH, 2))
		return nullptr;
	if (!isReg(insn.op(0), CSREG_DART_FP) || !isReg(insn.op(1), ARM_REG_LR))
		return nullptr;
	if (!insn.Next())
		return nullptr;
	bool setFrame = insn.Is(ARM_INS_MOV, 2) && isReg(insn.op(1), CSREG_DART_SP);
	if (insn.Is(ARM_INS_ADD, 3))
		setFrame = isReg(insn.op(1), CSREG_DART_SP) && isImm(insn.op(2), 0);
	if (!setFrame || !isReg(insn.op(0), CSREG_DART_FP))
		return nullptr;
	data.useFramePointer = true;
	return std::make_unique<EnterFrameInstr>(insn.Range());
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processLeaveFrameInstr(InsnCursor& insn)
{
	// LeaveDartFrame: sub sp, fp, #0; pop {fp, lr}. The return is separate.
	bool restore = insn.Is(ARM_INS_MOV, 2) && isReg(insn.op(1), CSREG_DART_FP);
	if (insn.Is(ARM_INS_SUB, 3))
		restore = isReg(insn.op(1), CSREG_DART_FP) && isImm(insn.op(2), 0);
	if (!restore || !isReg(insn.op(0), CSREG_DART_SP))
		return nullptr;
	auto pop = insn;
	if (!pop.Next() || !pop.Is(ARM_INS_POP, 2) || !isReg(pop.op(0), CSREG_DART_FP))
		return nullptr;
	if (isReg(pop.op(1), ARM_REG_LR))
		insn.Next();
	else if (!isReg(pop.op(1), ARM_REG_PC))
		return nullptr;
	// With POP {fp, pc}, leave-frame and return share the restore instruction.
	// Keep POP as Return IL, instead of silently losing the return operation.
	return std::make_unique<LeaveFrameInstr>(insn.Range());
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processAllocateStackInstr(InsnCursor& insn)
{
	if (!insn.Is(ARM_INS_SUB, 3))
		return nullptr;
	if (!isReg(insn.op(0), CSREG_DART_SP) || !isReg(insn.op(1), CSREG_DART_SP))
		return nullptr;
	if (insn.op(2).type != ARM_OP_IMM || insn.op(2).imm <= 0 || insn.op(2).imm % 4)
		return nullptr;
	const auto size = insn.op(2).imm;
	if (data.useFramePointer && !data.stackSize)
		data.stackSize = size;
	return std::make_unique<AllocateStackInstr>(insn.Range(), size);
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processCheckStackOverflowInstr(InsnCursor& insn)
{
	// CheckStackOverflowInstr::EmitNativeCode: ldr limit; cmp sp, limit; bls.
	const auto load = readMemory(insn);
	if (!load || !load->load || load->size != 4 || load->base != CSREG_DART_THR)
		return nullptr;
	if (load->offset != AOT_Thread_stack_limit_offset)
		return nullptr;
	const auto limit = insn.op(0).reg;
	if (!insn.Next() || !insn.Is(ARM_INS_CMP, 2))
		return nullptr;
	if (!isReg(insn.op(0), CSREG_DART_SP) || !isReg(insn.op(1), limit))
		return nullptr;
	if (!insn.Next() || (!insn.Is(ARM_INS_B, 1, ARM_CC_LS) && !insn.Is(ARM_INS_BL, 1, ARM_CC_LS)) ||
		insn.op(0).type != ARM_OP_IMM)
		return nullptr;
	data.firstCheckStackOverflowAddr = insn.Range().start;
	return std::make_unique<CheckStackOverflowInstr>(insn.Range(), uint32_t(insn.op(0).imm));
}

std::unique_ptr<ILInstr> FunctionAnalyzer::poolLoad(
	InsnCursor& insn, int64_t displacement, Reg dst, bool store)
{
	// PP is tagged on ARM. Validate index before asking the VM for a pool object.
	const auto offset = displacement + dart::kHeapObjectTag;
	const auto first = dart::ObjectPool::element_offset(0);
	if (offset < first || (offset - first) % dart::kWordSize)
		return nullptr;
	const auto index = (offset - first) / dart::kWordSize;
	if (index >= app.GetObjectPool().Length())
		return nullptr;
	auto& text = data.asmTexts.AtAddr(insn.Current()->address);
	text.dataType = AsmText::PoolOffset;
	text.poolOffset = offset;
	if (dst.IsDecimal()) {
		const auto& pool = app.GetObjectPool();
		if (pool.TypeAt(index) != dart::ObjectPool::EntryType::kImmediate)
			return nullptr;
		uint64_t bits = uint32_t(pool.RawValueAt(index));
		double value;
		if (dst < Reg{Reg::S0}) {
			if (index + 1 >= pool.Length() ||
				pool.TypeAt(index + 1) != dart::ObjectPool::EntryType::kImmediate)
				return nullptr;
			bits |= uint64_t(uint32_t(pool.RawValueAt(index + 1))) << 32;
			std::memcpy(&value, &bits, sizeof(value));
		} else {
			const uint32_t raw = bits;
			float single;
			std::memcpy(&single, &raw, sizeof(single));
			value = single;
		}
		return std::make_unique<LoadValueInstr>(insn.Range(),
			dst,
			VarItem{VarStorage::NewPool(offset), new VarDouble(value, VarValue::NativeDouble)});
	}
	if (store)
		return std::make_unique<StoreObjectPoolInstr>(insn.Range(), dst, offset);
	return std::make_unique<LoadValueInstr>(
		insn.Range(), dst, VarItem{VarStorage::NewPool(offset), getPoolObject(app, offset, dst)});
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processObjectPoolInstr(InsnCursor& insn)
{
	return processPoolAccess(insn, false);
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processPoolAccess(InsnCursor& insn, bool store)
{
	// LoadWordFromPoolIndex: ldr [pp, lo], or add dst, pp, hi; ldr [dst, lo].
	int64_t high = 0;
	arm_reg base = CSREG_DART_PP;
	if (insn.Is(ARM_INS_ADD, 3) && isReg(insn.op(1), CSREG_DART_PP) && insn.op(2).type == ARM_OP_IMM) {
		base = static_cast<arm_reg>(insn.op(0).reg);
		high = insn.op(2).imm;
		if (!insn.Next())
			return nullptr;
	} else if ((!insn.Is(store ? ARM_INS_STR : ARM_INS_LDR, 2) && (store || !insn.Is(ARM_INS_VLDR, 2)))) {
		arm_reg constant;
		auto value = readImmediate(insn, constant);
		if (!value || !insn.Next() || !insn.Is(ARM_INS_ADD, 3))
			return nullptr;
		if (!isReg(insn.op(0), constant) || !isReg(insn.op(1), CSREG_DART_PP) || !isReg(insn.op(2), constant))
			return nullptr;
		high = *value;
		base = constant;
		if (!insn.Next())
			return nullptr;
	}
	const auto memory = readMemory(insn);
	if (!memory || memory->load == store || memory->base != base || (memory->size != 4 && memory->size != 8))
		return nullptr;
	if ((store && (memory->size != 4 || memory->value.IsDecimal())) ||
		(memory->size == 8 && !memory->value.IsDecimal()))
		return nullptr;
	// The address temporary must not overwrite the value being stored.
	if (store && (memory->value == Reg{dart::PP} || (base != CSREG_DART_PP && memory->value == Reg{base})))
		return nullptr;
	return poolLoad(insn, high + memory->offset, memory->value, store);
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processCallInstr(InsnCursor& insn)
{
	if (insn.Is(ARM_INS_BL, 1) && insn.op(0).type == ARM_OP_IMM) {
		const auto address = uint32_t(insn.op(0).imm);
		return std::make_unique<CallInstr>(insn.Range(), app.GetFunction(address), address);
	}
	return nullptr;
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processPoolCallInstr(InsnCursor& insn)
{
	// EmitInstanceCallAOT: LoadWordFromPoolIndex(LR, target), optionally
	// LoadWordFromPoolIndex(R9, call_data), then BLX LR.
	auto call = insn;
	auto value = processObjectPoolInstr(call);
	if (!value)
		return nullptr;
	const auto& load = static_cast<LoadValueInstr&>(*value);
	uint32_t address;
	if (load.dstReg == Reg{dart::CODE_REG}) {
		// EmitCallToStub's non-PC-relative form loads a Code object, then its
		// normal entry field. Check the pool object itself, not VarValue's
		// shared Function/Code display category.
		const auto& pool = app.GetObjectPool();
		const auto index = PoolIndexFromOffset(load.val.storage.offset);
		if (pool.TypeAt(index) != dart::ObjectPool::EntryType::kTaggedObject)
			return nullptr;
		const auto& object = dart::Object::Handle(pool.ObjectAt(index));
		if (!object.IsCode() || !call.Next())
			return nullptr;
		const auto memory = readMemory(call);
		if (!memory || !memory->load || memory->size != dart::kWordSize ||
			memory->base != ToCapstoneReg(dart::CODE_REG) || memory->value != Reg{dart::R14})
			return nullptr;
		if (memory->offset !=
			AOT_Code_entry_point_offset[int(dart::CodeEntryKind::kNormal)] - dart::kHeapObjectTag)
			return nullptr;
		address = uint32_t(dart::Code::Cast(object).EntryPoint() - uintptr_t(app.base()));
	} else {
		if (load.dstReg != Reg{dart::R14} || load.val.Value()->RawTypeId() != dart::kIntegerCid)
			return nullptr;
		const auto absolute = uint32_t(load.val.Value()->AsInteger()->val);
		address = uint32_t(absolute - uintptr_t(app.base()));
	}
	auto* function = app.FindFunctionExact(address);
	if (!function || !call.Next())
		return nullptr;

	if (!call.Is(ARM_INS_BLX, 1)) {
		auto callData = processObjectPoolInstr(call);
		if (!callData)
			return nullptr;
		if (static_cast<LoadValueInstr&>(*callData).dstReg != Reg{dart::R9})
			return nullptr;
		if (!call.Next())
			return nullptr;
	}
	if (!call.Is(ARM_INS_BLX, 1) || !isReg(call.op(0), ARM_REG_LR))
		return nullptr;

	while (insn.End() < call.End())
		insn.Next();
	return std::make_unique<CallInstr>(insn.Range(), function, address);
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processReturnInstr(InsnCursor& insn)
{
	const bool linkReturn = insn.Is(ARM_INS_BX, 1) && isReg(insn.op(0), ARM_REG_LR);
	const bool frameReturn =
		insn.Is(ARM_INS_POP, 2) && isReg(insn.op(0), CSREG_DART_FP) && isReg(insn.op(1), ARM_REG_PC);
	if (!linkReturn && !frameReturn)
		return nullptr;
	return std::make_unique<ReturnInstr>(insn.Range());
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processMoveRegInstr(InsnCursor& insn)
{
	if (!insn.Is(ARM_INS_MOV, 2) || insn.detail().update_flags)
		return nullptr;
	if (insn.op(0).type != ARM_OP_REG || insn.op(1).type != ARM_OP_REG)
		return nullptr;
	if (insn.op(1).shift.type != ARM_SFT_INVALID)
		return nullptr;
	Reg dst{static_cast<arm_reg>(insn.op(0).reg)}, src{static_cast<arm_reg>(insn.op(1).reg)};
	if (!dst.IsSet() || !src.IsSet() || dst == Reg{dart::PC})
		return nullptr;
	return std::make_unique<MoveRegInstr>(insn.Range(), dst, src);
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processLoadValueInstr(InsnCursor& insn)
{
	// LoadSImmediate / LoadDImmediate can use VFP's immediate encoding. The
	// decoder supplies the expanded IEEE value; ordinary register VMOVs and
	// predicated constants must not turn into unconditional values.
	if ((insn.Is(ARM_INS_VMOV, 2) || insn.Is(ARM_INS_FCONSTD, 2) || insn.Is(ARM_INS_FCONSTS, 2)) &&
		insn.op(0).type == ARM_OP_REG && insn.op(1).type == ARM_OP_FP) {
		Reg dst{static_cast<arm_reg>(insn.op(0).reg)};
		if (dst.IsSet() && dst.IsDecimal())
			return std::make_unique<LoadValueInstr>(insn.Range(),
				dst,
				VarItem{VarStorage::NewImmediate(), new VarDouble(insn.op(1).fp, VarValue::NativeDouble)});
	}

	const auto memory = readMemory(insn);
	if (memory && memory->load && memory->size == 4 && memory->base == CSREG_DART_THR) {
		VarValue* value = nullptr;
		if (memory->offset == dart::Thread::object_null_offset())
			value = new VarNull();
		else if (memory->offset == dart::Thread::bool_true_offset())
			value = new VarBoolean(true);
		else if (memory->offset == dart::Thread::bool_false_offset())
			value = new VarBoolean(false);
		if (value)
			return std::make_unique<LoadValueInstr>(
				insn.Range(), memory->value, VarItem{VarStorage::NewThread(memory->offset), value});
	}
	arm_reg dst;
	const auto value = readImmediate(insn, dst);
	if (!value || dst == ARM_REG_PC)
		return nullptr;
	return std::make_unique<LoadValueInstr>(insn.Range(),
		Reg{dst},
		VarItem{VarStorage::NewImmediate(), new VarInteger(int32_t(*value), VarValue::NativeInt)});
}

// Folds which include a preceding pool load must not erase a branch entry.

std::unique_ptr<ILInstr> FunctionAnalyzer::processTailCallInstr(InsnCursor& insn)
{
	if (!insn.Is(ARM_INS_B, 1) || insn.op(0).type != ARM_OP_IMM)
		return nullptr;
	const auto address = uint32_t(insn.op(0).imm);
	if (address >= instructions.FirstPtr()->address && address < instructions.LastPtr()->address + 4)
		return nullptr;
	auto* target = app.FindFunctionExact(address);
	if (!target)
		return nullptr;
	return std::make_unique<CallInstr>(insn.Range(), target, address);
}

// PrologueBuilder produces descriptor arithmetic, followed by supplied/default
// diamonds. Track only those expressions; do not interpret arbitrary body code.

const FunctionAnalyzer::Matcher FunctionAnalyzer::matchers[] = {
	&FunctionAnalyzer::processEnterFrameInstr,
	&FunctionAnalyzer::processLeaveFrameInstr,
	&FunctionAnalyzer::processAllocateStackInstr,
	&FunctionAnalyzer::processCheckStackOverflowInstr,
	&FunctionAnalyzer::processTailCallInstr,
	&FunctionAnalyzer::processPoolCallInstr,
	&FunctionAnalyzer::processCallInstr,
	&FunctionAnalyzer::processObjectPoolInstr,
	&FunctionAnalyzer::processReturnInstr,
	&FunctionAnalyzer::processMoveRegInstr,
	&FunctionAnalyzer::processLoadValueInstr,
};

void FunctionAnalyzer::emit(std::unique_ptr<ILInstr> il, size_t start, size_t end)
{
	DartClass* movedObject = nullptr;
	bool movedNative = false;
	if (il->Kind() == ILInstr::MoveReg) {
		const auto& move = static_cast<MoveRegInstr&>(*il);
		movedObject = objects[move.srcReg];
		movedNative = nonObjects[move.srcReg];
	}
	for (size_t i = start; i < end; ++i) {
		const auto& instruction = *instructions.Ptr(i);
		const auto& arm = instruction.detail->arm;
		Reg tableDestination;
		std::optional<int64_t> tableValue;
		InsnCursor cursor{instructions, targets, i};
		const auto memory = readMemory(cursor);
		if (memory && memory->load && memory->size == dart::kWordSize && memory->base == CSREG_DART_THR &&
			memory->offset == AOT_Thread_field_table_values_offset) {
			tableDestination = memory->value;
			tableValue = 0;
		} else if (cursor.Is(ARM_INS_MOV, 2) || cursor.Is(ARM_INS_ADD, 3)) {
			const Reg source{static_cast<arm_reg>(cursor.op(1).reg)};
			if (cursor.op(0).type == ARM_OP_REG && cursor.op(1).type == ARM_OP_REG && source.IsSet() &&
				fieldTables[source] && !arm.update_flags) {
				tableDestination = Reg{static_cast<arm_reg>(cursor.op(0).reg)};
				if (cursor.Is(ARM_INS_MOV, 2) && cursor.op(1).shift.type == ARM_SFT_INVALID)
					tableValue = fieldTables[source];
				else if (cursor.Is(ARM_INS_ADD, 3) && cursor.op(2).type == ARM_OP_IMM)
					tableValue = *fieldTables[source] + cursor.op(2).imm;
			}
		}
		for (unsigned j = 0; j < arm.op_count; ++j) {
			const auto& op = arm.operands[j];
			if (op.type != ARM_OP_REG || !(op.access & CS_AC_WRITE))
				continue;
			Reg reg{static_cast<arm_reg>(op.reg)};
			if (!reg.IsSet())
				continue;
			objects[reg] = nullptr;
			fieldTables[reg].reset();
			// Arithmetic destinations are native values/derived addresses, unless
			// a successful recognizer below establishes an object result.
			switch (instruction.id) {
			case ARM_INS_ADD:
			case ARM_INS_SUB:
			case ARM_INS_AND:
			case ARM_INS_ORR:
			case ARM_INS_EOR:
			case ARM_INS_ASR:
			case ARM_INS_LSR:
			case ARM_INS_LSL:
				nonObjects[reg] = true;
				break;
			default:
				nonObjects[reg] = false;
			}
		}
		if (tableDestination.IsSet())
			fieldTables[tableDestination] = tableValue;
		if (tableDestination.IsSet() && tableValue)
			nonObjects[tableDestination] = true;
		const auto* groups = instruction.detail->groups;
		const bool transfer =
			std::any_of(groups, groups + instruction.detail->groups_count, [](uint8_t group) {
				return group == CS_GRP_JUMP || group == CS_GRP_CALL || group == CS_GRP_RET;
			});
		if (transfer || il->Kind() == ILInstr::Return) {
			objects.fill(nullptr);
			fieldTables.fill(std::nullopt);
			nonObjects.fill(false);
		}
	}
	if (il->Kind() == ILInstr::MoveReg) {
		const auto& move = static_cast<MoveRegInstr&>(*il);
		objects[move.dstReg] = movedObject;
		nonObjects[move.dstReg] = movedNative;
	} else if (il->Kind() == ILInstr::LoadValue) {
		auto& value = static_cast<LoadValueInstr&>(*il);
		auto cid = value.val.Value()->TypeId();
		if (value.val.storage.kind == VarStorage::Pool) {
			const auto index = PoolIndexFromOffset(value.val.storage.offset);
			const auto& pool = app.GetObjectPool();
			if (pool.TypeAt(index) == dart::ObjectPool::EntryType::kTaggedObject) {
				const auto object = pool.ObjectAt(index);
				cid = object.IsHeapObject() ? dart::Object::Handle(object).GetClassId() : dart::kSmiCid;
			}
		}
		if (cid > 0)
			objects[value.dstReg] = app.FindClass(cid);
		nonObjects[value.dstReg] =
			value.val.Value()->RawTypeId() == dart::kIntegerCid &&
			(value.val.Value()->AsInteger()->intTypeId == VarValue::NativeInt || cid == dart::kSmiCid);
	} else if (il->Kind() == ILInstr::WriteBarrier) {
		const auto& barrier = static_cast<WriteBarrierInstr&>(*il);
		if (barrier.isArray) {
			// ArrayStoreBarrier preserves its object argument. Carry its proven
			// layout forward until a write/control-flow entry invalidates it.
			objects[barrier.objReg] = app.FindClass(dart::kArrayCid);
			nonObjects[barrier.objReg] = false;
		}
	} else if (il->Kind() == ILInstr::LoadArrayElement) {
		const auto& load = static_cast<LoadArrayElementInstr&>(*il);
		if (load.arrayOp.arrType != ArrayOp::List && load.arrayOp.arrType != ArrayOp::Unknown)
			nonObjects[load.dstReg] = true;
	} else if (il->Kind() == ILInstr::UnboxInt) {
		const auto& unbox = static_cast<UnboxIntInstr&>(*il);
		nonObjects[unbox.dstReg] = true;
	} else if (il->Kind() == ILInstr::Call) {
		auto* fn = static_cast<CallInstr&>(*il).GetFunction();
		if (fn && fn->ReturnType() != dart::kIllegalCid)
			objects[Reg{dart::CallingConventions::kReturnReg}] = app.FindClass(fn->ReturnType());
	} else if (il->Kind() == ILInstr::BoxInt64) {
		const auto reg = static_cast<BoxInt64Instr&>(*il).objReg;
		objects[reg] = nullptr;
		nonObjects[reg] = false;
	} else if (il->Kind() == ILInstr::LoadTaggedClassIdMayBeSmi) {
		nonObjects[static_cast<LoadTaggedClassIdMayBeSmiInstr&>(*il).taggedCidReg] = true;
	} else if (il->Kind() == ILInstr::AllocateObject) {
		const auto& allocation = static_cast<AllocateObjectInstr&>(*il);
		objects[allocation.dstReg] = &allocation.dartCls;
		nonObjects[allocation.dstReg] = false;
	} else if (il->Kind() == ILInstr::LoadClassId) {
		nonObjects[static_cast<LoadClassIdInstr&>(*il).cidReg] = true;
	}
	data.AddIL(std::move(il));
}

void FunctionAnalyzer::asm2il()
{
	for (size_t i = 0; i < instructions.Count(); ++i) {
		const auto& insn = *instructions.Ptr(i);
		const auto& arm = insn.detail->arm;
		if ((insn.id == ARM_INS_B || insn.id == ARM_INS_BL) && arm.op_count == 1 &&
			arm.operands[0].type == ARM_OP_IMM)
			targets.insert(uint32_t(arm.operands[0].imm));
	}
	for (size_t i = 0; i < instructions.Count();) {
		if (targets.contains(instructions.Ptr(i)->address)) {
			objects.fill(nullptr);
			fieldTables.fill(std::nullopt);
			nonObjects.fill(false);
		}
		std::unique_ptr<ILInstr> il;
		size_t end = i + 1;
		for (auto matcher : matchers) {
			InsnCursor candidate{instructions, targets, i};
			il = (this->*matcher)(candidate);
			if (il) {
				end = candidate.End();
				break;
			}
		}
		if (!il)
			il = std::make_unique<UnknownInstr>(
				instructions.Ptr(i), data.asmTexts.AtAddr(instructions.Ptr(i)->address));
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
		const auto& insn = *instructions.Ptr(i);
		auto& text = texts[i];
		text.addr = insn.address;
		std::snprintf(text.text, sizeof(text.text), "%-16s%s", insn.mnemonic, insn.op_str);
		const auto& arm = insn.detail->arm;
		for (unsigned j = 0; j < arm.op_count; ++j) {
			const auto& op = arm.operands[j];
			if (isMemory(op, CSREG_DART_THR) && op.mem.disp >= 0) {
				text.dataType = AsmText::ThreadOffset;
				text.threadOffset = op.mem.disp;
				if (!stackLimit && op.mem.disp == AOT_Thread_stack_limit_offset)
					stackLimit = insn.address;
			}
			if (isMemory(op, CSREG_DART_FP) && op.mem.disp >= 8 && op.mem.disp < 0x10000)
				maxParamOffset = std::max(maxParamOffset, op.mem.disp);
		}
		if (insn.id == ARM_INS_BL && arm.op_count == 1 && arm.operands[0].type == ARM_OP_IMM) {
			text.dataType = AsmText::Call;
			text.callAddress = uint32_t(arm.operands[0].imm);
		}
	}
	return AsmTexts{std::move(texts), stackLimit, maxParamOffset};
}

void CodeAnalyzer::asm2il(DartFunction* dartFn, AsmInstructions& instructions)
{
	FunctionAnalyzer{app, *dartFn, instructions}.asm2il();
}
#endif
