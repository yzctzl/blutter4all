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

class ArmParameterRecovery;

class FunctionAnalyzer
{
	friend class ArmParameterRecovery;
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
	std::unique_ptr<ILInstr> processLoadClassIdInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processBranchIfSmiInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processLoadFieldTableInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processCallInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processPoolCallInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processCallLeafRuntimeInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processGdtCallInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processClosureCallInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processUnboxIntInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processInitAsyncInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processInitLateStaticFieldInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processTypeTestInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processInlineTypeTestInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processTryAllocateObjectInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processWriteBarrierInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processTailCallInstr(InsnCursor& insn);
	LoadValueInstr* previousLoad(const InsnCursor& insn);
	std::unique_ptr<ILInstr> processBoxInt64Instr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processTaggedClassIdInstr(InsnCursor& insn);
	void recoverParameters();
	void processPrologueParameters();
	void processSavedRegisters();
	std::unique_ptr<ILInstr> processSaveRegisterInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processLoadSavedRegisterInstr(InsnCursor& insn);
	void recoverIncomingParameters();
	void recoverRegisterParameters();
	std::unique_ptr<ILInstr> processReturnInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processMoveRegInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processLoadValueInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processLoadStore(InsnCursor& insn);
	std::unique_ptr<ILInstr> poolLoad(InsnCursor& insn, int64_t displacement, Reg dst, bool store = false);
	std::unique_ptr<ILInstr> processPoolAccess(InsnCursor& insn, bool store);
	std::unique_ptr<ILInstr> processStorePoolInstr(InsnCursor& insn);
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

std::unique_ptr<ILInstr> FunctionAnalyzer::processStorePoolInstr(InsnCursor& insn)
{
	return processPoolAccess(insn, true);
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

std::unique_ptr<ILInstr> FunctionAnalyzer::processLoadClassIdInstr(InsnCursor& insn)
{
	// assembler_arm.cc LoadClassId / LoadClassIdMayBeSmi. UBFX extracts the
	// 20-bit CID at bit 12; this is not ARM64's shift-only tags encoding.
	bool mayBeSmi = insn.Is(ARM_INS_TST, 2) && isImm(insn.op(1), dart::kSmiTagMask);
	arm_reg object = ARM_REG_INVALID;
	arm_cc cc = ARM_CC_AL;
	if (mayBeSmi) {
		object = static_cast<arm_reg>(insn.op(0).reg);
		cc = ARM_CC_NE;
		if (!insn.Next())
			return nullptr;
	}
	if (!insn.Is(ARM_INS_LDR, 2, cc) || insn.detail().writeback)
		return nullptr;
	if (!isMemory(insn.op(1), insn.op(1).mem.base) || insn.op(1).mem.disp != -dart::kHeapObjectTag)
		return nullptr;
	if (mayBeSmi && insn.op(1).mem.base != object)
		return nullptr;
	object = static_cast<arm_reg>(insn.op(1).mem.base);
	const auto cid = insn.op(0).reg;
	if (!insn.Next() || !insn.Is(ARM_INS_UBFX, 4, cc))
		return nullptr;
	if (!isReg(insn.op(0), cid) || !isReg(insn.op(1), cid))
		return nullptr;
	if (!isImm(insn.op(2), kUntaggedObjectClassIdTagPos) ||
		!isImm(insn.op(3), dart::UntaggedObject::kClassIdTagSize))
		return nullptr;
	if (mayBeSmi) {
		if (!insn.Next() || !insn.Is(ARM_INS_MOV, 2, ARM_CC_EQ))
			return nullptr;
		if (!isReg(insn.op(0), cid) || !isImm(insn.op(1), dart::kSmiCid))
			return nullptr;
	}
	return std::make_unique<LoadClassIdInstr>(
		insn.Range(), Reg{object}, Reg{static_cast<arm_reg>(cid)}, mayBeSmi);
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processBranchIfSmiInstr(InsnCursor& insn)
{
	if (!insn.Is(ARM_INS_TST, 2) || insn.op(0).type != ARM_OP_REG || !isImm(insn.op(1), dart::kSmiTagMask))
		return nullptr;
	const auto object = static_cast<arm_reg>(insn.op(0).reg);
	if (!insn.Next() || !insn.Is(ARM_INS_B, 1, ARM_CC_EQ) || insn.op(0).type != ARM_OP_IMM)
		return nullptr;
	return std::make_unique<BranchIfSmiInstr>(insn.Range(), Reg{object}, uint32_t(insn.op(0).imm));
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processLoadFieldTableInstr(InsnCursor& insn)
{
	// il_arm.cc LoadStaticField / StoreStaticField: thread's field table, then
	// a native word offset. Do not confuse it with a tagged heap field access.
	auto table = readMemory(insn);
	if (table && table->size == dart::kWordSize) {
		Reg base{table->base};
		if (base.IsSet() && fieldTables[base]) {
			const auto offset = *fieldTables[base] + table->offset;
			if (offset < 0 || offset > UINT32_MAX || offset % dart::kWordSize)
				return nullptr;
			if (table->load)
				return std::make_unique<LoadStaticFieldInstr>(insn.Range(), table->value, offset);
			return std::make_unique<StoreStaticFieldInstr>(insn.Range(), table->value, offset);
		}
	}
	if (!table || !table->load || table->base != CSREG_DART_THR || table->size != 4)
		return nullptr;
	if (table->offset != AOT_Thread_field_table_values_offset)
		return nullptr;
	auto base = insn.op(0).reg;
	if (!insn.Next())
		return nullptr;
	int64_t high = 0;
	if (insn.Is(ARM_INS_ADD, 3) && isReg(insn.op(1), base) && insn.op(2).type == ARM_OP_IMM) {
		if (insn.op(0).type != ARM_OP_REG || insn.detail().update_flags)
			return nullptr;
		base = insn.op(0).reg;
		high = insn.op(2).imm;
		if (!insn.Next())
			return nullptr;
	}
	auto memory = readMemory(insn);
	if (!memory || memory->base != base || memory->size != 4)
		return nullptr;
	const auto offset = high + memory->offset;
	if (offset < 0 || offset > UINT32_MAX || offset % 4)
		return nullptr;
	if (memory->load)
		return std::make_unique<LoadStaticFieldInstr>(insn.Range(), memory->value, offset);
	return std::make_unique<StoreStaticFieldInstr>(insn.Range(), memory->value, offset);
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

std::unique_ptr<ILInstr> FunctionAnalyzer::processCallLeafRuntimeInstr(InsnCursor& insn)
{
	// Leaf runtime entries are loaded from THR, then called through BLX.
	auto memory = readMemory(insn);
	if (!memory || !memory->load || memory->size != 4 || memory->base != CSREG_DART_THR)
		return nullptr;
	if (!GetThreadLeafFunction(memory->offset))
		return nullptr;
	const auto target = insn.op(0).reg;
	if (!insn.Next())
		return nullptr;
	// LeafRuntimeScope::Call stores the native entry as vm_tag before BLX.
	// The short form has no tag stores; a partial protocol is not accepted.
	const auto tag = readMemory(insn);
	if (tag) {
		if (tag->load || tag->size != dart::kWordSize)
			return nullptr;
		if (tag->base != CSREG_DART_THR || tag->offset != AOT_Thread_vm_tag_offset)
			return nullptr;
		if (tag->value != Reg{static_cast<arm_reg>(target)})
			return nullptr;
		if (!insn.Next())
			return nullptr;
	}
	if (!insn.Is(ARM_INS_BLX, 1) || !isReg(insn.op(0), target))
		return nullptr;
	if (tag) {
		if (!insn.Next())
			return nullptr;
		arm_reg reset;
		const auto dartTag = readImmediate(insn, reset);
		if (!dartTag || *dartTag != dart::VMTag::kDartTagId || reset != target || !insn.Next())
			return nullptr;
		const auto restore = readMemory(insn);
		if (!restore || restore->load || restore->size != dart::kWordSize || restore->base != tag->base ||
			restore->offset != tag->offset)
			return nullptr;
		if (restore->value != tag->value)
			return nullptr;
	}
	return std::make_unique<CallLeafRuntimeInstr>(insn.Range(), memory->offset);
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

std::unique_ptr<ILInstr> FunctionAnalyzer::processLoadStore(InsnCursor& insn)
{
	// ElementAddressForRegIndex and LoadFieldFromOffset both form an address
	// before accessing it. Fold only the proven address expression, with no
	// writeback or intervening branch entry.
	int64_t adjustment = 0;
	arm_reg object = ARM_REG_INVALID, address = ARM_REG_INVALID, index = ARM_REG_INVALID;
	arm_shifter shift = ARM_SFT_INVALID;
	unsigned scale = 0;
	if (insn.Is(ARM_INS_ADD, 3) && insn.op(0).type == ARM_OP_REG && insn.op(1).type == ARM_OP_REG) {
		if (insn.detail().update_flags)
			return nullptr;
		address = static_cast<arm_reg>(insn.op(0).reg);
		object = static_cast<arm_reg>(insn.op(1).reg);
		if (insn.op(2).type == ARM_OP_IMM)
			adjustment = insn.op(2).imm;
		else if (insn.op(2).type == ARM_OP_REG) {
			index = static_cast<arm_reg>(insn.op(2).reg);
			shift = insn.op(2).shift.type;
			scale = insn.op(2).shift.value;
		} else
			return nullptr;
		if (!insn.Next())
			return nullptr;
		// VFP and mode-3 stores cannot encode a tagged data displacement.
		// ElementAddressForRegIndex adds its high part to the temporary first.
		if (insn.Is(ARM_INS_ADD, 3) && isReg(insn.op(0), address) && isReg(insn.op(1), address)) {
			if (insn.op(2).type != ARM_OP_IMM || insn.detail().update_flags)
				return nullptr;
			adjustment += insn.op(2).imm;
			if (!insn.Next())
				return nullptr;
		}
	}
	auto memory = readMemory(insn, true);
	if (!memory)
		return nullptr;
	if (address != ARM_REG_INVALID && memory->base != address)
		return nullptr;
	if (insn.op(1).mem.index != ARM_REG_INVALID) {
		if (index != ARM_REG_INVALID)
			return nullptr;
		index = insn.op(1).mem.index;
		shift = insn.op(1).shift.type;
		scale = insn.op(1).shift.value;
	}
	Reg base{object == ARM_REG_INVALID ? memory->base : object};
	if (!base.IsSet() || base.IsDecimal() || base == Reg{dart::PP} || base == Reg{dart::THR})
		return nullptr;
	if (base == Reg{dart::SPREG} || base == Reg{dart::FPREG} || base == Reg{dart::PC})
		return nullptr;
	if (nonObjects[base])
		return nullptr;
	const int64_t offset = adjustment + memory->offset + dart::kHeapObjectTag;
	if (index != ARM_REG_INVALID) {
		// A word list's tagged index is shifted once. Other element kinds need
		// an exact internal receiver layout; raw/external backing pointers do not
		// establish a Dart array operation.
		const auto* receiver = objects[base];
		ArrayOp::ArrayType arrayType;
		if (receiver && receiver->Id() == dart::kImmutableArrayCid && !memory->load)
			return nullptr;
		if (receiver && dart::IsTypedDataClassId(receiver->Id())) {
			if (offset != dart::Instance::DataOffsetFor(receiver->Id()) ||
				memory->size != dart::TypedDataBase::ElementSizeInBytes(receiver->Id()))
				return nullptr;
			arrayType = ArrayOp::TypedUnknown;
		} else {
			if (receiver && receiver->Id() != dart::kArrayCid && receiver->Id() != dart::kImmutableArrayCid)
				return nullptr;
			if (offset != dart::Array::data_offset())
				return nullptr;
			if (memory->size != dart::kWordSize || memory->value.IsDecimal())
				return nullptr;
			arrayType = ArrayOp::List;
		}

		// A tagged index contributes one bit of scale. A byte element instead
		// needs ASR #1; larger elements use LSL #(log2(size) - tag size).
		const unsigned expected = ArrayOp{memory->size, memory->load, ArrayOp::Unknown}.SizeLog2();
		const bool unboxed = receiver && scale == expected &&
							 (shift == ARM_SFT_LSL || (scale == 0 && shift == ARM_SFT_INVALID));
		if (!unboxed && expected == 0) {
			if (shift != ARM_SFT_ASR || scale != 1)
				return nullptr;
		} else if (!unboxed) {
			if (scale != expected - 1)
				return nullptr;
			if (shift != ARM_SFT_LSL && !(scale == 0 && shift == ARM_SFT_INVALID))
				return nullptr;
		}
		ArrayOp operation{memory->size, memory->load, arrayType};
		operation.inferred = !objects[base];
		operation.indexUnboxed = unboxed;
		if (memory->load)
			return std::make_unique<LoadArrayElementInstr>(
				insn.Range(), memory->value, base, VarStorage{Reg{index}}, operation);
		return std::make_unique<StoreArrayElementInstr>(
			insn.Range(), memory->value, base, VarStorage{Reg{index}}, operation);
	}
	// Constant indices need a receiver layout (or the array barrier below).
	// Do not reinterpret arbitrary small fields as array elements.
	if (const auto* receiver = objects[base]) {
		const bool list = receiver->Id() == dart::kArrayCid || receiver->Id() == dart::kImmutableArrayCid;
		const bool typed = dart::IsTypedDataClassId(receiver->Id());
		if (list || typed) {
			const auto size =
				list ? dart::kWordSize : dart::TypedDataBase::ElementSizeInBytes(receiver->Id());
			const auto payload = offset - dart::Instance::DataOffsetFor(receiver->Id());
			if (payload >= 0 && payload % size == 0 && memory->size == size) {
				if (!memory->load && receiver->Id() == dart::kImmutableArrayCid)
					return nullptr;
				ArrayOp operation{memory->size, memory->load, list ? ArrayOp::List : ArrayOp::TypedUnknown};
				auto element = VarStorage::NewSmallImm(payload / size);
				if (memory->load)
					return std::make_unique<LoadArrayElementInstr>(
						insn.Range(), memory->value, base, element, operation);
				return std::make_unique<StoreArrayElementInstr>(
					insn.Range(), memory->value, base, element, operation);
			}
		}
	}
	// StoreIndexed computes the exact slot in kWriteBarrierSlotReg before
	// ArrayStoreBarrier. The verified barrier establishes the receiver kind;
	// a payload-looking offset by itself does not. Leave the barrier separate.
	if (!memory->load && memory->size == dart::kWordSize && !memory->value.IsDecimal()) {
		const bool slot = address == ToCapstoneReg(dart::kWriteBarrierSlotReg) && memory->offset == 0;
		const auto payload = offset - dart::Array::data_offset();
		if (slot && payload >= 0 && payload % dart::kWordSize == 0) {
			auto next = insn;
			auto barrier = next.Next() ? processWriteBarrierInstr(next) : nullptr;
			if (barrier) {
				const auto& write = static_cast<WriteBarrierInstr&>(*barrier);
				if (write.isArray && write.objReg == base && write.valReg == memory->value) {
					ArrayOp operation{dart::kWordSize, false, ArrayOp::List};
					return std::make_unique<StoreArrayElementInstr>(insn.Range(),
						memory->value,
						base,
						VarStorage::NewSmallImm(payload / dart::kWordSize),
						operation);
				}
			}
		}
	}
	if (offset < dart::kWordSize || offset > UINT32_MAX || offset % dart::kWordSize)
		return nullptr;
	// A tagged-address shape is weaker evidence than a receiver layout. Keep
	// this distinction in the IL, as on x64; byte/raw pointer loads stay unknown.
	if (memory->size != 4 && memory->size != 8)
		return nullptr;
	if (memory->size == 8 && !memory->value.IsDecimal())
		return nullptr;
	if (memory->load) {
		auto il = std::make_unique<LoadFieldInstr>(
			insn.Range(), memory->value, base, offset, FieldAccessEvidence::TaggedAddress);
		il->accessSize = memory->size;
		return il;
	}
	auto il = std::make_unique<StoreFieldInstr>(
		insn.Range(), memory->value, base, offset, FieldAccessEvidence::TaggedAddress);
	il->accessSize = memory->size;
	return il;
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processGdtCallInstr(InsnCursor& insn)
{
	// FlowGraphCompiler::EmitDispatchTableCall: CID scaled by target word size,
	// an optional selector displacement, then load LR and BLX LR.
	const auto table = ToCapstoneReg(dart::DISPATCH_TABLE_REG);
	const auto cid = ToCapstoneReg(dart::DispatchTableNullErrorABI::kClassIdReg);
	const auto scaledCid = [&](const cs_arm_op& op) {
		return op.type == ARM_OP_REG && op.reg == cid && op.shift.type == ARM_SFT_LSL && op.shift.value == 2;
	};
	int64_t offset = 0;
	if (insn.Is(ARM_INS_ADD, 3)) {
		if (!isReg(insn.op(0), ARM_REG_LR) || !isReg(insn.op(1), table) || !scaledCid(insn.op(2)))
			return nullptr;
		if (!insn.Next())
			return nullptr;
		if (insn.Is(ARM_INS_ADD, 3) || insn.Is(ARM_INS_SUB, 3)) {
			if (!isReg(insn.op(0), ARM_REG_LR) || !isReg(insn.op(1), ARM_REG_LR) ||
				insn.op(2).type != ARM_OP_IMM)
				return nullptr;
			offset = insn.op(2).imm * (insn.Current()->id == ARM_INS_SUB ? -1 : 1);
			if (!insn.Next())
				return nullptr;
		}
		auto memory = readMemory(insn);
		if (!memory || !memory->load || memory->size != dart::kWordSize || memory->base != ARM_REG_LR ||
			memory->value != Reg{dart::R14})
			return nullptr;
		offset += memory->offset;
	} else {
		if (!insn.Is(ARM_INS_LDR, 2) || insn.detail().writeback || !isReg(insn.op(0), ARM_REG_LR))
			return nullptr;
		const auto& memory = insn.op(1);
		if (memory.type != ARM_OP_MEM || memory.mem.base != table || memory.mem.index != cid ||
			memory.subtracted)
			return nullptr;
		if (memory.shift.type != ARM_SFT_LSL || memory.shift.value != 2)
			return nullptr;
	}
	if (offset % dart::kWordSize || !insn.Next() || !insn.Is(ARM_INS_BLX, 1) ||
		!isReg(insn.op(0), ARM_REG_LR))
		return nullptr;
	return std::make_unique<GdtCallInstr>(insn.Range(), offset / dart::kWordSize);
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processUnboxIntInstr(InsnCursor& insn)
{
	// il_arm.cc EmitLoadInt64FromBoxOrSmi also sign-fills a distinct high
	// register before untagging. Preserve the pair in IL rather than hiding
	// the upper word or confusing the two Mint loads with object fields.
	Reg high;
	arm_reg pairSource = ARM_REG_INVALID;
	if (isArithmeticShift(insn, 31) && !insn.detail().update_flags) {
		if (insn.op(0).type != ARM_OP_REG || insn.op(1).type != ARM_OP_REG)
			return nullptr;
		high = Reg{static_cast<arm_reg>(insn.op(0).reg)};
		pairSource = static_cast<arm_reg>(insn.op(1).reg);
		if (high == Reg{pairSource} || !insn.Next())
			return nullptr;
	}
	// assembler_arm.h LoadInt32FromBoxOrSmi: ASRS exposes the Smi tag in
	// carry; BCC skips exactly one Mint payload load. A bare ASR is ambiguous.
	if (!isArithmeticShift(insn, dart::kSmiTagSize) || !insn.detail().update_flags)
		return nullptr;
	if (insn.op(0).type != ARM_OP_REG || insn.op(1).type != ARM_OP_REG)
		return nullptr;
	const auto dst = static_cast<arm_reg>(insn.op(0).reg), src = static_cast<arm_reg>(insn.op(1).reg);
	if (dst == src || (high.IsSet() && (src != pairSource || high == Reg{dst})))
		return nullptr;
	if (!insn.Next() || !insn.Is(ARM_INS_B, 1, ARM_CC_LO) || insn.op(0).type != ARM_OP_IMM)
		return nullptr;
	const auto done = uint32_t(insn.op(0).imm);
	if (!insn.Next())
		return nullptr;
	const auto memory = readMemory(insn);
	if (!memory || !memory->load || memory->size != 4 || memory->base != src || memory->value != Reg{dst})
		return nullptr;
	if (memory->offset != AOT_Mint_value_offset - dart::kHeapObjectTag)
		return nullptr;
	if (high.IsSet()) {
		if (!insn.Next())
			return nullptr;
		const auto upper = readMemory(insn);
		if (!upper || !upper->load || upper->size != 4 || upper->base != src || upper->value != high)
			return nullptr;
		if (upper->offset != memory->offset + dart::kWordSize)
			return nullptr;
	}
	if (done != insn.Range().end)
		return nullptr;
	return std::make_unique<UnboxIntInstr>(insn.Range(), Reg{dst}, Reg{src}, high.IsSet() ? 64 : 32, high);
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processClosureCallInstr(InsnCursor& insn)
{
	// il_arm.cc ClosureCallInstr: descriptor in r4, cached entry from closure
	// r0 into r2, then BLX r2. The descriptor must be a valid VM array layout.
	if (targets.contains(insn.Current()->address) || data.il_insns.empty())
		return nullptr;
	auto* previous = data.LastIL();
	if (previous->Kind() != ILInstr::LoadValue || previous->End() != insn.Range().start)
		return nullptr;
	auto& descriptorLoad = static_cast<LoadValueInstr&>(*previous);
	if (descriptorLoad.dstReg != Reg{dart::ARGS_DESC_REG} ||
		descriptorLoad.val.ValueTypeId() != dart::kArrayCid)
		return nullptr;
	const auto memory = readMemory(insn);
	if (!memory || !memory->load || memory->size != dart::kWordSize || memory->base != ARM_REG_R0 ||
		memory->value != Reg{dart::R2})
		return nullptr;
	if (memory->offset != AOT_Closure_entry_point_offset - dart::kHeapObjectTag)
		return nullptr;
	if (!insn.Next() || !insn.Is(ARM_INS_BLX, 1) || !isReg(insn.op(0), ARM_REG_R2))
		return nullptr;
	const auto& array = dart::Array::Handle(descriptorLoad.val.Get<VarArray>()->ptr);
	const auto header = (dart::ArgumentsDescriptor::first_named_entry_offset() - dart::Array::data_offset()) /
						dart::kWordSize;
	if (array.Length() <= header || (array.Length() - header - 1) % 2)
		return nullptr;
	for (intptr_t i = 0; i < header; ++i)
		if (!dart::Object::Handle(array.At(i)).IsSmi())
			return nullptr;
	dart::ArgumentsDescriptor descriptor(array);
	if (descriptor.Count() <= 0 || descriptor.TypeArgsLen() < 0)
		return nullptr;
	if (descriptor.PositionalCount() < 0 || descriptor.PositionalCount() > descriptor.Count())
		return nullptr;
	if (descriptor.NamedCount() != (array.Length() - header - 1) / 2)
		return nullptr;
	const auto start = previous->Start();
	data.RemoveLastIL();
	return std::make_unique<ClosureCallInstr>(
		AddrRange{start, insn.Range().end}, descriptor.Count(), descriptor.TypeArgsLen());
}

// Folds which include a preceding pool load must not erase a branch entry.
LoadValueInstr* FunctionAnalyzer::previousLoad(const InsnCursor& insn)
{
	if (targets.contains(insn.Range().start) || data.il_insns.empty())
		return nullptr;
	auto* previous = data.LastIL();
	if (previous->Kind() != ILInstr::LoadValue || previous->End() != insn.Range().start)
		return nullptr;
	return static_cast<LoadValueInstr*>(previous);
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processInitAsyncInstr(InsnCursor& insn)
{
#ifdef HAS_INIT_ASYNC
	// StubCallInstr passes the Future type arguments in r0 on ARM too.
	if (!insn.Is(ARM_INS_BL, 1) || insn.op(0).type != ARM_OP_IMM)
		return nullptr;
	auto* fn = app.FindFunctionExact(uint32_t(insn.op(0).imm));
	if (!fn || !fn->IsStub() || fn->AsStub()->kind != DartStub::InitAsyncStub)
		return nullptr;
	auto* load = previousLoad(insn);
	if (!load || load->dstReg != Reg{dart::R0})
		return nullptr;
	auto& item = load->val;
	DartType* type = nullptr;
	if (item.ValueTypeId() == dart::kNullCid)
		type = app.TypeDb()->FindOrAdd(app.DartFutureCid(), &DartTypeArguments::Null);
	else if (item.ValueTypeId() == dart::kTypeArgumentsCid)
		type = app.TypeDb()->FindOrAdd(app.DartFutureCid(), &item.Get<VarTypeArgument>()->typeArgs);
	if (!type)
		return nullptr;
	const auto start = load->Start();
	data.returnType = type;
	data.RemoveLastIL();
	return std::make_unique<InitAsyncInstr>(AddrRange{start, insn.Range().end}, type);
#else
	return nullptr;
#endif
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processInitLateStaticFieldInstr(InsnCursor& insn)
{
#ifndef NO_INIT_LATE_STATIC_FIELD
	// il.cc LoadStaticField: sentinel test stays separate; only the exact
	// initializer stub and its Field pool argument establish this operation.
	if (!insn.Is(ARM_INS_BL, 1) || insn.op(0).type != ARM_OP_IMM)
		return nullptr;
	auto* fn = app.FindFunctionExact(uint32_t(insn.op(0).imm));
	if (!fn || !fn->IsStub())
		return nullptr;
	const auto kind = fn->AsStub()->kind;
	if (kind != DartStub::InitLateStaticFieldStub && kind != DartStub::InitLateFinalStaticFieldStub)
		return nullptr;
	auto* load = previousLoad(insn);
	if (!load || load->dstReg != Reg{dart::InitStaticFieldABI::kFieldReg})
		return nullptr;
	if (load->val.storage.kind != VarStorage::Pool)
		return nullptr;
	const auto index = PoolIndexFromOffset(load->val.storage.offset);
	const auto& pool = app.GetObjectPool();
	if (pool.TypeAt(index) != dart::ObjectPool::EntryType::kTaggedObject)
		return nullptr;
	const auto& object = dart::Object::Handle(pool.ObjectAt(index));
	if (!object.IsField())
		return nullptr;
	const auto& field = dart::Field::Cast(object);
	auto* info = app.FindStaticField(field.TargetOffset());
	if (!field.is_static() || !info)
		return nullptr;
	const auto start = load->Start();
	data.RemoveLastIL();
	return std::make_unique<InitLateStaticFieldInstr>(
		AddrRange{start, insn.Range().end}, VarStorage{Reg{dart::InitStaticFieldABI::kResultReg}}, *info);
#else
	return nullptr;
#endif
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processInlineTypeTestInstr(InsnCursor& insn)
{
	// GenerateCallerChecksForAssertAssignable: numeric positive fast paths
	// branch around a proven TTS. A CID-looking branch alone is not a cast.
	auto smi = processBranchIfSmiInstr(insn);
	if (!smi)
		return nullptr;
	const auto& branch = static_cast<BranchIfSmiInstr&>(*smi);
	if (branch.objReg != Reg{dart::TypeTestABI::kInstanceReg})
		return nullptr;
	const auto done = branch.branchAddr;
	if (!insn.Next())
		return nullptr;
	int range = 0;
	auto cidCursor = insn;
	if (auto cid = processLoadClassIdInstr(cidCursor)) {
		const auto& load = static_cast<LoadClassIdInstr&>(*cid);
		if (load.objReg != branch.objReg)
			return nullptr;
		while (insn.End() < cidCursor.End())
			insn.Next();
		const auto reg = ToCapstoneReg(static_cast<dart::Register>(int(load.cidReg)));
		if (!insn.Next() || !insn.Is(ARM_INS_SUB, 3) || insn.detail().update_flags)
			return nullptr;
		if (!isReg(insn.op(0), reg) || !isReg(insn.op(1), reg) || !isImm(insn.op(2), dart::kSmiCid))
			return nullptr;
		if (!insn.Next() || !insn.Is(ARM_INS_CMP, 2) || !isReg(insn.op(0), reg))
			return nullptr;
		if (insn.op(1).type != ARM_OP_IMM || (insn.op(1).imm != 1 && insn.op(1).imm != 2))
			return nullptr;
		range = insn.op(1).imm;
		if (!insn.Next() || !insn.Is(ARM_INS_B, 1, ARM_CC_LS) || !isImm(insn.op(0), done))
			return nullptr;
		if (!insn.Next())
			return nullptr;
	}
	auto slow = processTypeTestInstr(insn);
	if (!slow || insn.Range().end != done)
		return nullptr;
	const auto& type = static_cast<TestTypeInstr&>(*slow).typeName;
	const bool integer = type == "int" || type == "int?";
	const bool number = type == "num" || type == "num?";
	if (!integer && !number)
		return nullptr;
	if ((range == 1 && !integer) || (range == 2 && !number))
		return nullptr;
	return std::make_unique<TestTypeInstr>(insn.Range(), branch.objReg, type);
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processTypeTestInstr(InsnCursor& insn)
{
	// GenerateTTSCall: known per-type direct entry, or a type object's own
	// entry field. A random BLX after a pool load is not a type test.
	auto load = processObjectPoolInstr(insn);
	if (!load)
		return nullptr;
	const auto& pool = app.GetObjectPool();
	const auto poolObject = [&](const ILInstr& il) -> dart::ObjectPtr {
		const auto& value = static_cast<const LoadValueInstr&>(il);
		const auto index = PoolIndexFromOffset(value.val.storage.offset);
		if (pool.TypeAt(index) != dart::ObjectPool::EntryType::kTaggedObject)
			return dart::Object::null();
		return pool.ObjectAt(index);
	};
	dart::AbstractTypePtr expected = dart::AbstractType::null();
	arm_reg entry = ARM_REG_INVALID;
	if (static_cast<LoadValueInstr&>(*load).dstReg == Reg{dart::TypeTestABI::kDstTypeReg}) {
		const auto& type = dart::Object::Handle(poolObject(*load));
		if (!type.IsAbstractType())
			return nullptr;
		expected = dart::AbstractType::Cast(type).ptr();
		if (!insn.Next())
			return nullptr;
		const auto memory = readMemory(insn);
		if (memory && memory->load && memory->size == dart::kWordSize &&
			memory->base == ToCapstoneReg(dart::TypeTestABI::kDstTypeReg)) {
			if (memory->offset != AOT_AbstractType_type_test_stub_entry_point_offset - dart::kHeapObjectTag)
				return nullptr;
			entry = static_cast<arm_reg>(insn.op(0).reg);
			if (entry != ToCapstoneReg(dart::TTSInternalRegs::kScratchReg) || !insn.Next())
				return nullptr;
		}
		load = processObjectPoolInstr(insn);
		if (!load)
			return nullptr;
	}
	const auto& cache = static_cast<LoadValueInstr&>(*load);
	if (cache.dstReg != Reg{dart::TypeTestABI::kSubtypeTestCacheReg})
		return nullptr;
	if (pool.TypeAt(PoolIndexFromOffset(cache.val.storage.offset)) !=
		dart::ObjectPool::EntryType::kTaggedObject)
		return nullptr;
	const auto& value = dart::Object::Handle(poolObject(*load));
	if (!value.IsNull() && !value.IsSubtypeTestCache())
		return nullptr;
	if (!insn.Next())
		return nullptr;
	if (entry != ARM_REG_INVALID) {
		if (!insn.Is(ARM_INS_BLX, 1) || !isReg(insn.op(0), entry))
			return nullptr;
	} else {
		if (!insn.Is(ARM_INS_BL, 1) || insn.op(0).type != ARM_OP_IMM)
			return nullptr;
		auto* fn = app.FindFunctionExact(uint32_t(insn.op(0).imm));
		if (!fn || !fn->IsStub() || fn->AsStub()->kind != DartStub::TypeCheckStub)
			return nullptr;
		const auto& code = dart::Code::Handle(fn->AsStub()->ptr);
		if (code.IsNull() || uint32_t(code.EntryPoint() - uintptr_t(app.base())) != uint32_t(insn.op(0).imm))
			return nullptr;
		const auto& owner = dart::Object::Handle(code.owner());
		if (!owner.IsAbstractType())
			return nullptr;
		const auto type = dart::AbstractType::Cast(owner).ptr();
		if (expected != dart::AbstractType::null() && expected != type)
			return nullptr;
		expected = type;
	}
	auto* type = app.TypeDb()->FindOrAdd(expected);
	return std::make_unique<TestTypeInstr>(
		insn.Range(), Reg{dart::TypeTestABI::kInstanceReg}, type->ToString());
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processTryAllocateObjectInstr(InsnCursor& insn)
{
	// assembler_arm.cc TryAllocateObject (product): bump top, compare end,
	// commit top, tag the result, and initialize the class/size header.
	// ldr instance, [thr, #top]; add instance, instance, #size
	const auto top = readMemory(insn);
	if (!top || !top->load || top->size != dart::kWordSize)
		return nullptr;
	if (top->base != CSREG_DART_THR || top->offset != AOT_Thread_top_offset)
		return nullptr;
	const auto instance = insn.op(0).reg;
	if (!insn.Next() || !insn.Is(ARM_INS_ADD, 3))
		return nullptr;
	if (!isReg(insn.op(0), instance) || !isReg(insn.op(1), instance) || insn.op(2).type != ARM_OP_IMM)
		return nullptr;
	const auto size = insn.op(2).imm;
	if (size <= 0 || size % dart::kObjectAlignment)
		return nullptr;
	if (!insn.Next())
		return nullptr;
	const auto end = readMemory(insn);
	if (!end || !end->load || end->size != dart::kWordSize)
		return nullptr;
	if (end->base != CSREG_DART_THR || end->offset != AOT_Thread_end_offset)
		return nullptr;

	// cmp limit, instance; bls failure. The commit must remain on the fast path.
	const auto limit = insn.op(0).reg;
	if (instance == limit || !insn.Next() || !insn.Is(ARM_INS_CMP, 2))
		return nullptr;
	if (!isReg(insn.op(0), limit) || !isReg(insn.op(1), instance))
		return nullptr;
	if (!insn.Next() || !insn.Is(ARM_INS_B, 1, ARM_CC_LS) || insn.op(0).type != ARM_OP_IMM)
		return nullptr;
	const auto failure = uint32_t(insn.op(0).imm);
	if (failure <= insn.Current()->address || failure >= data.dartFn.AddressEnd())
		return nullptr;
	if (!insn.Next())
		return nullptr;

	// str instance, [thr, #top]; sub instance, instance, #(size - tag)
	const auto commit = readMemory(insn);
	if (!commit || commit->load || commit->size != dart::kWordSize)
		return nullptr;
	if (commit->base != CSREG_DART_THR || commit->offset != top->offset)
		return nullptr;
	if (commit->value != top->value)
		return nullptr;
	if (!insn.Next() || !insn.Is(ARM_INS_SUB, 3))
		return nullptr;
	if (!isReg(insn.op(0), instance) || !isReg(insn.op(1), instance) ||
		!isImm(insn.op(2), size - dart::kHeapObjectTag))
		return nullptr;
	if (!insn.Next())
		return nullptr;

	// LoadImmediate tags; str tags, [instance, #-tag]. Cross-check both
	// the encoded size and the VM class layout before publishing allocation IL.
	arm_reg tags;
	const auto header = readImmediate(insn, tags);
	if (!header || tags == instance || !insn.Next())
		return nullptr;
	const auto store = readMemory(insn);
	if (!store || store->load || store->size != 4 || store->base != instance || store->value != Reg{tags})
		return nullptr;
	if (store->offset != -dart::kHeapObjectTag || failure < insn.Range().end)
		return nullptr;
	const auto cid =
		(*header >> kUntaggedObjectClassIdTagPos) & ((1u << dart::UntaggedObject::kClassIdTagSize) - 1);
	auto* cls = app.FindClass(cid);
	if (!cls || dart::UntaggedObject::SizeTag::decode(*header) != size)
		return nullptr;
	intptr_t layout = cls->Size();
	if (cid == dart::kDoubleCid)
		layout = dart::Double::InstanceSize();
	if (cid == dart::kMintCid)
		layout = dart::Mint::InstanceSize();
	if (layout <= 0 || ((layout + dart::kObjectAlignment - 1) & -dart::kObjectAlignment) != size)
		return nullptr;
	return std::make_unique<AllocateObjectInstr>(insn.Range(), top->value, *cls);
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processWriteBarrierInstr(InsnCursor& insn)
{
	// StoreBarrier / ArrayStoreBarrier: conditional LDRNE+BLXNE on ARM,
	// not ARM64's branch around an unconditional call. LR may be spilled.
	arm_reg value = ARM_REG_INVALID;
	uint32_t done = 0;
	if (insn.Is(ARM_INS_TST, 2) && isImm(insn.op(1), dart::kSmiTagMask)) {
		if (insn.op(0).type != ARM_OP_REG)
			return nullptr;
		value = static_cast<arm_reg>(insn.op(0).reg);
		if (!insn.Next() || !insn.Is(ARM_INS_B, 1, ARM_CC_EQ) || insn.op(0).type != ARM_OP_IMM)
			return nullptr;
		done = uint32_t(insn.op(0).imm);
		if (!insn.Next())
			return nullptr;
	}

	// Optional LR spill, followed by object/value tag-byte loads.
	const bool spill = singleStackRegister(*insn.Current(), false) == Reg{dart::R14};
	if (spill && !insn.Next())
		return nullptr;
	if (!insn.Is(ARM_INS_LDRB, 2) || !isMemory(insn.op(1), insn.op(1).mem.base))
		return nullptr;
	if (insn.detail().writeback || insn.op(1).mem.disp != -dart::kHeapObjectTag)
		return nullptr;
	const auto object = static_cast<arm_reg>(insn.op(1).mem.base);
	const auto scratch = insn.op(0).reg;
	if (!insn.Next() || !insn.Is(ARM_INS_LDRB, 2) || !isReg(insn.op(0), ARM_REG_LR))
		return nullptr;
	if (!isMemory(insn.op(1), insn.op(1).mem.base) || insn.detail().writeback ||
		insn.op(1).mem.disp != -dart::kHeapObjectTag)
		return nullptr;
	if (value != ARM_REG_INVALID && value != insn.op(1).mem.base)
		return nullptr;
	value = static_cast<arm_reg>(insn.op(1).mem.base);
	if (object == ARM_REG_LR || object == value || scratch == object || scratch == value ||
		scratch == ARM_REG_LR)
		return nullptr;
	if (value != ToCapstoneReg(dart::kWriteBarrierValueReg))
		return nullptr;

	// and scratch, lr, scratch, lsr #overlap; ldr lr, [thr, #mask]; tst scratch, lr
	if (!insn.Next() || !insn.Is(ARM_INS_AND, 3) || insn.detail().update_flags)
		return nullptr;
	if (!isReg(insn.op(0), scratch) || !isReg(insn.op(1), ARM_REG_LR) || insn.op(2).type != ARM_OP_REG ||
		insn.op(2).reg != scratch)
		return nullptr;
	if (insn.op(2).shift.type != ARM_SFT_LSR ||
		insn.op(2).shift.value != dart::UntaggedObject::kBarrierOverlapShift)
		return nullptr;
	if (!insn.Next())
		return nullptr;
	const auto mask = readMemory(insn);
	if (!mask || !mask->load || mask->size != dart::kWordSize)
		return nullptr;
	if (mask->base != CSREG_DART_THR || mask->value != Reg{dart::R14})
		return nullptr;
	if (mask->offset != AOT_Thread_write_barrier_mask_offset)
		return nullptr;
	if (!insn.Next() || !insn.Is(ARM_INS_TST, 2))
		return nullptr;
	if (!isReg(insn.op(0), scratch) || !isReg(insn.op(1), ARM_REG_LR))
		return nullptr;
	if (!insn.Next())
		return nullptr;

	// The NE call must reach the array stub or the wrapper for this object
	// register. A matching stub family alone does not prove the correct entry.
	bool array = false;
	if (insn.Is(ARM_INS_BL, 1, ARM_CC_NE) && insn.op(0).type == ARM_OP_IMM) {
		// AOT relocation can replace the THR load/call with a direct BLNE.
		const auto target = uint32_t(insn.op(0).imm);
		auto* fn = app.GetFunction(target);
		if (!fn || !fn->IsStub())
			return nullptr;
		const auto kind = fn->AsStub()->kind;
		// GetFunction may split a stub at a referenced entry. Use the original
		// VM Code entry, not the address of that mutable split, as the origin.
		const auto& code = dart::Code::Handle(fn->AsStub()->ptr);
		if (code.IsNull())
			return nullptr;
		const auto origin = uint32_t(code.EntryPoint() - uintptr_t(app.base()));
		array = kind == DartStub::ArrayWriteBarrierStub;
		if (array) {
			if (target != origin)
				return nullptr;
		} else {
			if (kind != DartStub::WriteBarrierWrappersStub)
				return nullptr;
			const auto reg = static_cast<dart::Register>(int(Reg{object}));
			if (!(dart::kDartAvailableCpuRegs & (1 << reg)))
				return nullptr;
			const auto offset = dart::Thread::WriteBarrierWrappersOffsetForRegister(reg);
			if (target != origin + offset)
				return nullptr;
		}
	} else {
		if (!insn.Is(ARM_INS_LDR, 2, ARM_CC_NE) || !isReg(insn.op(0), ARM_REG_LR))
			return nullptr;
		if (!isMemory(insn.op(1), CSREG_DART_THR) || insn.detail().writeback)
			return nullptr;
		const auto entry = insn.op(1).mem.disp;
		array = entry == AOT_Thread_array_write_barrier_entry_point_offset;
		if (!array) {
			const auto reg = static_cast<dart::Register>(int(Reg{object}));
			if (!(dart::kDartAvailableCpuRegs & (1 << reg)))
				return nullptr;
			if (entry != dart::Thread::write_barrier_wrappers_thread_offset(reg))
				return nullptr;
		}
		if (!insn.Next() || !insn.Is(ARM_INS_BLX, 1, ARM_CC_NE) || !isReg(insn.op(0), ARM_REG_LR))
			return nullptr;
	}

	// Restore spilled LR and prove the optional Smi branch rejoins after it.
	if (array && object != ToCapstoneReg(dart::kWriteBarrierObjectReg))
		return nullptr;
	if (spill) {
		if (!insn.Next() || singleStackRegister(*insn.Current(), true) != Reg{dart::R14})
			return nullptr;
	}
	if (done && done != insn.Range().end)
		return nullptr;
	return std::make_unique<WriteBarrierInstr>(insn.Range(), Reg{object}, Reg{value}, array);
}

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

std::unique_ptr<ILInstr> FunctionAnalyzer::processTaggedClassIdInstr(InsnCursor& insn)
{
	// LoadTaggedClassIdMayBeSmi = predicated LoadClassIdMayBeSmi + SmiTag.
	auto load = processLoadClassIdInstr(insn);
	if (!load)
		return nullptr;
	const auto& cid = static_cast<LoadClassIdInstr&>(*load);
	if (!cid.mayBeSmi || !insn.Next() || !insn.Is(ARM_INS_LSL, 2) || insn.detail().update_flags)
		return nullptr;
	if (Reg{static_cast<arm_reg>(insn.op(0).reg)} != cid.cidReg)
		return nullptr;
	if (Reg{static_cast<arm_reg>(insn.op(1).reg)} != cid.cidReg)
		return nullptr;
	if (insn.op(1).shift.type != ARM_SFT_LSL || insn.op(1).shift.value != dart::kSmiTagSize)
		return nullptr;
	return std::make_unique<LoadTaggedClassIdMayBeSmiInstr>(insn.Range(), cid.objReg, cid.cidReg);
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processBoxInt64Instr(InsnCursor& insn)
{
	// il_arm.cc BoxInt64: compare both words with the sign-extended Smi,
	// allocate via a known shared Mint stub, then store both payload words.
	if (!insn.Is(ARM_INS_LSL, 2) || insn.detail().update_flags)
		return nullptr;
	if (insn.op(0).type != ARM_OP_REG || insn.op(1).type != ARM_OP_REG)
		return nullptr;
	if (insn.op(1).shift.type != ARM_SFT_LSL || insn.op(1).shift.value != dart::kSmiTagSize)
		return nullptr;
	const auto object = insn.op(0).reg, low = insn.op(1).reg;
	if (object == low || !insn.Next() || !insn.Is(ARM_INS_CMP, 2))
		return nullptr;
	const auto compare = [&](const InsnCursor& cursor, int source, unsigned shift) {
		if (cursor.op(1).type != ARM_OP_REG || cursor.op(1).reg != object ||
			cursor.op(1).shift.type != ARM_SFT_ASR)
			return false;
		return isReg(cursor.op(0), source) && cursor.op(1).shift.value == shift;
	};
	if (!compare(insn, low, dart::kSmiTagSize))
		return nullptr;
	if (!insn.Next() || !insn.Is(ARM_INS_CMP, 2, ARM_CC_EQ) || insn.op(0).type != ARM_OP_REG)
		return nullptr;
	const auto high = insn.op(0).reg;
	for (auto source : {low, high}) {
		Reg reg{static_cast<arm_reg>(source)};
		if (!reg.IsSet() || reg.IsDecimal() || !(dart::kDartAvailableCpuRegs & (1 << int(reg))))
			return nullptr;
	}
	if (high == low || high == object || !compare(insn, high, 31))
		return nullptr;
	if (!insn.Next() || !insn.Is(ARM_INS_B, 1, ARM_CC_EQ) || insn.op(0).type != ARM_OP_IMM)
		return nullptr;
	const auto done = uint32_t(insn.op(0).imm);
	if (!insn.Next() || object != ToCapstoneReg(dart::AllocateMintABI::kResultReg))
		return nullptr;
	// Frameless functions temporarily enter a Dart frame around the shared
	// allocation call. Check both halves without changing function frame facts.
	const bool temporaryFrame = insn.Is(ARM_INS_PUSH, 2);
	if (temporaryFrame) {
		if (!isReg(insn.op(0), CSREG_DART_FP) || !isReg(insn.op(1), ARM_REG_LR) || !insn.Next())
			return nullptr;
		bool frame = insn.Is(ARM_INS_MOV, 2) && isReg(insn.op(1), CSREG_DART_SP);
		if (insn.Is(ARM_INS_ADD, 3))
			frame = isReg(insn.op(1), CSREG_DART_SP) && isImm(insn.op(2), 0);
		if (!frame || !isReg(insn.op(0), CSREG_DART_FP) || !insn.Next())
			return nullptr;
	}
	bool mint = false;
	const auto memory = readMemory(insn);
	if (memory && memory->load && memory->size == dart::kWordSize && memory->base == CSREG_DART_THR) {
		mint = memory->offset == AOT_Thread_allocate_mint_with_fpu_regs_entry_point_offset ||
			   memory->offset == AOT_Thread_allocate_mint_without_fpu_regs_entry_point_offset;
		const auto entry = static_cast<arm_reg>(insn.op(0).reg);
		if (!mint || entry != ARM_REG_LR || !insn.Next() || !insn.Is(ARM_INS_BLX, 1) ||
			!isReg(insn.op(0), entry))
			return nullptr;
	} else {
		auto call = insn.Is(ARM_INS_BL, 1) ? processCallInstr(insn) : processPoolCallInstr(insn);
		if (!call)
			return nullptr;
		// A Code/call-data pool load must not replace either source word.
		for (size_t i = data.asmTexts.AtIndex(call->Start());
			i < instructions.Count() && instructions.Ptr(i)->address < call->End();
			++i) {
			const auto& arm = instructions.Ptr(i)->detail->arm;
			for (unsigned j = 0; j < arm.op_count; ++j)
				if (arm.operands[j].type == ARM_OP_REG && (arm.operands[j].access & CS_AC_WRITE) &&
					(arm.operands[j].reg == low || arm.operands[j].reg == high))
					return nullptr;
		}
		auto* fn = static_cast<CallInstr&>(*call).GetFunction();
		if (fn && fn->IsStub()) {
			const auto kind = fn->AsStub()->kind;
			mint = kind == DartStub::AllocateMintSharedWithFPURegsStub ||
				   kind == DartStub::AllocateMintSharedWithoutFPURegsStub;
			const auto& code = dart::Code::Handle(fn->AsStub()->ptr);
			if (code.IsNull() || static_cast<CallInstr&>(*call).GetCallAddress() !=
									 uint32_t(code.EntryPoint() - uintptr_t(app.base())))
				return nullptr;
		}
	}
	if (!mint)
		return nullptr;
	if (temporaryFrame) {
		if (!insn.Next())
			return nullptr;
		bool restore = insn.Is(ARM_INS_MOV, 2) && isReg(insn.op(1), CSREG_DART_FP);
		if (insn.Is(ARM_INS_SUB, 3))
			restore = isReg(insn.op(1), CSREG_DART_FP) && isImm(insn.op(2), 0);
		if (!restore || !isReg(insn.op(0), CSREG_DART_SP) || !insn.Next())
			return nullptr;
		if (!insn.Is(ARM_INS_POP, 2) || !isReg(insn.op(0), CSREG_DART_FP) || !isReg(insn.op(1), ARM_REG_LR))
			return nullptr;
	}
	for (int word = 0; word < 2; ++word) {
		if (!insn.Next())
			return nullptr;
		const auto store = readMemory(insn);
		if (!store || store->load || store->size != 4 || store->base != object)
			return nullptr;
		if (store->value != Reg{static_cast<arm_reg>(word ? high : low)})
			return nullptr;
		if (store->offset != AOT_Mint_value_offset - dart::kHeapObjectTag + word * dart::kWordSize)
			return nullptr;
	}
	if (done != insn.Range().end)
		return nullptr;
	return std::make_unique<BoxInt64Instr>(insn.Range(),
		Reg{static_cast<arm_reg>(object)},
		Reg{static_cast<arm_reg>(low)},
		Reg{static_cast<arm_reg>(high)});
}

// PrologueBuilder produces descriptor arithmetic, followed by supplied/default
// diamonds. Track only those expressions; do not interpret arbitrary body code.
class ArmParameterRecovery
{
	FunctionAnalyzer& fn;
	bool inferredDeclaration{false};
	std::vector<int> requiredOrder;
	enum Kind {
		Unknown,
		Descriptor,
		Count,
		FrameAddress,
		Name,
		Position,
		Value,
		Constant,
		Symbol,
		Dynamic,
		Null,
		TypeArgsLength,
		TypeArgsValue,
		RequiredPosition,
		Context,
		DoubleAddress,
		DoubleValue
	};
	struct Source {
		Kind kind{Unknown};
		int64_t offset{0};
		int parameter{-1};
		int64_t scale{1};
		bool operator==(const Source&) const = default;
	};
	using Registers = std::array<Source, Reg::kNumberOfRegisters>;
	Registers registers{};
	std::vector<AddrRange> ranges, typeArgumentRanges;
	std::unordered_set<uint64_t> joins;
	int checkedTuple{-1}, checkedParameter{-1}, checkedSymbol{-1}, checkedScale{1}, nextSymbol{0};

	Source source(const cs_arm_op& op) const
	{
		if (op.type == ARM_OP_IMM)
			return {Constant, op.imm};
		if (op.type != ARM_OP_REG || op.shift.type != ARM_SFT_INVALID)
			return {};
		Reg reg{static_cast<arm_reg>(op.reg)};
		return reg.IsSet() ? registers[reg] : Source{};
	}
	bool transfer(size_t& index);
	bool defaultDiamond(size_t& index);
	bool typeArgumentDiamond(size_t& index);
	bool floatingConstant(size_t& index, std::unique_ptr<ILInstr>* constant = nullptr);
	bool doubleParameter(int parameter) const;
	bool closedRange(size_t begin, size_t end) const;
	int comparedParameter(const cs_arm& arm, int& tuple);

  public:
	explicit ArmParameterRecovery(FunctionAnalyzer& fn) : fn(fn), inferredDeclaration(fn.data.params.empty())
	{
		// With only required names, every descriptor entry is present and its
		// alphabetic slot is proven by the surviving signature. Mixed optional
		// names require the explicit name comparison protocol instead.
		if (!fn.data.params.isNamedParam || inferredDeclaration)
			return;
		for (int i = fn.data.params.numFixedParam; i < fn.data.params.NumParam(); ++i) {
			if (i >= fn.data.dartFn.NumParam() || !fn.data.dartFn.Params()[i].isRequired ||
				fn.data.params[i].name.empty()) {
				requiredOrder.clear();
				return;
			}
			requiredOrder.push_back(i);
		}
		std::sort(requiredOrder.begin(), requiredOrder.end(), [&](int left, int right) {
			const auto& vm = dart::Function::Handle(fn.data.dartFn.Ptr());
			const auto& a = dart::String::Handle(vm.ParameterNameAt(left));
			const auto& b = dart::String::Handle(vm.ParameterNameAt(right));
			return a.CompareTo(b) < 0;
		});
	}
	void Recover();
};

bool ArmParameterRecovery::closedRange(size_t begin, size_t end) const
{
	const auto first = fn.instructions.Ptr(begin)->address;
	const auto last = fn.instructions.Ptr(end)->address;
	for (size_t i = 0; i < fn.instructions.Count(); ++i) {
		const auto& instruction = *fn.instructions.Ptr(i);
		if (instruction.id != ARM_INS_B && instruction.id != ARM_INS_BL)
			continue;
		const auto& arm = instruction.detail->arm;
		if (arm.op_count != 1 || arm.operands[0].type != ARM_OP_IMM)
			continue;
		const auto target = uint32_t(arm.operands[0].imm);
		if (target > first && target < last && (i < begin || i >= end))
			return false;
	}
	return true;
}

bool ArmParameterRecovery::doubleParameter(int parameter) const
{
	if (fn.data.dartFn.Ptr() == dart::Function::null())
		return false;
	const auto& vm = dart::Function::Handle(fn.data.dartFn.Ptr());
	const auto& signature = dart::FunctionType::Handle(vm.signature());
	if (signature.IsNull() || parameter < 0 || parameter >= signature.NumParameters())
		return false;
	return dart::AbstractType::Handle(signature.ParameterTypeAt(parameter)).IsDoubleType();
}

bool ArmParameterRecovery::transfer(size_t& index)
{
	InsnCursor cursor{fn.instructions, fn.targets, index};
	const auto& arm = cursor.detail();
	if (!isUnconditional(*cursor.Current()) || arm.update_flags)
		return false;
	auto poolCursor = cursor;
	auto constant = fn.processObjectPoolInstr(poolCursor);
	if (constant)
		index = poolCursor.End() - 1;
	if (!constant) {
		constant = fn.processLoadValueInstr(cursor);
	}
	if (constant) {
		auto& load = static_cast<LoadValueInstr&>(*constant);
		Source result;
		if (load.val.Value()->RawTypeId() == dart::kNullCid)
			result = {Null};
		else if (load.val.Value()->RawTypeId() == dart::kIntegerCid)
			result = {Constant, int(load.val.Value()->AsInteger()->val)};
		else if (load.val.Value()->RawTypeId() == dart::kStringCid &&
				 load.val.storage.kind == VarStorage::Pool)
			result = {Symbol, int(load.val.storage.offset)};
		registers[load.dstReg] = result;
		index = std::max(index, cursor.End() - 1);
		return true;
	}
	Source result;
	if (cursor.Is(ARM_INS_MOV, 2)) {
		result = source(arm.operands[1]);
	} else if ((cursor.Is(ARM_INS_ADD, 3) || cursor.Is(ARM_INS_SUB, 3)) && !arm.update_flags) {
		const auto left = source(arm.operands[1]);
		const auto right = source(arm.operands[2]);
		const int sign = cursor.Current()->id == ARM_INS_ADD ? 1 : -1;
		if (left.kind == Count && right.kind == Constant) {
			result = {Count, left.offset + sign * right.offset, left.parameter};
			if (inferredDeclaration && left.parameter == -1 && left.offset == 0 && sign == -1 &&
				right.offset >= 0 && right.offset % 2 == 0 && right.offset / 2 < UINT8_MAX &&
				fn.data.params.empty()) {
				fn.data.params.numFixedParam = right.offset / 2;
				for (int i = 0; i < fn.data.params.numFixedParam; ++i)
					fn.data.params.add(FnParamInfo{});
			}
		} else if (left.kind == Count && left.parameter == -1 && left.offset == 0 &&
				   right.kind == RequiredPosition && sign == -1)
			result = {Count, left.offset, right.parameter};
		else if (left.kind == Count && left.parameter == -1 && left.offset == 0 && right.kind == Position &&
				 sign == -1 && right.offset == checkedTuple && right.parameter == checkedSymbol &&
				 right.scale == checkedScale)
			result = {Count, left.offset, checkedParameter};
		else if (left.kind == Value && right.kind == Constant && sign == 1 && doubleParameter(left.parameter))
			result = {DoubleAddress, right.offset, left.parameter};
		else if (left.kind == Dynamic && right.kind == Constant)
			result = {Dynamic, left.offset + sign * right.offset, left.parameter, left.scale};
		else if (left.kind == Constant && right.kind == Constant)
			result = {Constant, left.offset + sign * right.offset};
		else if (sign == 1 && arm.operands[2].type == ARM_OP_REG) {
			const auto& shifted = arm.operands[2];
			const Reg reg{static_cast<arm_reg>(shifted.reg)};
			if (!reg.IsSet() || shifted.shift.type != ARM_SFT_LSL || shifted.shift.value != 1)
				return false;
			const auto offset = registers[reg];
			if (isReg(arm.operands[1], CSREG_DART_FP) && offset.kind == Count)
				result = {FrameAddress, offset.offset * 2, offset.parameter};
			else if (left.kind == Descriptor && (offset.kind == Constant || offset.kind == Dynamic))
				result = {Descriptor, left.offset + offset.offset * 2, offset.parameter, offset.scale * 2};
		}
	} else if (cursor.Is(ARM_INS_LSL, 2) && !arm.update_flags) {
		const auto& shifted = arm.operands[1];
		const Reg reg{static_cast<arm_reg>(shifted.reg)};
		if (shifted.type == ARM_OP_REG && reg.IsSet() && shifted.shift.value < 5) {
			const auto value = registers[reg];
			if ((value.kind == Constant || value.kind == Dynamic) && value.scale <= 64 &&
				value.offset >= INT32_MIN && value.offset <= INT32_MAX)
				result = {value.kind,
					value.offset * (1 << shifted.shift.value),
					value.parameter,
					value.scale * (1 << shifted.shift.value)};
		}
	} else if (const auto memory = readMemory(cursor)) {
		Reg base{memory->base};
		if (!base.IsSet())
			return false;
		const auto address = registers[base];
		if (memory->load && memory->size == 8 && memory->value.IsDecimal() && address.kind == DoubleAddress) {
			if (address.offset + memory->offset != AOT_Double_value_offset - dart::kHeapObjectTag)
				return false;
			registers[memory->value] = {DoubleValue, 0, address.parameter};
			return true;
		}
		if (memory->size != dart::kWordSize &&
			!(memory->size == 8 && !memory->load && registers[memory->value].kind == DoubleValue))
			return false;
		if (!memory->load) {
			if (memory->base != CSREG_DART_FP || memory->offset >= 0)
				return false;
			// A spill of another entry value does not alter descriptor facts.
			return true;
		}
		if (address.kind == Descriptor) {
			const auto offset = address.offset + memory->offset + dart::kHeapObjectTag;
			if (offset == dart::ArgumentsDescriptor::count_offset())
				result = {Count};
			else if (offset == dart::ArgumentsDescriptor::type_args_len_offset())
				result = {TypeArgsLength};
			else if (offset == dart::ArgumentsDescriptor::size_offset())
				result = {Count, 0, -2};
			else if (offset >= dart::ArgumentsDescriptor::first_named_entry_offset() &&
					 offset < dart::ArgumentsDescriptor::first_named_entry_offset() +
								  UINT8_MAX * dart::ArgumentsDescriptor::named_entry_size()) {
				const auto tuple = offset - dart::ArgumentsDescriptor::first_named_entry_offset();
				if (tuple % dart::ArgumentsDescriptor::named_entry_size() ==
					dart::ArgumentsDescriptor::name_offset())
					result = {Name, tuple, address.parameter, address.scale};
				else if (tuple % dart::ArgumentsDescriptor::named_entry_size() ==
						 dart::ArgumentsDescriptor::position_offset())
					result = {Position,
						tuple - dart::ArgumentsDescriptor::position_offset(),
						address.parameter,
						address.scale};
				if (result.kind == Position && address.parameter == -1) {
					const auto entry = result.offset / dart::ArgumentsDescriptor::named_entry_size();
					if (entry >= 0 && entry < int(requiredOrder.size()))
						result = {RequiredPosition, result.offset, requiredOrder[entry]};
				}
			}
		} else if (address.kind == FrameAddress) {
			const auto offset = address.offset + memory->offset;
			int parameter = address.parameter;
			if (parameter >= 0 && offset != dart::kWordSize)
				return false;
			if (parameter == -2 && offset == 2 * dart::kWordSize)
				result = {TypeArgsValue};
			if (parameter == -1 && offset % dart::kWordSize == 0)
				parameter = 1 - offset / dart::kWordSize;
			if (parameter >= 0 && parameter < fn.data.params.NumParam())
				result = {Value, 0, parameter};
		} else if (address.kind == Value && address.parameter == 0 && fn.data.dartFn.IsClosure() &&
				   memory->offset == AOT_Closure_context_offset - dart::kHeapObjectTag) {
			result = {Context};
		} else if (memory->base == CSREG_DART_FP) {
			for (int i = 0; i < fn.data.params.NumParam(); ++i)
				if (fn.data.params[i].paramOffset == memory->offset &&
					fn.data.params[i].valReg == memory->value)
					result = {Value, 0, i};
		} else {
			return false;
		}
		registers[memory->value] = result;
		return true;
	} else {
		return false;
	}
	if (arm.op_count == 0 || arm.operands[0].type != ARM_OP_REG)
		return false;
	Reg destination{static_cast<arm_reg>(arm.operands[0].reg)};
	if (!destination.IsSet() || destination.IsDecimal())
		return false;
	registers[destination] = result;
	return true;
}

int ArmParameterRecovery::comparedParameter(const cs_arm& arm, int& tuple)
{
	const auto left = source(arm.operands[0]), right = source(arm.operands[1]);
	if (left.kind == Count && left.parameter == -1 && right.kind == Constant &&
		!fn.data.params.isNamedParam) {
		if (right.offset <= 0 || right.offset % 2 || left.offset % 2)
			return -1;
		const auto parameter = (right.offset - left.offset) / 2 - 1;
		if (parameter < 0 || parameter >= UINT8_MAX)
			return -1;
		if (inferredDeclaration && parameter >= fn.data.params.numFixedParam && parameter < UINT8_MAX)
			while (fn.data.params.NumParam() <= parameter)
				fn.data.params.add(FnParamInfo{});
		return parameter;
	}
	const auto name = left.kind == Name ? left : right;
	const auto symbol = left.kind == Symbol ? left : right;
	if (name.kind != Name || symbol.kind != Symbol)
		return -1;
	const auto& pool = fn.app.GetObjectPool();
	const auto& object = dart::Object::Handle(pool.ObjectAt(PoolIndexFromOffset(symbol.offset)));
	if (!object.IsString())
		return -1;
	tuple = name.offset;
	checkedSymbol = name.parameter;
	checkedScale = name.scale;
	const std::string text = dart::String::Cast(object).ToCString();
	for (int i = fn.data.params.numFixedParam; i < fn.data.params.NumParam(); ++i)
		if (fn.data.params[i].name == text)
			return i;
	if (inferredDeclaration && fn.data.params.NumParam() < UINT8_MAX) {
		fn.data.params.isNamedParam = true;
		fn.data.params.add(FnParamInfo{text});
		return fn.data.params.NumParam() - 1;
	}
	return -1;
}

bool ArmParameterRecovery::defaultDiamond(size_t& index)
{
	const auto& compare = *fn.instructions.Ptr(index);
	if (compare.id != ARM_INS_CMP || compare.detail->arm.op_count != 2 || !isUnconditional(compare))
		return false;
	struct DeclarationCandidate {
		FnParams& params;
		size_t count;
		bool named, accepted{false};
		~DeclarationCandidate()
		{
			if (!accepted) {
				params.params.resize(count);
				params.isNamedParam = named;
			}
		}
	} declaration{fn.data.params, fn.data.params.params.size(), fn.data.params.isNamedParam};
	checkedTuple = -1;
	checkedSymbol = -1;
	checkedScale = 1;
	checkedParameter = comparedParameter(compare.detail->arm, checkedTuple);
	if (checkedParameter < fn.data.params.numFixedParam || checkedParameter >= fn.data.params.NumParam())
		return false;
	if (index + 2 >= fn.instructions.Count())
		return false;
	const auto& branch = *fn.instructions.Ptr(index + 1);
	const auto& arm = branch.detail->arm;
	const auto condition = fn.data.params.isNamedParam ? ARM_CC_NE : ARM_CC_LT;
	if (branch.id != ARM_INS_B || arm.cc != condition || arm.op_count != 1 ||
		arm.operands[0].type != ARM_OP_IMM)
		return false;
	const auto missingAddress = uint32_t(arm.operands[0].imm);
	const auto origin = fn.instructions.FirstPtr()->address;
	if (missingAddress < branch.address + 8 || missingAddress >= fn.instructions.LastPtr()->address)
		return false;
	const size_t missing = (missingAddress - origin) / 4;
	if (fn.instructions.Ptr(missing)->address != missingAddress)
		return false;
	const auto& jump = *fn.instructions.Ptr(missing - 1);
	const bool triangle = jump.id != ARM_INS_B || !isUnconditional(jump);
	if (triangle && !fn.data.params.isNamedParam)
		return false;
	if (!triangle && (jump.detail->arm.op_count != 1 || jump.detail->arm.operands[0].type != ARM_OP_IMM))
		return false;
	const auto joinAddress = triangle ? missingAddress : uint32_t(jump.detail->arm.operands[0].imm);
	if (joinAddress < missingAddress || (!triangle && joinAddress == missingAddress) ||
		joinAddress > fn.instructions.LastPtr()->address)
		return false;
	const size_t join = (joinAddress - origin) / 4;
	if (fn.instructions.Ptr(join)->address != joinAddress || !closedRange(index, join))
		return false;

	const auto before = registers;
	for (size_t i = index + 2; i < missing - (triangle ? 0 : 1); ++i) {
		if (!transfer(i)) {
			registers = before;
			return false;
		}
	}
	const auto supplied = registers;
	registers = before;
	std::unique_ptr<VarValue> value;
	Reg destination;
	// Defaults are constants, with optional parallel moves/processed-count
	// updates. Prove the very same result register on the supplied path.
	for (size_t i = missing; i < join; ++i) {
		const auto& writes = fn.instructions.Ptr(i)->detail->arm;
		for (unsigned j = 0; j < writes.op_count; ++j) {
			const auto& op = writes.operands[j];
			if (op.type == ARM_OP_REG && (op.access & CS_AC_WRITE) &&
				Reg{static_cast<arm_reg>(op.reg)} == destination) {
				value.reset();
				destination.Clear();
			}
		}
		std::unique_ptr<ILInstr> floating;
		if (floatingConstant(i, &floating)) {
			auto& constant = static_cast<LoadValueInstr&>(*floating);
			if (supplied[constant.dstReg] == Source{DoubleValue, 0, checkedParameter}) {
				destination = constant.dstReg;
				value = constant.val.TakeValue();
			}
			continue;
		}
		InsnCursor cursor{fn.instructions, fn.targets, i};
		auto load = fn.processObjectPoolInstr(cursor);
		if (!load) {
			InsnCursor immediate{fn.instructions, fn.targets, i};
			load = fn.processLoadValueInstr(immediate);
		}
		if (load) {
			auto& constant = static_cast<LoadValueInstr&>(*load);
			if (supplied[constant.dstReg] == Source{Value, 0, checkedParameter} ||
				supplied[constant.dstReg] == Source{DoubleValue, 0, checkedParameter}) {
				destination = constant.dstReg;
				value = constant.val.TakeValue();
			}
		}
		if (!transfer(i)) {
			registers = before;
			return false;
		}
	}
	// DCE can remove an unused named value and its default while retaining
	// the name-presence/index update needed for later names. Prove only that
	// protocol, never invent a default from a 0/2 presence flag.
	const bool unused = !value && fn.data.params.isNamedParam &&
						std::none_of(supplied.begin(), supplied.end(), [&](const Source& source) {
							return (source.kind == Value || source.kind == DoubleValue) &&
								   source.parameter == checkedParameter;
						});
	if (unused) {
		for (size_t i = index + 2; i < join; ++i) {
			const auto id = fn.instructions.Ptr(i)->id;
			if (id != ARM_INS_MOV && id != ARM_INS_MOVW && id != ARM_INS_MOVT && id != ARM_INS_ADD &&
				id != ARM_INS_SUB && id != ARM_INS_LSL && id != ARM_INS_B) {
				registers = before;
				return false;
			}
		}
	}
	if ((!value || !destination.IsSet()) && !unused) {
		registers = before;
		return false;
	}
	// Optional parameters are loaded as tagged values by PrologueBuilder.
	// ARM immediate moves carry raw Smi bits, unlike PP's typed constants.
	if (value && value->RawTypeId() == dart::kIntegerCid) {
		auto* integer = static_cast<VarInteger*>(value.get());
		if (integer->intTypeId == VarValue::NativeInt) {
			if ((integer->val & dart::kSmiTagMask) != dart::kSmiTag) {
				registers = before;
				return false;
			}
			integer->intTypeId = dart::kSmiCid;
		}
	}
	for (size_t r = 0; r < registers.size(); ++r) {
		if (registers[r] == supplied[r])
			continue;
		// A varying processed-name index is still a symbolic affine value.
		// Preserve identity through scaling; name/position must use the same
		// expression. This does not guess how many names were supplied.
		if ((registers[r].kind == Constant || registers[r].kind == Dynamic) &&
			(supplied[r].kind == Constant || supplied[r].kind == Dynamic))
			registers[r] = {Dynamic, 0, ++nextSymbol};
		else
			registers[r] = {};
	}
	if (!unused) {
		registers[destination] = {destination.IsDecimal() ? DoubleValue : Value, 0, checkedParameter};
		auto& parameter = fn.data.params[checkedParameter];
		parameter.valReg = destination;
		parameter.val = std::move(value);
	}
	declaration.accepted = true;
	ranges.push_back({compare.address, joinAddress});
	joins.insert(joinAddress);
	index = join - 1;
	return true;
}

bool ArmParameterRecovery::typeArgumentDiamond(size_t& index)
{
	const auto& compare = *fn.instructions.Ptr(index);
	const auto& cmp = compare.detail->arm;
	if (compare.id != ARM_INS_CMP || cmp.op_count != 2 || !isUnconditional(compare))
		return false;
	if (source(cmp.operands[0]).kind != TypeArgsLength || !isImm(cmp.operands[1], 0))
		return false;
	if (index + 2 >= fn.instructions.Count())
		return false;
	const auto& branch = *fn.instructions.Ptr(index + 1);
	const auto& arm = branch.detail->arm;
	if (branch.id != ARM_INS_B || arm.cc != ARM_CC_NE || arm.op_count != 1 ||
		arm.operands[0].type != ARM_OP_IMM)
		return false;
	const auto suppliedAddress = uint32_t(arm.operands[0].imm);
	if (suppliedAddress < branch.address + 8 || suppliedAddress >= fn.instructions.LastPtr()->address)
		return false;
	const size_t supplied = (suppliedAddress - fn.instructions.FirstPtr()->address) / 4;
	if (fn.instructions.Ptr(supplied)->address != suppliedAddress)
		return false;
	const auto& jump = *fn.instructions.Ptr(supplied - 1);
	const auto& edge = jump.detail->arm;
	if (jump.id != ARM_INS_B || !isUnconditional(jump) || edge.op_count != 1 ||
		edge.operands[0].type != ARM_OP_IMM)
		return false;
	const auto joinAddress = uint32_t(edge.operands[0].imm);
	if (joinAddress <= suppliedAddress || joinAddress > fn.instructions.LastPtr()->address)
		return false;
	const size_t join = (joinAddress - fn.instructions.FirstPtr()->address) / 4;
	if (fn.instructions.Ptr(join)->address != joinAddress || !closedRange(index, join))
		return false;
	const auto before = registers;
	for (size_t i = index + 2; i < supplied - 1; ++i)
		if (!transfer(i)) {
			registers = before;
			return false;
		}
	const auto absent = registers;
	registers = before;
	for (size_t i = supplied; i < join; ++i)
		if (!transfer(i)) {
			registers = before;
			return false;
		}
	Reg result;
	for (size_t r = 0; r < registers.size(); ++r) {
		if (registers[r].kind == TypeArgsValue && absent[r].kind == Null)
			result = Reg{static_cast<Reg::Value>(r)};
		if (registers[r] != absent[r])
			registers[r] = {};
	}
	if (!result.IsSet()) {
		registers = before;
		return false;
	}
	registers[result] = {TypeArgsValue};
	fn.data.typeArgumentReg = result;
	typeArgumentRanges.push_back({compare.address, joinAddress});
	joins.insert(joinAddress);
	index = join - 1;
	return true;
}

bool ArmParameterRecovery::floatingConstant(size_t& index, std::unique_ptr<ILInstr>* constant)
{
	InsnCursor cursor{fn.instructions, fn.targets, index};
	const auto saved = singleStackRegister(*cursor.Current(), false);
	if (!saved.IsSet() || saved.IsDecimal() || !cursor.Next())
		return false;
	auto pool = cursor;
	auto load = fn.processObjectPoolInstr(pool);
	if (load) {
		while (cursor.End() < pool.End())
			cursor.Next();
	} else
		load = fn.processLoadValueInstr(cursor);
	if (!load || !static_cast<LoadValueInstr&>(*load).dstReg.IsDecimal())
		return false;
	if (!cursor.Next() || singleStackRegister(*cursor.Current(), true) != saved)
		return false;
	const auto value = registers[saved];
	for (size_t i = index; i < cursor.End(); ++i) {
		const auto& arm = fn.instructions.Ptr(i)->detail->arm;
		for (unsigned j = 0; j < arm.op_count; ++j) {
			const auto& op = arm.operands[j];
			Reg reg{static_cast<arm_reg>(op.reg)};
			if (op.type == ARM_OP_REG && reg.IsSet() && (op.access & CS_AC_WRITE))
				registers[reg] = {};
		}
	}
	registers[saved] = value;
	index = cursor.End() - 1;
	if (constant)
		*constant = std::move(load);
	return true;
}

void ArmParameterRecovery::Recover()
{
	if (!fn.data.useFramePointer)
		return;
	if (inferredDeclaration)
		fn.data.params.isPartial = true;
	if (!fn.data.params.isPartial) {
		if (fn.data.dartFn.Ptr() == dart::Function::null())
			return;
		const auto& vm = dart::Function::Handle(fn.data.dartFn.Ptr());
		const auto& signature = dart::FunctionType::Handle(vm.signature());
		if (signature.IsNull() || !vm.IsGeneric())
			return;
	}
	registers[Reg{dart::ARGS_DESC_REG}] = {Descriptor};
	for (size_t i = 0; i < fn.instructions.Count(); ++i) {
		const auto& instruction = *fn.instructions.Ptr(i);
		// Frame construction is structural; the first stack check closes the
		// copy/default prologue. Never follow a body call or an unproved edge.
		if (fn.data.firstCheckStackOverflowAddr && instruction.address >= fn.data.firstCheckStackOverflowAddr)
			break;
		if (instruction.id == ARM_INS_PUSH ||
			(instruction.id == ARM_INS_ADD && isReg(instruction.detail->arm.operands[0], CSREG_DART_FP)) ||
			(instruction.id == ARM_INS_SUB && isReg(instruction.detail->arm.operands[0], CSREG_DART_SP)))
			continue;
		if (i && fn.targets.contains(instruction.address) && !joins.contains(instruction.address))
			break;
		if (floatingConstant(i) || typeArgumentDiamond(i) || defaultDiamond(i))
			continue;
		const auto begin = instruction.address;
		if (!transfer(i))
			break;
		for (size_t r = 0; r < registers.size(); ++r) {
			const auto value = registers[r];
			if (value.kind == Context)
				fn.data.closureContextReg = Reg{static_cast<Reg::Value>(r)};
			if (value.kind == Value || value.kind == DoubleValue)
				fn.data.params[value.parameter].valReg = Reg{static_cast<Reg::Value>(r)};
		}
		InsnCursor spillCursor{fn.instructions, fn.targets, i};
		if (const auto memory = readMemory(spillCursor); memory && !memory->load) {
			const auto value = registers[memory->value];
			if (memory->base == CSREG_DART_FP && memory->offset < 0) {
				if (value.kind == Value || value.kind == DoubleValue)
					fn.data.params[value.parameter].localOffset = memory->offset;
				else if (value.kind == TypeArgsValue)
					fn.data.typeArgumentLocalOffset = memory->offset;
				else if (value.kind == Context)
					fn.data.closureContextLocalOffset = memory->offset;
			}
		}
		// Only consume proven argument loads; descriptor arithmetic and other
		// constants remain visible until their complete protocol is established.
		InsnCursor cursor{fn.instructions, fn.targets, i};
		const auto memory = readMemory(cursor);
		if (memory && memory->load && registers[memory->value].kind == Value)
			ranges.push_back({begin, instruction.address + 4});
	}
	if (inferredDeclaration && std::none_of(fn.data.params.params.begin(),
								   fn.data.params.params.end(),
								   [](const FnParamInfo& parameter) { return bool(parameter.val); }))
		fn.data.params = FnParams{};
	if (fn.data.params.empty())
		ranges.clear();
	ranges.insert(ranges.end(), typeArgumentRanges.begin(), typeArgumentRanges.end());
	// Publish each proved protocol as one span, not a copy of the complete
	// parameter list on every CMP/MOV/branch. Boundaries must already be IL
	// boundaries; a range never cuts an unrelated compound instruction.
	std::unordered_map<uint64_t, uint64_t> setups;
	for (const auto& range : ranges)
		setups[range.start] = range.end;
	std::vector<std::unique_ptr<ILInstr>> result;
	result.reserve(fn.data.il_insns.size());
	for (size_t i = 0; i < fn.data.il_insns.size(); ++i) {
		auto& il = fn.data.il_insns[i];
		const auto range = setups.find(il->Start());
		if (range != setups.end()) {
			size_t last = i;
			while (last + 1 < fn.data.il_insns.size() && fn.data.il_insns[last]->End() < range->second)
				++last;
			if (fn.data.il_insns[last]->End() == range->second) {
				result.push_back(std::make_unique<SetupParametersInstr>(
					AddrRange{il->Start(), range->second}, &fn.data.params));
				i = last;
				continue;
			}
		}
		result.push_back(std::move(il));
	}
	fn.data.il_insns = std::move(result);
	// Declaration completeness, default recovery and physical locations are
	// separate. Do not mark an optional signature complete from a partial path.
}

void FunctionAnalyzer::recoverParameters()
{
	// Prefer a surviving VM declaration over guesses from stack offsets.
	// Optional dispatch changes stack offsets, so only
	// fixed-arity declarations receive direct FP-slot bindings here.
	auto& function = data.dartFn;
	if (function.Ptr() == dart::Function::null())
		return;
	const auto& vm = dart::Function::Handle(function.Ptr());
	const auto& signature = dart::FunctionType::Handle(vm.signature());
	const bool accessor = function.Kind() == DartFunction::GETTER || function.Kind() == DartFunction::SETTER;
	if (signature.IsNull() && !accessor)
		return;
	const auto count = signature.IsNull()
						   ? vm.NumImplicitParameters() + (function.Kind() == DartFunction::SETTER)
						   : vm.NumParameters();
	if (count < 0 || count > UINT8_MAX)
		return;
	data.params.numFixedParam = signature.IsNull() ? count : vm.num_fixed_parameters();
	data.params.isNamedParam = !signature.IsNull() && vm.HasOptionalNamedParameters();
	const bool fixed = count == data.params.numFixedParam;
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
		if (fixed && data.useFramePointer) {
			const auto offset = (count - i + 1) * dart::kWordSize;
			for (const auto& incoming : data.incomingParameters) {
				if (incoming.paramOffset != offset)
					continue;
				parameter.paramOffset = offset;
				parameter.valReg = incoming.valReg;
				break;
			}
		}
		data.params.add(std::move(parameter));
	}
	// A declaration does not recover erased defaults or an optional entry path.
	data.params.isPartial = !fixed;
}

void FunctionAnalyzer::processPrologueParameters()
{
	// Fold only entry FP loads backed by a complete fixed-arity declaration.
	// Stack allocation/checks and unrelated prologue instructions remain IL.
	if (data.params.empty() || data.params.isPartial || !data.useFramePointer)
		return;
	size_t boundary = instructions.Count();
	for (size_t i = 0; i < instructions.Count(); ++i) {
		const auto* insn = instructions.Ptr(i);
		if (i && targets.contains(insn->address)) {
			boundary = i;
			break;
		}
		if (insn->id == ARM_INS_B || insn->id == ARM_INS_BL || insn->id == ARM_INS_BX ||
			insn->id == ARM_INS_BLX) {
			const bool stackCheck =
				std::any_of(data.il_insns.begin(), data.il_insns.end(), [&](const auto& il) {
					return il->Kind() == ILInstr::CheckStackOverflow && il->End() == insn->address + 4;
				});
			if (!stackCheck) {
				boundary = i;
				break;
			}
		}
	}
	if (!boundary)
		return;
	const auto end = instructions.Ptr(boundary - 1)->address + 4;
	for (size_t i = 0; i < data.il_insns.size(); ++i) {
		auto& il = data.il_insns[i];
		if (il->Start() >= end)
			break;
		if (il->Kind() != ILInstr::Unknown)
			continue;
		const auto index = data.asmTexts.AtIndex(il->Start());
		InsnCursor cursor{instructions, targets, index};
		const auto load = readMemory(cursor);
		if (!load || !load->load || load->base != CSREG_DART_FP || load->size != 4)
			continue;
		const bool parameter = std::any_of(data.params.params.begin(),
			data.params.params.end(),
			[&](const auto& item) { return item.paramOffset == load->offset && item.valReg == load->value; });
		if (!parameter)
			continue;
		il = std::make_unique<SetupParametersInstr>(il->Range(), &data.params);
		if (!i || targets.contains(il->Start()))
			continue;
		auto& previous = data.il_insns[i - 1];
		if (previous->Kind() != ILInstr::SetupParameters || previous->End() != il->Start())
			continue;
		previous =
			std::make_unique<SetupParametersInstr>(AddrRange{previous->Start(), il->End()}, &data.params);
		data.il_insns.erase(data.il_insns.begin() + i--);
	}
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processSaveRegisterInstr(InsnCursor& insn)
{
	// PushRegisters(FPU): reserve space, copy SP to IP, VSTMIA IP! pairs.
	// Prove the matching stub call and VPOP sequence before consuming a save.
	if (!insn.Is(ARM_INS_SUB, 3) || !isReg(insn.op(0), CSREG_DART_SP) || !isReg(insn.op(1), CSREG_DART_SP))
		return nullptr;
	if (insn.op(2).type != ARM_OP_IMM)
		return nullptr;
	const auto size = insn.op(2).imm;
	if (size <= 0 || size > 32 * 8 || size % 16)
		return nullptr;
	if (!insn.Next() || !insn.Is(ARM_INS_MOV, 2))
		return nullptr;
	if (!isReg(insn.op(0), ARM_REG_R12) || !isReg(insn.op(1), CSREG_DART_SP))
		return nullptr;
	std::vector<CpuRegister> regs;
	while (int(regs.size()) * 8 < size) {
		if (!insn.Next() || !insn.Is(ARM_INS_VSTMIA, 3) || !insn.detail().writeback)
			return nullptr;
		if (!isReg(insn.op(0), ARM_REG_R12))
			return nullptr;
		for (int j = 1; j <= 2; ++j) {
			const auto reg = insn.op(j).reg;
			if (insn.op(j).type != ARM_OP_REG || reg < ARM_REG_D0 || reg > ARM_REG_D31)
				return nullptr;
			Reg value{static_cast<arm_reg>(reg)};
			if (std::find(regs.begin(), regs.end(), value) != regs.end())
				return nullptr;
			regs.push_back(value);
		}
	}
	auto call = insn;
	if (!call.Next())
		return nullptr;
	const auto cpu = stackRegisters(*call.Current(), false);
	if (!cpu.empty() && !call.Next())
		return nullptr;
	if (!call.Is(ARM_INS_BL, 1) || call.op(0).type != ARM_OP_IMM)
		return nullptr;
	auto* fn = app.FindFunctionExact(uint32_t(call.op(0).imm));
	if (!fn || !fn->IsStub() || !call.Next())
		return nullptr;
	// Allocation slow paths can copy R0 out before restoring the saved CPU
	// set. The copy does not affect SP or the values being restored.
	if (call.Is(ARM_INS_MOV, 2) && call.op(0).type == ARM_OP_REG) {
		Reg destination{static_cast<arm_reg>(call.op(0).reg)};
		if (!destination.IsSet() || destination.IsDecimal() ||
			!isReg(call.op(1), ToCapstoneReg(dart::CallingConventions::kReturnReg)))
			return nullptr;
		if (!(dart::kDartAvailableCpuRegs & (1 << int(destination))) ||
			std::find(cpu.begin(), cpu.end(), destination) != cpu.end())
			return nullptr;
		if (!call.Next())
			return nullptr;
	}
	if (!cpu.empty()) {
		if (stackRegisters(*call.Current(), true) != cpu || !call.Next())
			return nullptr;
	}
	const auto restore = call.Current()->address;
	for (size_t j = 0; j < regs.size(); j += 2) {
		if (!call.Is(ARM_INS_VPOP, 2))
			return nullptr;
		if (Reg{static_cast<arm_reg>(call.op(0).reg)} != regs[j])
			return nullptr;
		if (Reg{static_cast<arm_reg>(call.op(1).reg)} != regs[j + 1])
			return nullptr;
		if (j + 2 < regs.size() && !call.Next())
			return nullptr;
	}
	fpuRestores.emplace(restore, SavedFpu{call.Range().end, regs});
	return std::make_unique<SaveRegisterInstr>(insn.Range(), std::move(regs));
}

std::unique_ptr<ILInstr> FunctionAnalyzer::processLoadSavedRegisterInstr(InsnCursor& insn)
{
	const auto saved = fpuRestores.find(insn.Current()->address);
	if (saved == fpuRestores.end())
		return nullptr;
	while (insn.Range().end < saved->second.end)
		if (!insn.Next())
			return nullptr;
	return std::make_unique<RestoreRegisterInstr>(insn.Range(), saved->second.regs);
}

void FunctionAnalyzer::processSavedRegisters()
{
	// PushRegisters/PopRegisters around a stub. Equal register lists and an
	// unchanged stack prove restoration; an ordinary argument push does not.
	// A slow-path result copy can precede restoration, as in the FPU scope.
	for (size_t i = 1; i + 1 < data.il_insns.size(); ++i) {
		const auto& call = data.il_insns[i];
		if (call->Kind() != ILInstr::Call)
			continue;
		auto* fn = static_cast<CallInstr&>(*call).GetFunction();
		if (!fn || !fn->IsStub() || targets.contains(call->Start()))
			continue;
		auto& save = data.il_insns[i - 1];
		if (save->Kind() != ILInstr::Unknown || save->End() != call->Start())
			continue;
		const auto* push = instructions.Ptr(data.asmTexts.AtIndex(save->Start()));
		auto registers = stackRegisters(*push, false);
		if (registers.empty())
			continue;
		size_t restoreIndex = i + 1;
		uint64_t restoreStart = call->End();
		if (data.il_insns[restoreIndex]->Kind() == ILInstr::MoveReg) {
			const auto& move = static_cast<MoveRegInstr&>(*data.il_insns[restoreIndex]);
			if (move.Start() != restoreStart || targets.contains(move.Start()))
				continue;
			if (move.srcReg != Reg{dart::CallingConventions::kReturnReg} || !move.dstReg.IsSet() ||
				move.dstReg.IsDecimal())
				continue;
			if (!(dart::kDartAvailableCpuRegs & (1 << int(move.dstReg))) ||
				std::find(registers.begin(), registers.end(), move.dstReg) != registers.end())
				continue;
			restoreStart = move.End();
			if (++restoreIndex == data.il_insns.size())
				continue;
		}
		auto& restore = data.il_insns[restoreIndex];
		if (restore->Kind() != ILInstr::Unknown || restore->Start() != restoreStart ||
			targets.contains(restoreStart))
			continue;
		const auto* pop = instructions.Ptr(data.asmTexts.AtIndex(restoreStart));
		if (stackRegisters(*pop, true) != registers)
			continue;
		save = std::make_unique<SaveRegisterInstr>(save->Range(), registers);
		restore = std::make_unique<RestoreRegisterInstr>(restore->Range(), std::move(registers));
	}
}

void FunctionAnalyzer::recoverRegisterParameters()
{
#if __has_include("vm/compiler/backend/dart_calling_conventions.h")
	// Modern AOT Dart uses r1/r2/r3/r8, not the native r0-r3 ABI. Kernel
	// unboxing metadata and the use_register_cc flag are erased from AOT, so
	// publish observed entry sources separately, without inventing ordinals.
	const auto& function = data.dartFn;
	if (function.Ptr() == dart::Function::null())
		return;
	const auto& vm = dart::Function::Handle(function.Ptr());
	if (!vm.IsRegularFunction() && vm.kind() != dart::UntaggedFunction::kConstructor &&
		function.Kind() != DartFunction::GETTER && function.Kind() != DartFunction::SETTER)
		return;
	const auto& signature = dart::FunctionType::Handle(vm.signature());
	if (!signature.IsNull() && vm.IsGeneric())
		return;
	std::array<Reg, Reg::kNumberOfRegisters> sources{};
	std::array<bool, Reg::kNumberOfRegisters> observed{};
	std::array<int32_t, Reg::kNumberOfRegisters> spills{};
	std::vector<Reg> incoming;
	for (auto reg : dart::DartCallingConvention::kCpuRegistersForArgs) {
		sources[Reg{reg}] = Reg{reg};
		incoming.push_back(Reg{reg});
	}
	// ARM allocates floating parameters in Q registers but accesses a double
	// through the even D register. Track overlapping S/D/Q writes together.
	for (auto reg : dart::DartCallingConvention::kFpuRegistersForArgs) {
		const int group = int(reg);
		const Reg value{static_cast<Reg::Value>(Reg::D0 + group * 2)};
		incoming.push_back(value);
		sources[value] = value;
		sources[Reg::Q0 + group] = value;
		if (group < 8) {
			sources[Reg::S0 + group * 4] = value;
			sources[Reg::S0 + group * 4 + 1] = value;
		}
	}
	std::unordered_set<uint64_t> stackChecks;
	for (const auto& il : data.il_insns)
		if (il->Kind() == ILInstr::CheckStackOverflow)
			stackChecks.insert(il->End() - 4);
	for (size_t i = 0; i < instructions.Count(); ++i) {
		const auto& instruction = *instructions.Ptr(i);
		if (i && targets.contains(instruction.address))
			break;
		const auto& arm = instruction.detail->arm;
		if (stackChecks.contains(instruction.address))
			continue;
		if (!isUnconditional(instruction))
			break;
		const auto* groups = instruction.detail->groups;
		if (std::any_of(groups, groups + instruction.detail->groups_count, [](uint8_t group) {
				return group == CS_GRP_JUMP || group == CS_GRP_CALL || group == CS_GRP_RET;
			}))
			break;
		const auto read = [&](int capstone) {
			Reg reg{static_cast<arm_reg>(capstone)};
			if (reg.IsSet() && sources[reg].IsSet())
				observed[sources[reg]] = true;
		};
		// XOR/subtract of the same unshifted value is a zeroing idiom, not
		// evidence of an incoming argument (notably VEOR Q0,Q0,Q0).
		const bool zero = (instruction.id == ARM_INS_EOR || instruction.id == ARM_INS_VEOR ||
							  instruction.id == ARM_INS_SUB) &&
						  arm.op_count == 3 && arm.operands[1].type == ARM_OP_REG &&
						  isReg(arm.operands[2], arm.operands[1].reg) &&
						  arm.operands[1].shift.type == ARM_SFT_INVALID;
		for (unsigned j = 0; j < arm.op_count; ++j) {
			const auto& op = arm.operands[j];
			if (!zero && op.type == ARM_OP_REG && (op.access & CS_AC_READ))
				read(op.reg);
			if (op.type == ARM_OP_MEM) {
				read(op.mem.base);
				read(op.mem.index);
			}
		}
		InsnCursor cursor{instructions, targets, i};
		const auto memory = readMemory(cursor);
		if (memory && !memory->load && memory->base == CSREG_DART_FP &&
			(memory->size == dart::kWordSize || (memory->size == 8 && memory->value.IsDecimal()))) {
			const auto source = sources[memory->value];
			if (source.IsSet() && memory->offset < 0)
				spills[source] = memory->offset;
		}
		Reg moved;
		if (cursor.Is(ARM_INS_MOV, 2) && arm.operands[1].type == ARM_OP_REG) {
			Reg source{static_cast<arm_reg>(arm.operands[1].reg)};
			if (source.IsSet() && arm.operands[1].shift.type == ARM_SFT_INVALID)
				moved = sources[source];
		}
		for (unsigned j = 0; j < arm.op_count; ++j) {
			const auto& op = arm.operands[j];
			Reg reg{static_cast<arm_reg>(op.reg)};
			if (op.type != ARM_OP_REG || !reg.IsSet() || !(op.access & CS_AC_WRITE))
				continue;
			if (!reg.IsDecimal()) {
				sources[reg].Clear();
				continue;
			}
			if (reg >= Reg{Reg::Q0}) {
				const int group = int(reg) - Reg::Q0;
				sources[reg].Clear();
				sources[Reg::D0 + group * 2].Clear();
				sources[Reg::D0 + group * 2 + 1].Clear();
				if (group < 8)
					for (int lane = 0; lane < 4; ++lane)
						sources[Reg::S0 + group * 4 + lane].Clear();
			} else if (reg >= Reg{Reg::S0}) {
				const int lane = int(reg) - Reg::S0;
				sources[reg].Clear();
				sources[Reg::D0 + lane / 2].Clear();
				sources[Reg::Q0 + lane / 4].Clear();
			} else {
				const int lane = int(reg) - Reg::D0;
				sources[reg].Clear();
				sources[Reg::Q0 + lane / 2].Clear();
				if (lane < 16) {
					sources[Reg::S0 + lane * 2].Clear();
					sources[Reg::S0 + lane * 2 + 1].Clear();
				}
			}
		}
		if (moved.IsSet())
			sources[Reg{static_cast<arm_reg>(arm.operands[0].reg)}] = moved;
	}
	for (auto reg : incoming) {
		if (!observed[reg])
			continue;
		FnParamInfo parameter;
		parameter.paramReg = Reg{reg};
		parameter.localOffset = spills[Reg{reg}];
		parameter.name = std::string("arg_") + Reg{reg}.Name();
		data.incomingParameters.push_back(std::move(parameter));
	}
#endif
}

void FunctionAnalyzer::recoverIncomingParameters()
{
	// Observe stack entry loads independently of modern register arguments.
	// Record observed entry loads, without inferring arity from the largest
	// offset: signatures and optional-argument dispatch may be trimmed in AOT.
	if (!data.useFramePointer)
		return;
	uint64_t frameEnd = 0;
	std::unordered_set<uint64_t> stackChecks;
	for (const auto& il : data.il_insns) {
		if (!frameEnd && il->Kind() == ILInstr::EnterFrame)
			frameEnd = il->End();
		if (il->Kind() == ILInstr::CheckStackOverflow)
			stackChecks.insert(il->End() - 4);
	}
	for (size_t i = 0; i < instructions.Count(); ++i) {
		const auto& insn = *instructions.Ptr(i);
		if (i && targets.contains(insn.address))
			break;
		if (stackChecks.contains(insn.address))
			continue;
		if (insn.id == ARM_INS_B || insn.id == ARM_INS_BL || insn.id == ARM_INS_BX || insn.id == ARM_INS_BLX)
			break;
		if (insn.address < frameEnd)
			continue;
		InsnCursor cursor{instructions, targets, i};
		const auto memory = readMemory(cursor);
		if (!memory || !memory->load || memory->size != 4 || memory->base != CSREG_DART_FP)
			continue;
		if (memory->offset < 8 || memory->offset % 4 || memory->value.IsDecimal())
			continue;
		FnParamInfo parameter{memory->value};
		parameter.paramOffset = memory->offset;
		data.incomingParameters.push_back(std::move(parameter));
	}
}

const FunctionAnalyzer::Matcher FunctionAnalyzer::matchers[] = {
	&FunctionAnalyzer::processEnterFrameInstr,
	&FunctionAnalyzer::processLeaveFrameInstr,
	&FunctionAnalyzer::processSaveRegisterInstr,
	&FunctionAnalyzer::processLoadSavedRegisterInstr,
	&FunctionAnalyzer::processAllocateStackInstr,
	&FunctionAnalyzer::processCheckStackOverflowInstr,
	&FunctionAnalyzer::processInitAsyncInstr,
	&FunctionAnalyzer::processInitLateStaticFieldInstr,
	&FunctionAnalyzer::processInlineTypeTestInstr,
	&FunctionAnalyzer::processTypeTestInstr,
	&FunctionAnalyzer::processTryAllocateObjectInstr,
	&FunctionAnalyzer::processWriteBarrierInstr,
	&FunctionAnalyzer::processTailCallInstr,
	&FunctionAnalyzer::processBoxInt64Instr,
	&FunctionAnalyzer::processTaggedClassIdInstr,
	&FunctionAnalyzer::processUnboxIntInstr,
	&FunctionAnalyzer::processLoadClassIdInstr,
	&FunctionAnalyzer::processBranchIfSmiInstr,
	&FunctionAnalyzer::processLoadFieldTableInstr,
	&FunctionAnalyzer::processClosureCallInstr,
	&FunctionAnalyzer::processGdtCallInstr,
	&FunctionAnalyzer::processPoolCallInstr,
	&FunctionAnalyzer::processCallLeafRuntimeInstr,
	&FunctionAnalyzer::processCallInstr,
	&FunctionAnalyzer::processObjectPoolInstr,
	&FunctionAnalyzer::processStorePoolInstr,
	&FunctionAnalyzer::processReturnInstr,
	&FunctionAnalyzer::processMoveRegInstr,
	&FunctionAnalyzer::processLoadValueInstr,
	&FunctionAnalyzer::processLoadStore,
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
		if (unbox.highReg.IsSet())
			nonObjects[unbox.highReg] = true;
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
	recoverIncomingParameters();
	recoverRegisterParameters();
	recoverParameters();
	ArmParameterRecovery{*this}.Recover();
	processPrologueParameters();
	processSavedRegisters();
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
