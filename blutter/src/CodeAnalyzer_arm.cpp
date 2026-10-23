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
	std::unique_ptr<ILInstr> processLoadClassIdInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processBranchIfSmiInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processCallInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processPoolCallInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processCallLeafRuntimeInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processGdtCallInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processClosureCallInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processUnboxIntInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processInitAsyncInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processTypeTestInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processInlineTypeTestInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processTryAllocateObjectInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processTailCallInstr(InsnCursor& insn);
	LoadValueInstr* previousLoad(const InsnCursor& insn);
	std::unique_ptr<ILInstr> processBoxInt64Instr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processTaggedClassIdInstr(InsnCursor& insn);
	void processSavedRegisters();
	std::unique_ptr<ILInstr> processSaveRegisterInstr(InsnCursor& insn);
	std::unique_ptr<ILInstr> processLoadSavedRegisterInstr(InsnCursor& insn);
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

const FunctionAnalyzer::Matcher FunctionAnalyzer::matchers[] = {
	&FunctionAnalyzer::processEnterFrameInstr,
	&FunctionAnalyzer::processLeaveFrameInstr,
	&FunctionAnalyzer::processSaveRegisterInstr,
	&FunctionAnalyzer::processLoadSavedRegisterInstr,
	&FunctionAnalyzer::processAllocateStackInstr,
	&FunctionAnalyzer::processCheckStackOverflowInstr,
	&FunctionAnalyzer::processInitAsyncInstr,
	&FunctionAnalyzer::processInlineTypeTestInstr,
	&FunctionAnalyzer::processTypeTestInstr,
	&FunctionAnalyzer::processTryAllocateObjectInstr,
	&FunctionAnalyzer::processTailCallInstr,
	&FunctionAnalyzer::processBoxInt64Instr,
	&FunctionAnalyzer::processTaggedClassIdInstr,
	&FunctionAnalyzer::processUnboxIntInstr,
	&FunctionAnalyzer::processLoadClassIdInstr,
	&FunctionAnalyzer::processBranchIfSmiInstr,
	&FunctionAnalyzer::processClosureCallInstr,
	&FunctionAnalyzer::processGdtCallInstr,
	&FunctionAnalyzer::processPoolCallInstr,
	&FunctionAnalyzer::processCallLeafRuntimeInstr,
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
