#pragma once

namespace ARM
{
// Keep scalar S and D views distinct: a write to S0 does not define a double D0.
class Register
{
public:
	enum Value : int32_t {
		R0 = 0,
		R15 = 15,
		D0 = 16,
		S0 = 48,
		Q0 = 80,
		kNumberOfRegisters = 96,
		kNoRegister = -1
	};
	constexpr Register() : reg(kNoRegister)
	{
	}
	constexpr Register(Value value) : reg(value)
	{
	}
	constexpr Register(dart::Register value) : reg(static_cast<Value>(value))
	{
	}
	constexpr Register(arm_reg value) : reg(kNoRegister)
	{
		if (value >= ARM_REG_R0 && value <= ARM_REG_R12)
			reg = static_cast<Value>(value - ARM_REG_R0);
		else if (value == ARM_REG_SP)
			reg = static_cast<Value>(13);
		else if (value == ARM_REG_LR)
			reg = static_cast<Value>(14);
		else if (value == ARM_REG_PC)
			reg = R15;
		else if (value >= ARM_REG_D0 && value <= ARM_REG_D31)
			reg = static_cast<Value>(int(D0) + int(value) - ARM_REG_D0);
		else if (value >= ARM_REG_S0 && value <= ARM_REG_S31)
			reg = static_cast<Value>(int(S0) + int(value) - ARM_REG_S0);
		else if (value >= ARM_REG_Q0 && value <= ARM_REG_Q15)
			reg = static_cast<Value>(int(Q0) + int(value) - ARM_REG_Q0);
	}
	constexpr bool operator==(Register other) const
	{
		return reg == other.reg;
	}
	constexpr bool operator!=(Register other) const
	{
		return reg != other.reg;
	}
	constexpr bool IsSet() const
	{
		return reg != kNoRegister;
	}
	constexpr bool IsDecimal() const
	{
		return reg >= D0;
	}
	void Clear()
	{
		reg = kNoRegister;
	}
	constexpr operator int() const
	{
		return reg;
	}
	const char* Name() const;

private:
	Value reg;
};
} // namespace ARM

constexpr arm_reg ToCapstoneReg(dart::Register reg)
{
	if (reg >= dart::R0 && reg <= dart::R12)
		return static_cast<arm_reg>(int(ARM_REG_R0) + int(reg));
	if (reg == dart::SP)
		return ARM_REG_SP;
	if (reg == dart::R14)
		return ARM_REG_LR;
	if (reg == dart::PC)
		return ARM_REG_PC;
	return ARM_REG_INVALID;
}
constexpr arm_reg CSREG_DART_THR = ToCapstoneReg(dart::THR);
constexpr arm_reg CSREG_DART_PP = ToCapstoneReg(dart::PP);
constexpr arm_reg CSREG_DART_FP = ToCapstoneReg(dart::FPREG);
constexpr arm_reg CSREG_DART_SP = ToCapstoneReg(dart::SPREG);
static_assert(dart::THR == dart::R10 && dart::PP == dart::R5 && dart::SPREG == dart::SP);
static_assert(sizeof(void*) == 4, "ARM snapshots require a 32-bit Dart runtime");

class AsmInstruction
{
	cs_insn* insn;

public:
	const cs_arm_op* ops;
	explicit AsmInstruction(cs_insn* insn) : insn(insn), ops(insn->detail->arm.operands)
	{
	}
	cs_insn* ptr() const
	{
		return insn;
	}
	uint64_t address() const
	{
		return insn->address;
	}
	uint16_t size() const
	{
		return insn->size;
	}
	uint64_t NextAddress() const
	{
		return address() + size();
	}
	unsigned id() const
	{
		return insn->id;
	}
	uint8_t op_count() const
	{
		return insn->detail->arm.op_count;
	}
	const char* mnemonic() const
	{
		return insn->mnemonic;
	}
	const char* op_str() const
	{
		return insn->op_str;
	}
	unsigned MemoryBase(size_t i) const
	{
		return ops[i].type == ARM_OP_MEM ? ops[i].mem.base : ARM_REG_INVALID;
	}
};
