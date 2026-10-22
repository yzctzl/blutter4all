#pragma once

// Register numbering comes from Dart SDK runtime/vm/constants_x64.h.
// Capstone subregisters share an identity here; this does not imply that a
// partial register write preserves a pointer. The analyzer invalidates the
// corresponding object fact on every register write, including AL/EAX writes.
namespace X64 {
class Register
{
public:
	enum Value : int32_t {
		RAX = 0,
		RCX = 1,
		RDX = 2,
		RBX = 3,
		RSP = 4,
		RBP = 5,
		RSI = 6,
		RDI = 7,
		R8 = 8,
		R9 = 9,
		R10 = 10,
		R11 = 11,
		R12 = 12,
		R13 = 13,
		R14 = 14,
		R15 = 15,
		XMM0 = 16,
		kNumberOfRegisters = 32,
		kNoRegister = -1,
	};
	constexpr Register() : reg(kNoRegister) {}
	constexpr Register(Value value) : reg(value) {}
	constexpr Register(dart::Register value) : reg(static_cast<Value>(value)) {}
	constexpr Register(x86_reg value) : reg(kNoRegister)
	{
		switch (value) {
		case X86_REG_RAX:
		case X86_REG_EAX:
		case X86_REG_AX:
		case X86_REG_AL:
		case X86_REG_AH:
			reg = RAX;
			break;
		case X86_REG_RCX:
		case X86_REG_ECX:
		case X86_REG_CX:
		case X86_REG_CL:
		case X86_REG_CH:
			reg = RCX;
			break;
		case X86_REG_RDX:
		case X86_REG_EDX:
		case X86_REG_DX:
		case X86_REG_DL:
		case X86_REG_DH:
			reg = RDX;
			break;
		case X86_REG_RBX:
		case X86_REG_EBX:
		case X86_REG_BX:
		case X86_REG_BL:
		case X86_REG_BH:
			reg = RBX;
			break;
		case X86_REG_RSP:
		case X86_REG_ESP:
		case X86_REG_SP:
		case X86_REG_SPL:
			reg = RSP;
			break;
		case X86_REG_RBP:
		case X86_REG_EBP:
		case X86_REG_BP:
		case X86_REG_BPL:
			reg = RBP;
			break;
		case X86_REG_RSI:
		case X86_REG_ESI:
		case X86_REG_SI:
		case X86_REG_SIL:
			reg = RSI;
			break;
		case X86_REG_RDI:
		case X86_REG_EDI:
		case X86_REG_DI:
		case X86_REG_DIL:
			reg = RDI;
			break;
		case X86_REG_R8:
		case X86_REG_R8D:
		case X86_REG_R8W:
		case X86_REG_R8B:
			reg = R8;
			break;
		case X86_REG_R9:
		case X86_REG_R9D:
		case X86_REG_R9W:
		case X86_REG_R9B:
			reg = R9;
			break;
		case X86_REG_R10:
		case X86_REG_R10D:
		case X86_REG_R10W:
		case X86_REG_R10B:
			reg = R10;
			break;
		case X86_REG_R11:
		case X86_REG_R11D:
		case X86_REG_R11W:
		case X86_REG_R11B:
			reg = R11;
			break;
		case X86_REG_R12:
		case X86_REG_R12D:
		case X86_REG_R12W:
		case X86_REG_R12B:
			reg = R12;
			break;
		case X86_REG_R13:
		case X86_REG_R13D:
		case X86_REG_R13W:
		case X86_REG_R13B:
			reg = R13;
			break;
		case X86_REG_R14:
		case X86_REG_R14D:
		case X86_REG_R14W:
		case X86_REG_R14B:
			reg = R14;
			break;
		case X86_REG_R15:
		case X86_REG_R15D:
		case X86_REG_R15W:
		case X86_REG_R15B:
			reg = R15;
			break;
		default:
			if (value >= X86_REG_XMM0 && value <= X86_REG_XMM15)
				reg = static_cast<Value>(int(XMM0) + int(value) - int(X86_REG_XMM0));
		}
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
		return reg >= XMM0 && reg < kNumberOfRegisters;
	}
	void Clear()
	{
		reg = kNoRegister;
	}
	const char* Name() const;
	constexpr operator int() const
	{
		return reg;
	}

private:
	Value reg;
};
} // namespace X64

constexpr x86_reg CSREG_DART_THR = X86_REG_R14;
constexpr x86_reg CSREG_DART_PP = X86_REG_R15;
static_assert(dart::THR == dart::R14 && dart::PP == dart::R15);
static_assert(dart::FPREG == dart::RBP && dart::SPREG == dart::RSP);

class AsmInstruction
{
	cs_insn* insn;

public:
	const cs_x86_op* ops;
	explicit AsmInstruction(cs_insn* insn) : insn(insn), ops(insn->detail->x86.operands) {}
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
		return insn->detail->x86.op_count;
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
		return ops[i].type == X86_OP_MEM ? ops[i].mem.base : X86_REG_INVALID;
	}
};
