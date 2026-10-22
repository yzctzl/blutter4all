#include "pch.h"
#include "Disassembler.h"

const char* X64::Register::Name() const
{
	static constexpr const char* names[] = {
		"rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi",
		"r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15",
		"xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7",
		"xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15"
	};
	return IsSet() ? names[reg] : "unknown";
}

Disassembler::Disassembler(bool hasDetail)
{
	if (cs_open(CS_ARCH_X86, CS_MODE_64, &cshandle) != CS_ERR_OK)
		throw std::runtime_error("Cannot open x64 capstone engine");
	if (hasDetail)
		cs_option(cshandle, CS_OPT_DETAIL, CS_OPT_ON);
}
