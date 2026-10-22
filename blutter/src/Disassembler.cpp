#include "pch.h"
#include "Disassembler.h"

AsmInstructions Disassembler::Disasm(const uint8_t* code, size_t code_size, uint64_t address, size_t max_count)
{
	cs_insn* insns = NULL;
	size_t insn_cnt = 0;

	insn_cnt = cs_disasm(cshandle, code, code_size, address, max_count, &insns);

#if defined(TARGET_ARCH_X64)
    if (code_size && (!max_count || insn_cnt < max_count) && (!insn_cnt || insns[insn_cnt - 1].address + insns[insn_cnt - 1].size != address + code_size)) {
        cs_free(insns, insn_cnt);
        throw std::runtime_error(std::format("Incomplete x64 disassembly at {:#x} ({} bytes)", address, code_size));
    }
#endif
	return AsmInstructions(insns, insn_cnt);
}