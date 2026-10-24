#include "pch.h"
#include "Disassembler.h"

AsmInstructions Disassembler::Disasm(const uint8_t* code, size_t code_size, uint64_t address, size_t max_count)
{
	cs_insn* insns = nullptr;
	const auto insn_cnt = cs_disasm(cshandle, code, code_size, address, max_count, &insns);
	const auto decoded = insn_cnt ? insns[insn_cnt - 1].address - address + insns[insn_cnt - 1].size : 0;
	// A bounded preview may stop at its instruction limit. Full decoding must
	// cover the requested range, including on fixed-width architectures.
	if ((!max_count || insn_cnt < max_count) && decoded != code_size) {
		cs_free(insns, insn_cnt);
		throw std::runtime_error(std::format("Incomplete disassembly at {:#x}: decoded {} of {} bytes (stopped at {:#x})",
			address, decoded, code_size, address + decoded));
	}
	return AsmInstructions(insns, insn_cnt);
}
