#include "pch.h"
#include "Disassembler.h"

const char* ARM::Register::Name() const
{
	static const auto names = [] {
		std::array<std::string, kNumberOfRegisters> result;
		for (int r = 0; r < 16; ++r)
			result[r] = "r" + std::to_string(r);
		result[dart::THR] = "rTHR";
		result[dart::PP] = "rPP";
		result[dart::SPREG] = "rSP";
		result[dart::FPREG] = "rFP";
		for (int r = 0; r < 32; ++r) {
			result[D0 + r] = "d" + std::to_string(r);
			result[S0 + r] = "s" + std::to_string(r);
		}
		for (int r = 0; r < 16; ++r)
			result[Q0 + r] = "q" + std::to_string(r);
		return result;
	}();
	return IsSet() ? names[reg].c_str() : "unknown";
}

Disassembler::Disassembler(bool hasDetail)
{
	// Dart's ARM backend emits A32, not Thumb, including armeabi-v7a AOT.
	if (cs_open(CS_ARCH_ARM, CS_MODE_ARM, &cshandle) != CS_ERR_OK)
		throw std::runtime_error("Cannot open ARM capstone engine");
	if (hasDetail)
		cs_option(cshandle, CS_OPT_DETAIL, CS_OPT_ON);
}
