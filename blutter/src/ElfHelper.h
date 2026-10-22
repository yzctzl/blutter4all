#pragma once
#include <stdint.h>
#include <memory>

struct LibAppInfo {
	const void* lib;
	const uint8_t* vm_snapshot_data;
	const uint8_t* vm_snapshot_instructions;
	const uint8_t* isolate_snapshot_data;
	const uint8_t* isolate_snapshot_instructions;
	std::shared_ptr<void> owner; // Optional mapping ownership; must outlive the VM.
};

class ElfHelper final
{
public:
	static LibAppInfo MapLibAppSo(const char* path);

private:
	ElfHelper() = delete;
};
