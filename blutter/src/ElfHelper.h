#pragma once
#include <stdint.h>
#include <memory>

// Offline, writable image. Target virtual address A is stored at lib + A;
// loaders only accept zero-based images and keep file offsets private.
struct LibAppInfo {
	const void* lib;
	const uint8_t* vm_snapshot_data;
	const uint8_t* vm_snapshot_instructions;
	const uint8_t* isolate_snapshot_data;
	const uint8_t* isolate_snapshot_instructions;
	std::shared_ptr<void> owner; // Must outlive the Dart VM.
};

class ElfHelper final
{
public:
	static LibAppInfo MapLibAppSo(const char* path);

private:
	ElfHelper() = delete;
};
