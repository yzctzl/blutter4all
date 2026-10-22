#pragma once
#include "ElfHelper.h"

// Offline mapping of ARM64/x64 Dart snapshot dylibs. No dyld calls or
// target code execution; the returned owner keeps the writable image alive.
class MachOHelper final {
public:
	static bool IsMachO(const char* path);
	static LibAppInfo MapLibApp(const char* path);
};
