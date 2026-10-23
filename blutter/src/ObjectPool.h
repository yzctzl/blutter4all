#pragma once

// Shared analysis stores offsets from the untagged pool object. SDK
// IndexFromOffset instead accepts a tagged-pointer displacement. Keep the
// conversion explicit; integer division must not hide a misaligned offset.
inline intptr_t PoolIndexFromOffset(intptr_t offset) {
    return dart::ObjectPool::IndexFromOffset(offset - dart::kHeapObjectTag);
}

#if defined(TARGET_ARCH_X64) || defined(TARGET_ARCH_ARM)
constexpr intptr_t kPoolPointerTag = dart::kHeapObjectTag;
#else
constexpr intptr_t kPoolPointerTag = 0;
#endif

#if defined(TARGET_ARCH_X64) || defined(TARGET_ARCH_ARM)
constexpr intptr_t kUnlinkedCallTargetDelta = -1;
#else
constexpr intptr_t kUnlinkedCallTargetDelta = 1;
#endif

inline intptr_t PoolInstructionOffset(intptr_t offset) {
    return offset - kPoolPointerTag;
}

inline intptr_t UnlinkedCallTargetIndex(intptr_t index) {
    return index + kUnlinkedCallTargetDelta;
}
