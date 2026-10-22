#include "ElfHelper.h"
#include <algorithm>
#include <array>
#include <cstring>
#include <fstream>
#include <new>
#include <span>
#include <stdexcept>
#include <string>
#include <string_view>
#include <vector>

// ELF64 layouts: Dart SDK runtime/platform/elf.h. Build a virtual image,
// not a file mapping: PT_LOAD offsets can differ and BSS has no file bytes.
namespace {
void Require(bool ok, const char* message) {
    if (!ok) throw std::invalid_argument(std::string("ELF: ") + message);
}
struct Reader {
    std::span<const uint8_t> bytes;
    std::span<const uint8_t> Range(uint64_t offset, uint64_t size) const {
        Require(offset <= bytes.size() && size <= bytes.size() - offset, "Read outside file");
        return bytes.subspan(static_cast<size_t>(offset), static_cast<size_t>(size));
    }
    uint16_t U16(uint64_t offset) const {
        auto b = Range(offset, 2); return uint16_t(b[0]) | uint16_t(b[1]) << 8;
    }
    uint32_t U32(uint64_t offset) const { return U16(offset) | uint32_t(U16(offset + 2)) << 16; }
    uint64_t U64(uint64_t offset) const { return U32(offset) | uint64_t(U32(offset + 4)) << 32; }
};
struct Segment { uint64_t address, offset, fileSize, size; };
constexpr uint64_t kMaxImageSize = uint64_t{1} << 30;
constexpr size_t kAlignment = 0x10000;
}

LibAppInfo ElfHelper::MapLibAppSo(const char* path)
{
    std::ifstream input(path, std::ios::binary | std::ios::ate);
    Require(bool(input), "Cannot open input");
    const auto length = input.tellg();
    Require(length >= 64, "Truncated header");
    std::vector<uint8_t> bytes(static_cast<size_t>(length));
    input.seekg(0);
    Require(bool(input.read(reinterpret_cast<char*>(bytes.data()), length)), "Truncated input");
    const Reader file{bytes};
    Require(std::memcmp(bytes.data(), "\x7f" "ELF", 4) == 0, "Invalid magic");
    Require(bytes[4] == 2 && bytes[5] == 1 && bytes[6] == 1, "Expected little-endian ELF64");
    Require(file.U16(16) == 3 && file.U32(20) == 1 && file.U16(52) == 64, "Invalid shared-object header");
#if defined(TARGET_ARCH_X64)
    Require(file.U16(18) == 62, "Expected x64 target");
#else
    Require(file.U16(18) == 183, "Expected ARM64 target");
#endif
    const auto phoff = file.U64(32), shoff = file.U64(40);
    const auto phnum = file.U16(56), shnum = file.U16(60);
    Require(file.U16(54) == 56 && file.U16(58) == 64 && phnum != 0 && shnum != 0,
            "Invalid program or section table");
    file.Range(phoff, uint64_t(phnum) * 56);
    file.Range(shoff, uint64_t(shnum) * 64);
    std::vector<Segment> segments;
    for (uint32_t i = 0; i < phnum; ++i) {
        const auto at = phoff + uint64_t(i) * 56;
        if (file.U32(at) != 1) continue; // PT_LOAD
        Segment s{file.U64(at + 16), file.U64(at + 8), file.U64(at + 32), file.U64(at + 40)};
        Require(s.fileSize <= s.size, "Segment file size exceeds memory size");
        file.Range(s.offset, s.fileSize);
        Require(s.address <= kMaxImageSize && s.size <= kMaxImageSize - s.address,
                "Image exceeds supported 1 GiB virtual range");
        if (s.size != 0) segments.push_back(s);
    }
    Require(!segments.empty(), "Missing loadable segments");
    std::sort(segments.begin(), segments.end(), [](const auto& a, const auto& b) { return a.address < b.address; });
    Require(segments.front().address == 0, "Only zero-based snapshot images are supported");
    uint64_t imageSize = 0;
    for (const auto& s : segments) {
        Require(s.address >= imageSize, "Overlapping virtual segments");
        imageSize = s.address + s.size;
    }
    constexpr std::array<std::string_view, 4> names{
        "_kDartVmSnapshotData", "_kDartVmSnapshotInstructions",
        "_kDartIsolateSnapshotData", "_kDartIsolateSnapshotInstructions"};
    std::array<uint64_t, 4> addresses{};
    std::array<bool, 4> found{};
    for (uint32_t i = 0; i < shnum; ++i) {
        const auto at = shoff + uint64_t(i) * 64;
        if (file.U32(at + 4) != 11) continue; // SHT_DYNSYM
        const auto offset = file.U64(at + 24), size = file.U64(at + 32);
        const auto link = file.U32(at + 40);
        Require(file.U64(at + 56) == 24 && size % 24 == 0 && link < shnum, "Invalid dynamic symbol table");
        file.Range(offset, size);
        const auto str = shoff + uint64_t(link) * 64;
        Require(file.U32(str + 4) == 3, "Invalid linked string table");
        const auto stringsOffset = file.U64(str + 24), stringsSize = file.U64(str + 32);
        file.Range(stringsOffset, stringsSize);
        for (uint64_t index = 0; index < size / 24; ++index) {
            const auto sym = offset + index * 24;
            if (file.U16(sym + 6) == 0) continue; // SHN_UNDEF
            const auto nameOffset = file.U32(sym);
            Require(nameOffset < stringsSize, "Invalid symbol string offset");
            auto text = file.Range(stringsOffset + nameOffset, stringsSize - nameOffset);
            const auto* end = static_cast<const uint8_t*>(std::memchr(text.data(), 0, text.size()));
            Require(end != nullptr, "Unterminated symbol name");
            const auto match = std::find(names.begin(), names.end(),
                std::string_view(reinterpret_cast<const char*>(text.data()), end - text.data()));
            if (match == names.end()) continue;
            const auto n = static_cast<size_t>(match - names.begin());
            Require(!found[n], "Duplicate snapshot symbol");
            const auto address = file.U64(sym + 8);
            const uint64_t required = n % 2 == 0 ? 53 : 16;
            const auto segment = std::find_if(segments.begin(), segments.end(), [&](const auto& s) {
                return address >= s.address && address - s.address <= s.fileSize && required <= s.fileSize - (address - s.address);
            });
            Require(segment != segments.end() && address % 16 == 0, "Snapshot is unaligned or not file backed");
            const auto data = segment->offset + address - segment->address;
            const auto remaining = segment->fileSize - (address - segment->address);
            if (n % 2 == 0) {
                Require(file.U32(data) == 0xdcdcf5f5, "Invalid snapshot magic");
                const auto snapshotSize = file.U64(data + 4);
                Require(snapshotSize >= 49 && snapshotSize <= remaining - 4, "Invalid snapshot length");
                auto flags = file.Range(data + 52, snapshotSize + 4 - 52);
                Require(std::memchr(flags.data(), 0, flags.size()) != nullptr, "Unterminated snapshot flags");
            } else {
                Require(file.U64(data) >= 16 && file.U64(data) <= remaining, "Invalid instruction image length");
            }
            addresses[n] = address; found[n] = true;
        }
    }
    Require(std::all_of(found.begin(), found.end(), [](bool v) { return v; }), "Missing Dart snapshot symbols");
    std::shared_ptr<void> owner(::operator new(static_cast<size_t>(imageSize), std::align_val_t{kAlignment}),
        [](void* p) { ::operator delete(p, std::align_val_t{kAlignment}); });
    auto* image = static_cast<uint8_t*>(owner.get());
    std::memset(image, 0, static_cast<size_t>(imageSize));
    for (const auto& s : segments)
        if (s.fileSize) std::memcpy(image + s.address, file.Range(s.offset, s.fileSize).data(), static_cast<size_t>(s.fileSize));
    return LibAppInfo{image, image + addresses[0], image + addresses[1], image + addresses[2], image + addresses[3], std::move(owner)};
}
