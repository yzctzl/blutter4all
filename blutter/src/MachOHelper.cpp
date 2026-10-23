#include "MachOHelper.h"
#include <algorithm>
#include <array>
#include <cstring>
#include <fstream>
#include <limits>
#include <new>
#include <span>
#include <stdexcept>
#include <string>
#include <string_view>
#include <vector>

// Layout references: Dart SDK runtime/platform/mach_o.h and
// runtime/bin/macho_loader.cc. Keep this reader independent of SDK headers:
// older SDKs (including our iOS fixture's 2.19.6) have no Mach-O header.
namespace {
#if defined(TARGET_ARCH_X64)
constexpr uint32_t kTargetCpu = 0x01000007;
constexpr uint32_t kTargetSubtype = 3;
#else
constexpr uint32_t kTargetCpu = 0x0100000c;
constexpr uint32_t kTargetSubtype = 0;
#endif
constexpr uint32_t kMach64 = 0xfeedfacf;
constexpr uint32_t kFat = 0xcafebabe;
constexpr size_t kAlignment = 0x10000;
// Bound allocations when inspecting untrusted headers. This is a supported
// image-size limit, not an inference about a snapshot's validity.
constexpr uint64_t kMaxImageSize = uint64_t{1} << 30;

void Require(bool ok, const char* message)
{
	if (!ok)
		throw std::invalid_argument(std::string("Mach-O: ") + message);
}

struct Reader {
	std::span<const uint8_t> bytes;

	std::span<const uint8_t> Range(uint64_t offset, uint64_t size) const {
		Require(offset <= bytes.size() && size <= bytes.size() - offset, "Read outside image or selected slice");
		return bytes.subspan(static_cast<size_t>(offset), static_cast<size_t>(size));
	}
	uint32_t U32(uint64_t offset) const {
		auto b = Range(offset, 4);
		return uint32_t(b[0]) | uint32_t(b[1]) << 8 | uint32_t(b[2]) << 16 | uint32_t(b[3]) << 24;
	}
	uint32_t BE32(uint64_t offset) const {
		auto b = Range(offset, 4);
		return uint32_t(b[3]) | uint32_t(b[2]) << 8 | uint32_t(b[1]) << 16 | uint32_t(b[0]) << 24;
	}
	uint64_t U64(uint64_t offset) const { return U32(offset) | uint64_t(U32(offset + 4)) << 32; }
};

Reader SelectTarget(Reader file)
{
	if (file.BE32(0) != kFat)
		return file;
	const auto count = file.BE32(4);
	const uint64_t tableEnd = 8 + uint64_t(count) * 20;
	file.Range(0, tableEnd);
	std::span<const uint8_t> selected;
	for (uint32_t i = 0; i < count; ++i) {
		const uint64_t at = 8 + uint64_t(i) * 20;
		const auto cpu = file.BE32(at);
		const auto subtype = file.BE32(at + 4);
		const auto offset = file.BE32(at + 8);
		const auto size = file.BE32(at + 12);
		const auto alignment = file.BE32(at + 16);
		Require(offset >= tableEnd && size != 0, "Invalid universal slice range");
		Require(alignment < 32 && (uint64_t(offset) % (uint64_t{1} << alignment)) == 0, "Invalid slice alignment");
		auto slice = file.Range(offset, size);
		if (cpu == kTargetCpu && (subtype & 0x00ffffff) == kTargetSubtype) {
			Require(selected.empty(), "Ambiguous target architecture slices");
			selected = slice;
		}
	}
	Require(!selected.empty(), "No matching target architecture slice");
	return {selected};
}

struct Segment {
	uint64_t address, size, offset, fileSize;
};

std::vector<uint8_t> ReadFile(const char* path)
{
	std::ifstream file(path, std::ios::binary | std::ios::ate);
	Require(bool(file), "Cannot open input");
	const auto length = file.tellg();
	Require(length >= 4 && uint64_t(length) <= uint64_t(std::numeric_limits<std::streamsize>::max()), "Invalid file size");
	std::vector<uint8_t> bytes(static_cast<size_t>(length));
	file.seekg(0);
	Require(bool(file.read(reinterpret_cast<char*>(bytes.data()), static_cast<std::streamsize>(bytes.size()))), "Truncated input");
	return bytes;
}
} // namespace

bool MachOHelper::IsMachO(const char* path)
{
	std::ifstream file(path, std::ios::binary);
	std::array<uint8_t, 4> bytes{};
	if (!file.read(reinterpret_cast<char*>(bytes.data()), bytes.size()))
		return false;
	const auto magic = Reader{bytes}.U32(0);
	// Recognize unsupported flavours too, so MapLibApp returns an explicit error.
	return magic == kMach64 || magic == 0xcffaedfe || magic == 0xfeedface || magic == 0xcefaedfe ||
		magic == 0xbebafeca || magic == kFat || magic == 0xbfbafeca || magic == 0xcafebabf;
}

LibAppInfo MachOHelper::MapLibApp(const char* path)
{
#if defined(TARGET_ARCH_ARM)
	throw std::invalid_argument("ARM32 Mach-O snapshots are not supported");
#endif
	const auto bytes = ReadFile(path);
	const auto file = SelectTarget(Reader{bytes});
	Require(file.U32(0) == kMach64, "Expected little-endian Mach-O 64 or FAT32 universal container");
	file.Range(0, 32);
	Require(file.U32(4) == kTargetCpu && (file.U32(8) & 0x00ffffff) == kTargetSubtype, "Expected matching ARM64 or x64 target (arm64e is deferred)");
	Require(file.U32(12) == 6, "Expected a snapshot dynamic library"); // MH_DYLIB
	const auto count = file.U32(16);
	const auto commandsSize = file.U32(20);
	file.Range(32, commandsSize);
	Require(count <= commandsSize / 8, "Invalid load command count");
	const uint64_t commandsEnd = 32 + uint64_t(commandsSize);
	std::vector<Segment> segments;
	uint64_t symbolsOffset = 0, stringsOffset = 0;
	uint32_t symbolsCount = 0, stringsSize = 0;
	uint64_t sectionCount = 0;
	bool hasSymbols = false;
	uint64_t pos = 32;
	for (uint32_t i = 0; i < count; ++i) {
		Require(pos <= commandsEnd && commandsEnd - pos >= 8, "Truncated load command");
		const auto cmd = file.U32(pos), size = file.U32(pos + 4);
		Require(size >= 8 && size % 8 == 0 && size <= commandsEnd - pos, "Invalid load command size");
		if (cmd == 0x19) { // LC_SEGMENT_64
			Require(size >= 72, "Truncated segment command");
			const auto sections = file.U32(pos + 64);
			Require(72 + uint64_t(sections) * 80 == size, "Invalid section table size");
			sectionCount += sections;
			Segment segment{file.U64(pos + 24), file.U64(pos + 32), file.U64(pos + 40), file.U64(pos + 48)};
			Require(segment.fileSize <= segment.size, "Segment file size exceeds virtual size");
			file.Range(segment.offset, segment.fileSize);
			auto name = file.Range(pos + 8, 16);
			if (std::memcmp(name.data(), "__PAGEZERO\0", 11) != 0 && segment.size != 0) {
				Require(segment.address <= kMaxImageSize && segment.size <= kMaxImageSize - segment.address, "Image exceeds supported 1 GiB virtual range");
				segments.push_back(segment);
			}
		} else if (cmd == 2) { // LC_SYMTAB
			Require(size == 24 && !hasSymbols, "Invalid or duplicate symbol table");
			hasSymbols = true;
			symbolsOffset = file.U32(pos + 8); symbolsCount = file.U32(pos + 12);
			stringsOffset = file.U32(pos + 16); stringsSize = file.U32(pos + 20);
			file.Range(symbolsOffset, uint64_t(symbolsCount) * 16);
			file.Range(stringsOffset, stringsSize);
		} else if (cmd == 0x32) { // LC_BUILD_VERSION
			Require(size >= 24, "Truncated build version command");
			const auto platform = file.U32(pos + 8);
			Require(platform == 1 || platform == 2, "Expected macOS or iOS device target");
		} else if (cmd == 0x21 || cmd == 0x2c) { // LC_ENCRYPTION_INFO[_64]
			Require(size >= (cmd == 0x2c ? 24u : 20u), "Truncated encryption command");
			Require(file.U32(pos + 16) == 0, "Encrypted snapshot image is unsupported");
		}
		pos += size;
	}
	Require(pos == commandsEnd, "Load commands do not fill declared range");
	Require(hasSymbols && !segments.empty(), "Missing symbol table or loadable segments");
	std::sort(segments.begin(), segments.end(), [](const auto& a, const auto& b) { return a.address < b.address; });
	// Dart's snapshot dylibs are zero based. This preserves the existing
	// DartApp::base()/function offset contract without a synthetic pointer bias.
	Require(segments.front().address == 0, "Only zero-based snapshot dylibs are supported");
	uint64_t imageSize = 0;
	for (const auto& segment : segments) {
		Require(segment.address >= imageSize, "Overlapping virtual segments");
		imageSize = segment.address + segment.size;
	}

	constexpr std::array<std::string_view, 4> names{
		"_kDartVmSnapshotData", "_kDartVmSnapshotInstructions",
		"_kDartIsolateSnapshotData", "_kDartIsolateSnapshotInstructions"};
	std::array<uint64_t, 4> addresses{};
	std::array<bool, 4> found{};
	for (uint32_t i = 0; i < symbolsCount; ++i) {
		const uint64_t at = symbolsOffset + uint64_t(i) * 16;
		const auto type = file.Range(at + 4, 1)[0];
		if ((type & 0xe0) != 0 || (type & 0x0e) != 0x0e)
			continue; // Skip debug/undefined symbols.
		const auto strIndex = file.U32(at);
		Require(strIndex < stringsSize, "Invalid symbol string offset");
		auto text = file.Range(stringsOffset + strIndex, stringsSize - strIndex);
		const auto* end = static_cast<const uint8_t*>(std::memchr(text.data(), 0, text.size()));
		Require(end != nullptr, "Unterminated symbol name");
		std::string_view name(reinterpret_cast<const char*>(text.data()), end - text.data());
		const auto match = std::find(names.begin(), names.end(), name);
		if (match == names.end())
			continue;
		const auto index = static_cast<size_t>(match - names.begin());
		Require(!found[index], "Duplicate snapshot symbol");
		const auto section = file.Range(at + 5, 1)[0];
		Require(section != 0 && section <= sectionCount, "Invalid snapshot section index");
		const auto address = file.U64(at + 8);
		const uint64_t required = index % 2 == 0 ? 53 : 8;
		const auto segment = std::find_if(segments.begin(), segments.end(), [&](const auto& s) {
			return address >= s.address && address - s.address <= s.fileSize && required <= s.fileSize - (address - s.address);
		});
		Require(segment != segments.end(), "Snapshot symbol is not file backed");
		const auto offset = segment->offset + address - segment->address;
		const auto remaining = segment->fileSize - (address - segment->address);
		if (index % 2 == 0) {
			Require(file.U32(offset) == 0xdcdcf5f5, "Invalid Dart data snapshot magic");
			const auto length = file.U64(offset + 4);
			Require(length >= 49 && length <= remaining - 4, "Data snapshot exceeds its file-backed segment");
			auto flags = file.Range(offset + 52, length + 4 - 52);
			Require(std::memchr(flags.data(), 0, flags.size()) != nullptr, "Unterminated snapshot flags");
		} else {
			const auto length = file.U64(offset);
			Require(length >= 16 && length <= remaining, "Instruction image exceeds its file-backed segment");
		}
		Require(address % 16 == 0, "Unaligned snapshot symbol");
		addresses[index] = address; found[index] = true;
	}
	Require(std::all_of(found.begin(), found.end(), [](bool value) { return value; }), "Missing Dart snapshot symbols");

	// Anonymous writable storage: no target imports or constructors are run.
	// Zero fill includes BSS, whose relative position is used by Image::bss().
	std::shared_ptr<void> owner(::operator new(static_cast<size_t>(imageSize), std::align_val_t{kAlignment}),
		[](void* image) { ::operator delete(image, std::align_val_t{kAlignment}); });
	auto* image = static_cast<uint8_t*>(owner.get());
	std::memset(image, 0, static_cast<size_t>(imageSize));
	for (const auto& segment : segments)
		if (segment.fileSize != 0)
			std::memcpy(image + segment.address, file.Range(segment.offset, segment.fileSize).data(), static_cast<size_t>(segment.fileSize));
	return LibAppInfo{image, image + addresses[0], image + addresses[1], image + addresses[2], image + addresses[3], std::move(owner)};
}
