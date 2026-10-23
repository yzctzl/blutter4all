"""Bounded metadata reads for ARM64/x64 Apple snapshot dylibs/engines.

No native loading: offsets are relative to the selected universal slice.
The C++ mapper owns the VM image; this reader only discovers build metadata.
"""
import struct


MAGICS = {b'\xcf\xfa\xed\xfe', b'\xfe\xed\xfa\xcf', b'\xce\xfa\xed\xfe',
          b'\xfe\xed\xfa\xce', b'\xca\xfe\xba\xbe', b'\xbe\xba\xfe\xca',
          b'\xca\xfe\xba\xbf', b'\xbf\xba\xfe\xca'}


def is_macho(path):
    with open(path, 'rb') as stream:
        return stream.read(4) in MAGICS


def require(condition, message):
    if not condition:
        raise ValueError('Mach-O: ' + message)


class MachO:
    def __init__(self, path, arch=None):
        require(arch in (None, "arm64", "x64"), "Unsupported architecture")
        requested_arch = arch
        with open(path, 'rb') as stream:
            self.data = memoryview(stream.read())
        magic = self.read(0, 4).tobytes()
        if magic in (b'\xca\xfe\xba\xbe', b'\xca\xfe\xba\xbf'):
            is64 = magic == b'\xca\xfe\xba\xbf'
            entry_size = 32 if is64 else 20
            count, = self.unpack('>I', 4)
            table_end = 8 + count * entry_size
            self.read(0, table_end)
            slices = {}
            for index in range(count):
                fields = self.unpack('>IIQQII' if is64 else '>IIIII', 8 + index * entry_size)
                cpu, subtype, offset, size, alignment = fields[:5]
                require(not is64 or fields[5] == 0, 'Invalid universal slice reserved field')
                require(offset >= table_end and size > 0 and alignment < (64 if is64 else 32) and
                        offset % (1 << alignment) == 0, 'Invalid universal slice')
                image = self.read(offset, size)
                slice_arch = {(0x100000c, 0): 'arm64', (0x1000007, 3): 'x64'}.get((cpu, subtype & 0xffffff))
                if slice_arch is not None and arch in (None, slice_arch):
                    require(slice_arch not in slices, 'Ambiguous target architecture slices')
                    slices[slice_arch] = image
            selected = slices.get(arch) if arch else slices.get('arm64', slices.get('x64'))
            require(selected is not None, 'No matching target architecture slice')
            self.data = selected
        magic, cpu, subtype, filetype, count, size, _, _ = self.unpack('<8I', 0)
        require(magic == 0xfeedfacf, 'Expected little-endian Mach-O 64')
        self.arch = {(0x100000c, 0): 'arm64', (0x1000007, 3): 'x64'}.get((cpu, subtype & 0xffffff))
        require(self.arch is not None, 'Expected ordinary ARM64 or x64 (arm64e is deferred)')
        require(requested_arch in (None, self.arch), 'Requested architecture does not match image')
        require(filetype == 6, 'Expected dynamic library')
        self.read(32, size)
        require(count <= size // 8, 'Invalid load command count')
        self.segments = []
        self.symbols = None
        self.section_count = 0
        self.platform = None
        pos, end = 32, 32 + size
        for _ in range(count):
            require(pos + 8 <= end, 'Truncated load command')
            cmd, length = self.unpack('<II', pos)
            require(length >= 8 and length % 8 == 0 and length <= end - pos,
                    'Invalid load command size')
            if cmd == 0x19:
                require(length >= 72, 'Truncated segment')
                address, virtual_size, offset, file_size = self.unpack('<QQQQ', pos + 24)
                sections, = self.unpack('<I', pos + 64)
                require(length == 72 + sections * 80 and file_size <= virtual_size,
                        'Invalid segment size')
                self.section_count += sections
                self.read(offset, file_size)
                name = self.read(pos + 8, 16).tobytes()
                if not name.startswith(b'__PAGEZERO\0') and virtual_size:
                    self.segments.append((address, offset, file_size, virtual_size))
            elif cmd == 2:
                require(length == 24 and self.symbols is None, 'Invalid symbol table')
                self.symbols = self.unpack('<IIII', pos + 8)
                symbols, count_symbols, strings, size_strings = self.symbols
                self.read(symbols, count_symbols * 16)
                self.read(strings, size_strings)
            elif cmd == 0x32:
                require(length >= 24, 'Truncated build version')
                platform, = self.unpack('<I', pos + 8)
                tools, = self.unpack('<I', pos + 20)
                require(length == 24 + tools * 8, 'Invalid build tool table')
                require(platform in (1, 2), 'Expected macOS or iOS device target')
                self.set_platform({1: 'macos', 2: 'ios'}[platform])
            elif cmd in (0x24, 0x25):
                require(length == 16, 'Invalid minimum OS version command')
                self.set_platform('macos' if cmd == 0x24 else 'ios')
            elif cmd in (0x21, 0x2c):
                require(length >= (24 if cmd == 0x2c else 20), 'Truncated encryption command')
                cryptid, = self.unpack('<I', pos + 16)
                require(cryptid == 0, 'Encrypted image is unsupported')
            pos += length
        require(pos == end, 'Invalid load command range')

    def set_platform(self, platform):
        require(self.platform in (None, platform), 'Conflicting target platforms')
        self.platform = platform

    def read(self, offset, size):
        require(0 <= offset <= len(self.data) and 0 <= size <= len(self.data) - offset,
                'Read outside selected image')
        return self.data[offset:offset + size]

    def unpack(self, layout, offset):
        return struct.unpack(layout, self.read(offset, struct.calcsize(layout)))

    def symbol_data(self, name):
        require(self.symbols is not None, 'Missing symbol table')
        symbols, count, strings, size = self.symbols
        names = self.read(strings, size).tobytes()
        match = None
        for index in range(count):
            string, kind, section, _, address = self.unpack('<IBBHQ', symbols + index * 16)
            if kind & 0xe0 or kind & 0x0e != 0x0e:
                continue
            require(string < size, 'Invalid symbol name offset')
            terminator = names.find(b'\0', string)
            require(terminator >= 0, 'Unterminated symbol name')
            if names[string:terminator] != name:
                continue
            require(match is None and 0 < section <= self.section_count,
                    'Duplicate or invalid snapshot symbol')
            require(address % 16 == 0, 'Unaligned snapshot symbol')
            for base, offset, length, _ in self.segments:
                if base <= address < base + length:
                    match = self.read(offset + address - base, length - (address - base))
                    break
            require(match is not None, 'Snapshot symbol is not file backed')
        require(match is not None, 'Missing snapshot symbol')
        return match

    def snapshot_info(self):
        # Snapshot offsets are also the analyzer's exported target addresses.
        # Keep this contract identical to the C++ mapper before building a VM.
        segments = sorted(self.segments)
        require(segments and segments[0][0] == 0, 'Expected zero-based snapshot dylib')
        image_end = 0
        for address, _, _, size in segments:
            require(image_end <= address <= (1 << 30) and size <= (1 << 30) - address,
                    'Overlapping or oversized virtual segments')
            image_end = address + size
        data = self.symbol_data(b'_kDartVmSnapshotData')
        require(len(data) >= 53, 'Truncated snapshot header')
        magic, length = struct.unpack_from('<IQ', data)
        require(magic == 0xdcdcf5f5 and 49 <= length <= len(data) - 4,
                'Invalid snapshot header or length')
        snapshot_hash = data[20:52].tobytes().decode('ascii')
        flags = data[52:length + 4].tobytes()
        end = flags.find(b'\0')
        require(end >= 0, 'Unterminated snapshot flags')
        flags = flags[:end].decode('ascii').split()
        require(self.arch in flags, 'Snapshot architecture does not match image')
        platforms = [value for value in ('ios', 'macos') if value in flags]
        require(len(platforms) == 1, 'Missing or ambiguous snapshot platform')
        require(self.platform in (None, platforms[0]), 'Snapshot platform does not match image')
        return snapshot_hash, flags, platforms[0]
