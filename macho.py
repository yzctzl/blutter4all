"""Bounded metadata reads for ordinary ARM64 Apple snapshot dylibs/engines.

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
    def __init__(self, path):
        with open(path, 'rb') as stream:
            self.data = memoryview(stream.read())
        if self.read(0, 4) == b'\xca\xfe\xba\xbe':
            count, = self.unpack('>I', 4)
            table_end = 8 + count * 20
            self.read(0, table_end)
            selected = None
            for index in range(count):
                cpu, subtype, offset, size, alignment = self.unpack('>IIIII', 8 + index * 20)
                require(offset >= table_end and size > 0 and alignment < 32 and
                        offset % (1 << alignment) == 0, 'Invalid universal slice')
                image = self.read(offset, size)
                if cpu == 0x100000c and subtype & 0xffffff == 0:
                    require(selected is None, 'Ambiguous ordinary ARM64 slices')
                    selected = image
            require(selected is not None, 'No ordinary ARM64 slice')
            self.data = selected
        magic, cpu, subtype, filetype, count, size, _, _ = self.unpack('<8I', 0)
        require(magic == 0xfeedfacf and cpu == 0x100000c and subtype & 0xffffff == 0,
                'Expected little-endian ordinary ARM64 (arm64e is deferred)')
        require(filetype == 6, 'Expected dynamic library')
        self.read(32, size)
        require(count <= size // 8, 'Invalid load command count')
        self.segments = []
        self.symbols = None
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
                self.read(offset, file_size)
                self.segments.append((address, offset, file_size))
            elif cmd == 2:
                require(length == 24 and self.symbols is None, 'Invalid symbol table')
                self.symbols = self.unpack('<IIII', pos + 8)
                symbols, count_symbols, strings, size_strings = self.symbols
                self.read(symbols, count_symbols * 16)
                self.read(strings, size_strings)
            elif cmd == 0x32:
                require(length >= 24, 'Truncated build version')
                platform, = self.unpack('<I', pos + 8)
                require(platform in (1, 2), 'Expected macOS or iOS device target')
                self.platform = {1: 'macos', 2: 'ios'}[platform]
            elif cmd in (0x21, 0x2c):
                require(length >= (24 if cmd == 0x2c else 20), 'Truncated encryption command')
                cryptid, = self.unpack('<I', pos + 16)
                require(cryptid == 0, 'Encrypted image is unsupported')
            pos += length
        require(pos == end, 'Invalid load command range')

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
            require(match is None and section != 0, 'Duplicate or invalid snapshot symbol')
            for base, offset, length in self.segments:
                if base <= address < base + length:
                    match = self.read(offset + address - base, length - (address - base))
                    break
            require(match is not None, 'Snapshot symbol is not file backed')
        require(match is not None, 'Missing snapshot symbol')
        return match

    def snapshot_info(self):
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
        require('arm64' in flags, 'Snapshot architecture does not match image')
        platforms = [value for value in ('ios', 'macos') if value in flags]
        require(len(platforms) == 1, 'Missing or ambiguous snapshot platform')
        require(self.platform in (None, platforms[0]), 'Snapshot platform does not match image')
        return snapshot_hash, flags, platforms[0]
