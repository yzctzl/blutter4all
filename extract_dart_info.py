import os
import re
import requests
import sys
import zipfile
import zlib
from struct import unpack

import lief


def binary_format(path):
    if lief.is_elf(path):
        return 'elf'
    if lief.is_macho(path):
        return 'macho'
    with open(path, 'rb') as stream:
        if stream.read(4) == b'\xca\xfe\xba\xbf':
            return 'macho'
    raise ValueError('Unsupported snapshot format; expected ELF or Mach-O')


def _binary_arch(image):
    if isinstance(image, lief.ELF.Binary):
        return {lief.ELF.ARCH.ARM: 'arm', lief.ELF.ARCH.AARCH64: 'arm64',
                lief.ELF.ARCH.X86_64: 'x64'}.get(image.header.machine_type)
    return {(lief.MachO.Header.CPU_TYPE.ARM64, 0): 'arm64',
            (lief.MachO.Header.CPU_TYPE.X86_64, 3): 'x64'}.get(
                (image.header.cpu_type, image.header.cpu_subtype & 0xffffff))


def _read_macho(path, target_arch):
    # LIEF 1.0 does not recognize FAT64. Unwrap only that container; LIEF still
    # parses every Mach-O header, load command, segment and symbol in the slice.
    with open(path, 'rb') as stream:
        if stream.read(4) != b'\xca\xfe\xba\xbf':
            return lief.MachO.parse(path, lief.MachO.ParserConfig.quick), 0
        file_size = os.fstat(stream.fileno()).st_size
        count_data = stream.read(4)
        if len(count_data) != 4:
            raise ValueError('Truncated FAT64 header')
        count, = unpack('>I', count_data)
        table_end = 8 + count * 32
        if table_end > file_size:
            raise ValueError('Truncated FAT64 slice table')
        candidates = {}
        for _ in range(count):
            cpu, subtype, offset, size, alignment, reserved = unpack('>IIQQII', stream.read(32))
            if (reserved or offset < table_end or not 0 < size <= file_size - offset or
                    alignment >= 64 or offset % (1 << alignment)):
                raise ValueError('Invalid FAT64 slice range or alignment')
            arch = {(0x100000c, 0): 'arm64', (0x1000007, 3): 'x64'}.get((cpu, subtype & 0xffffff))
            if arch is not None and target_arch in (None, arch):
                if arch in candidates:
                    raise ValueError('Ambiguous FAT64 architecture slices')
                candidates[arch] = offset, size
        arch = target_arch or ('arm64' if 'arm64' in candidates else 'x64')
        if arch not in candidates:
            raise ValueError('No matching FAT64 architecture slice')
        offset, size = candidates[arch]
        stream.seek(offset)
        images = lief.MachO.parse(stream.read(size), lief.MachO.ParserConfig.quick)
        if images is None or len(images) != 1 or _binary_arch(images.at(0)) != arch:
            raise ValueError('FAT64 slice architecture does not match its header')
        return images, offset


def _read_binary(path, target_arch=None):
    owner, slice_offset = None, 0
    if binary_format(path) == 'elf':
        config = lief.ELF.ParserConfig()
        config.parse_relocations = False
        config.parse_notes = False
        config.parse_overlay = False
        config.parse_symbol_versions = False
        config.parse_symtab_symbols = False
        image = lief.ELF.parse(path, config)
        if image is None:
            raise ValueError('Cannot parse ELF image')
        if image.header.identity_data != lief.ELF.Header.ELF_DATA.LSB:
            raise ValueError('Expected little-endian ELF')
    else:
        images, slice_offset = _read_macho(path, target_arch)
        if images is None:
            raise ValueError('Cannot parse Mach-O image')
        candidates = [image for image in images
                      if _binary_arch(image) is not None and
                      target_arch in (None, _binary_arch(image))]
        if not candidates:
            raise ValueError('Expected ordinary ARM64 or x64 Mach-O (arm64e is deferred)')
        arch = target_arch or ('arm64' if any(_binary_arch(b) == 'arm64' for b in candidates) else 'x64')
        selected = [image for image in candidates if _binary_arch(image) == arch]
        if len(selected) != 1:
            raise ValueError('Ambiguous Mach-O architecture slices')
        image = selected[0]
        owner = images
        if (image.header.magic != lief.MachO.MACHO_TYPES.MAGIC_64 or
                image.header.file_type != lief.MachO.Header.FILE_TYPE.DYLIB):
            raise ValueError('Expected little-endian Mach-O 64 dynamic library')
        commands = list(image.commands)
        if (len(commands) != image.header.nb_cmds or
                sum(cmd.size for cmd in commands) != image.header.sizeof_cmds or
                any(cmd.size < 8 or cmd.size % 8 for cmd in commands)):
            raise ValueError('Incomplete or invalid Mach-O load commands')
        if any(isinstance(cmd, lief.MachO.BuildVersion) and
               (cmd.size < 24 or len(cmd.data) < 24 or
                cmd.size != 24 + unpack('<I', bytes(cmd.data)[20:24])[0] * 8)
               for cmd in commands):
            raise ValueError('Invalid Mach-O build tool table')
        if any(isinstance(cmd, lief.MachO.EncryptionInfo) and cmd.crypt_id
               for cmd in image.commands):
            raise ValueError('Encrypted Mach-O image is unsupported')
    arch = _binary_arch(image)
    if arch is None or target_arch not in (None, arch):
        raise ValueError('Unsupported or mismatched binary architecture')
    if isinstance(image, lief.ELF.Binary):
        expected = lief.ELF.Header.CLASS.ELF32 if arch == 'arm' else lief.ELF.Header.CLASS.ELF64
        if image.header.identity_class != expected:
            raise ValueError('Snapshot word size does not match ELF header')
    # LIEF Mach-O slices borrow storage from their FatBinary container.
    return image, owner, slice_offset


def _apple_platform(image):
    platforms = set()
    for cmd in image.commands:
        if isinstance(cmd, lief.MachO.BuildVersion):
            platform = {lief.MachO.BuildVersion.PLATFORMS.MACOS: 'macos',
                        lief.MachO.BuildVersion.PLATFORMS.IOS: 'ios'}.get(cmd.platform)
            if platform is None:
                raise ValueError('Expected macOS or iOS device target')
            platforms.add(platform)
        elif cmd.command == lief.MachO.LoadCommand.TYPE.VERSION_MIN_MACOSX:
            platforms.add('macos')
        elif cmd.command == lief.MachO.LoadCommand.TYPE.VERSION_MIN_IPHONEOS:
            platforms.add('ios')
    if len(platforms) > 1:
        raise ValueError('Conflicting Mach-O target platforms')
    return next(iter(platforms), None)


def _snapshot_info(path, image, slice_offset):
    apple = isinstance(image, lief.MachO.Binary)
    if apple:
        segments = [(s.virtual_address, s.virtual_size, s.file_offset, s.file_size)
                    for s in image.segments if s.name != '__PAGEZERO' and s.virtual_size]
        symbols = [s for s in image.symbols if s.name == '_kDartVmSnapshotData' and
                   s.type == lief.MachO.Symbol.TYPE.SECTION and
                   0 < s.numberof_sections <= len(image.sections)]
        base, file_size = slice_offset + image.fat_offset, image.original_size
    else:
        if image.header.file_type != lief.ELF.Header.FILE_TYPE.DYN:
            raise ValueError('Expected a shared ELF snapshot image')
        segments = [(s.virtual_address, s.virtual_size, s.file_offset, s.physical_size)
                    for s in image.segments if s.type == lief.ELF.Segment.TYPE.LOAD and s.virtual_size]
        symbols = [s for s in image.dynamic_symbols
                   if s.name == '_kDartVmSnapshotData' and s.shndx != 0]
        base, file_size = 0, os.path.getsize(path)
    segments.sort()
    if not segments or segments[0][0] != 0:
        raise ValueError('Expected zero-based snapshot image')
    end = 0
    for address, size, offset, length in segments:
        if not end <= address <= (1 << 30) or size > (1 << 30) - address:
            raise ValueError('Overlapping or oversized snapshot segments')
        if length > size or offset > file_size or length > file_size - offset:
            raise ValueError('Invalid file-backed snapshot segment range')
        end = address + size
    if len(symbols) != 1 or symbols[0].value % 16:
        raise ValueError('Missing, duplicate or unaligned VM snapshot data symbol')
    address = symbols[0].value
    segment = next((s for s in segments if s[0] <= address and address - s[0] + 53 <= s[3]), None)
    if segment is None:
        raise ValueError('Snapshot metadata is not file backed')
    virtual, _, offset, length = segment
    with open(path, 'rb') as stream:
        stream.seek(base + offset + address - virtual)
        header = stream.read(52)
        if len(header) != 52:
            raise ValueError('Truncated snapshot header')
        magic, size = unpack('<IQ', header[:12])
        if magic != 0xdcdcf5f5 or not 49 <= size <= length - (address - virtual) - 4:
            raise ValueError('Invalid snapshot header or length')
        # Read flags incrementally; the declared data snapshot can be very large.
        chunks, remaining = [], size + 4 - 52
        while remaining:
            data = stream.read(min(remaining, 256))
            if not data:
                raise ValueError('Truncated snapshot flags')
            end = data.find(b'\0')
            if end >= 0:
                chunks.append(data[:end])
                break
            chunks.append(data)
            remaining -= len(data)
        else:
            raise ValueError('Unterminated snapshot flags')
    flags = b''.join(chunks).decode('ascii').split()
    architectures = [a for a in ('arm', 'arm64', 'x64') if a in flags]
    platforms = [p for p in ('android', 'linux', 'windows', 'ios', 'macos') if p in flags]
    if architectures != [_binary_arch(image)] or len(platforms) != 1:
        raise ValueError('Missing, ambiguous or mismatched snapshot target')
    platform = platforms[0]
    if apple:
        if platform not in ('ios', 'macos') or _apple_platform(image) not in (None, platform):
            raise ValueError('Snapshot platform does not match Mach-O image')
    elif platform not in ('android', 'linux', 'windows'):
        raise ValueError('Snapshot platform does not match ELF image')
    if architectures[0] == 'arm' and (platform != 'android' or 'compressed-pointers' in flags):
        raise ValueError('ARM32 requires Android without compressed pointers')
    return header[20:52].decode('ascii'), flags, architectures[0], platform


def extract_snapshot_hash_flags(libapp_file):
    return extract_snapshot_target(libapp_file)[:2]


def extract_snapshot_target(libapp_file, target_arch=None):
    image, owner, slice_offset = _read_binary(libapp_file, target_arch)
    return _snapshot_info(libapp_file, image, slice_offset)


def extract_libflutter_info(libflutter_file, target_arch=None):
    image, owner, slice_offset = _read_binary(libflutter_file, target_arch)
    if isinstance(image, lief.MachO.Binary):
        # Scan the original selected slice, not a rebuilt Mach-O representation.
        with open(libflutter_file, 'rb') as stream:
            stream.seek(slice_offset + image.fat_offset)
            data = stream.read(image.original_size)
        platform = _apple_platform(image)
    else:
        data = b'\0'.join(bytes(s.content) for s in image.segments
                          if s.type == lief.ELF.Segment.TYPE.LOAD and
                          s.has(lief.ELF.Segment.FLAGS.R) and not s.has(lief.ELF.Segment.FLAGS.W))
        if not data:
            raise ValueError('ELF: Missing read-only engine data')
        platform = None
    versions = {match[0].decode() for match in re.findall(br'\x00([\d\w\.-]+) \((stable|beta|dev)\)', data)}
    if len(versions) > 1:
        raise ValueError('Ambiguous Dart versions in Flutter engine')
    hashes = re.findall(br'\x00([a-f\d]{40})(?=\x00)', data)
    return list(dict.fromkeys(h.decode() for h in hashes)), next(iter(versions), None), _binary_arch(image), platform


def get_dart_sdk_url_size(engine_ids):
    #url = f'https://storage.googleapis.com/dart-archive/channels/stable/release/3.0.3/sdk/dartsdk-windows-x64-release.zip'
    for engine_id in engine_ids:
        url = f'https://storage.googleapis.com/flutter_infra_release/flutter/{engine_id}/dart-sdk-windows-x64.zip'
        resp = requests.head(url, timeout=30)
        if resp.status_code == 200:
           sdk_size = int(resp.headers['Content-Length'])
           return engine_id, url, sdk_size
    
    return None, None, None

def get_dart_commit(url):
    # Read only the archive prefix, even when the server ignores Range.
    limit = 64 * 1024
    prefix = bytearray()
    with requests.get(url, headers={"Range": f"bytes=0-{limit - 1}"},
                      stream=True, timeout=30) as response:
        response.raise_for_status()
        for chunk in response.iter_content(chunk_size=4096):
            prefix.extend(chunk[:limit - len(prefix)])
            if len(prefix) == limit:
                break

    values = {}
    offset = 0
    while offset + 30 <= len(prefix):
        signature, _, flags, method, _, _, crc, size, unpacked, name_len, extra_len = unpack(
            '<IHHHHHIIIHH', prefix[offset:offset + 30])
        if signature != 0x04034b50 or flags & 0x09:
            break  # Central directory, encryption or unknown data-descriptor size.
        name = bytes(prefix[offset + 30:offset + 30 + name_len])
        start = offset + 30 + name_len + extra_len
        end = start + size
        if end > len(prefix):
            break
        if name in (b'dart-sdk/revision', b'dart-sdk/version'):
            if unpacked > 4096:
                raise ValueError('Dart SDK version record is too large')
            data = bytes(prefix[start:end])
            if method == zipfile.ZIP_DEFLATED:
                decoder = zlib.decompressobj(-zlib.MAX_WBITS)
                try:
                    data = decoder.decompress(data, 4097)
                except zlib.error as error:
                    raise ValueError('Invalid compressed Dart SDK version record') from error
                if not decoder.eof or decoder.unused_data or decoder.unconsumed_tail:
                    raise ValueError('Truncated or oversized Dart SDK version record')
            elif method != zipfile.ZIP_STORED:
                raise ValueError('Unsupported Dart SDK version record compression')
            if len(data) != unpacked or zlib.crc32(data) != crc:
                raise ValueError('Corrupt Dart SDK version record')
            values[name] = data.decode('utf-8').strip()
            if len(values) == 2:
                break
        offset = end

    version = values.get(b'dart-sdk/version')
    if not version or re.fullmatch(r'\d+\.\d+\.\d+(?:[-+][0-9A-Za-z.-]+)?', version) is None:
        raise ValueError('Cannot determine Dart version from SDK archive prefix; use --dart-version')
    return values.get(b'dart-sdk/revision'), version


def extract_dart_info(libapp_file: str, libflutter_file: str, target_arch=None):
    apple = binary_format(libapp_file) == 'macho'
    snapshot_hash, flags, arch, snapshot_os = extract_snapshot_target(libapp_file, target_arch)
    if snapshot_os != 'windows' and apple != (binary_format(libflutter_file) == 'macho'):
        raise ValueError('App and Flutter engine formats do not match')
    #print('snapshot hash', snapshot_hash)
    #print(flags)

    if not apple:
        os_name = snapshot_os
        if os_name == 'windows':
            # The engine is PE even when its AOT payload is ELF. Read only
            # embedded SDK metadata; no PE snapshot loading or execution.
            with open(libflutter_file, 'rb') as stream:
                engine_data = stream.read()
            engine = lief.PE.parse(libflutter_file) if lief.is_pe(libflutter_file) else None
            if engine is None:
                raise ValueError('Expected Windows Flutter engine')
            if engine.header.machine != {'x64': lief.PE.Header.MACHINE_TYPES.AMD64,
                                         'arm64': lief.PE.Header.MACHINE_TYPES.ARM64}.get(arch):
                raise ValueError('App and Windows Flutter engine architectures do not match')
            versions = {match[0].decode() for match in re.findall(br'\x00([\d\w.-]+) \((stable|beta|dev)\)', engine_data)}
            if len(versions) != 1:
                raise ValueError('Cannot determine unique Dart version from Windows engine')
            dart_version = versions.pop()
            engine_ids = []
        else:
            engine_ids, dart_version, engine_arch, _ = extract_libflutter_info(libflutter_file)
            if arch != engine_arch:
                raise ValueError('App and Flutter engine architectures do not match')
    else:
        engine_ids, dart_version, arch, os_name = extract_libflutter_info(libflutter_file, arch)
    if apple:
        if os_name not in (None, snapshot_os):
            raise ValueError('App and Flutter engine target platforms do not match')
        os_name = snapshot_os
    # print('possible engine ids', engine_ids)
    # print('dart version', dart_version)

    if dart_version is None:
        engine_id, sdk_url, sdk_size = get_dart_sdk_url_size(engine_ids)
        if sdk_url is None:
            raise ValueError('Cannot determine Dart SDK version from Flutter engine')
        # print(engine_id)
        # print(sdk_url)
        # print(sdk_size)

        commit_id, dart_version = get_dart_commit(sdk_url)
        # print(commit_id)
        # print(dart_version)
        #assert dart_version == dart_version_sdk
    
    return dart_version, snapshot_hash, flags, arch, os_name


if __name__ == "__main__":
    libdir = sys.argv[1]
    libapp_file = os.path.join(libdir, 'libapp.so')
    libflutter_file = os.path.join(libdir, 'libflutter.so')

    print(extract_dart_info(libapp_file, libflutter_file))
