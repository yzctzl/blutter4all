import io
import os
import re
import requests
import sys
import zipfile
import zlib
from struct import unpack

from elftools.elf.elffile import ELFFile
from macho import MachO, is_macho

def binary_format(path):
    with open(path, 'rb') as stream:
        magic = stream.read(4)
    if magic == b'\x7fELF':
        return 'elf'
    if is_macho(path):
        return 'macho'
    raise ValueError('Unsupported snapshot format; expected ELF or Mach-O')

def extract_snapshot_hash_flags(libapp_file):
    if binary_format(libapp_file) == 'macho':
        snapshot_hash, flags, _ = MachO(libapp_file).snapshot_info()
        return snapshot_hash, flags
    with open(libapp_file, 'rb') as f:
        elf = ELFFile(f)
        # find "_kDartVmSnapshotData" symbol
        if not elf.little_endian or elf.header.e_type != 'ET_DYN':
            raise ValueError('ELF: Expected a little-endian shared snapshot image')
        segments = sorted((s for s in elf.iter_segments() if s['p_type'] == 'PT_LOAD'
                           and s['p_memsz']), key=lambda s: s['p_vaddr'])
        if not segments or segments[0]['p_vaddr'] != 0:
            raise ValueError('ELF: Expected zero-based snapshot image')
        f.seek(0, 2)
        file_size, image_end = f.tell(), 0
        for s in segments:
            address, size = s['p_vaddr'], s['p_memsz']
            if not image_end <= address <= (1 << 30) or size > (1 << 30) - address:
                raise ValueError('ELF: Overlapping or oversized virtual segments')
            if (s['p_filesz'] > size or s['p_offset'] > file_size or
                    s['p_filesz'] > file_size - s['p_offset']):
                raise ValueError('ELF: Invalid file-backed segment range')
            image_end = address + size
        symbols = [sym for section in elf.iter_sections() if section['sh_type'] == 'SHT_DYNSYM'
                   for sym in section.iter_symbols()
                   if sym.name == '_kDartVmSnapshotData' and sym['st_shndx'] != 'SHN_UNDEF']
        if len(symbols) != 1:
            raise ValueError('ELF: Missing or duplicate VM snapshot data symbol')
        sym = symbols[0]
        address = sym['st_value']
        segment = next((s for s in segments if
                        s['p_vaddr'] <= address and address - s['p_vaddr'] + 53 <= s['p_filesz']), None)
        if segment is None:
            raise ValueError('ELF snapshot metadata is not file backed')
        if address % 16:
            raise ValueError('ELF: Unaligned snapshot symbol')
        f.seek(segment['p_offset'] + address - segment['p_vaddr'])
        header = f.read(52)
        if len(header) != 52:
            raise ValueError('ELF: Truncated snapshot header')
        magic, length = unpack('<IQ', header[:12])
        remaining = segment['p_filesz'] - (address - segment['p_vaddr'])
        if magic != 0xdcdcf5f5 or not 49 <= length <= remaining - 4:
            raise ValueError('ELF: Invalid snapshot header or length')
        snapshot_hash = header[20:52].decode('ascii')
        # Read only the flags, bounded by the declared snapshot, rather than
        # copying the full data image or assuming flags fit in 256 bytes.
        chunks = []
        remaining = length + 4 - 52
        while remaining:
            data = f.read(min(remaining, 256))
            if not data:
                raise ValueError('ELF: Truncated snapshot flags')
            end = data.find(b'\0')
            if end >= 0:
                chunks.append(data[:end])
                break
            chunks.append(data)
            remaining -= len(data)
        else:
            raise ValueError('ELF: Unterminated snapshot flags')
        flags = b''.join(chunks).decode('ascii').split()
    
    return snapshot_hash, flags

def extract_snapshot_target(libapp_file, target_arch=None):
    if binary_format(libapp_file) == 'macho':
        image = MachO(libapp_file, target_arch)
        snapshot_hash, flags, os_name = image.snapshot_info()
        return snapshot_hash, flags, image.arch, os_name
    snapshot_hash, flags = extract_snapshot_hash_flags(libapp_file)
    architectures = [value for value in ('arm64', 'x64', 'arm') if value in flags]
    platforms = [value for value in ('android', 'linux', 'windows') if value in flags]
    if len(architectures) != 1 or len(platforms) != 1:
        raise ValueError('Missing or ambiguous snapshot architecture/platform')
    arch, os_name = architectures[0], platforms[0]
    if target_arch not in (None, arch):
        raise ValueError('Requested architecture does not match snapshot')
    with open(libapp_file, 'rb') as stream:
        elf = ELFFile(stream)
        machine = elf.header.e_machine
        if elf.elfclass != (32 if arch == 'arm' else 64):
            raise ValueError('Snapshot word size does not match ELF header')
    if machine != {'arm64': 'EM_AARCH64', 'x64': 'EM_X86_64', 'arm': 'EM_ARM'}[arch]:
        raise ValueError('Snapshot architecture does not match ELF header')
    if arch == 'arm' and 'compressed-pointers' in flags:
        raise ValueError('ARM32 snapshots cannot use compressed pointers')
    return snapshot_hash, flags, arch, os_name

def extract_libflutter_info(libflutter_file, target_arch=None):
    if is_macho(libflutter_file):
        image = MachO(libflutter_file, target_arch)
        data = image.data.tobytes()
        versions = {match[0].decode() for match in re.findall(br'\x00([\d\w\.-]+) \((stable|beta|dev)\)', data)}
        if len(versions) > 1:
            raise ValueError('Ambiguous Dart versions in selected Flutter engine slice')
        hashes = re.findall(br'\x00([a-f\d]{40})(?=\x00)', data)
        return [value.decode() for value in hashes], next(iter(versions), None), image.arch, image.platform
    with open(libflutter_file, 'rb') as f:
        elf = ELFFile(f)
        if elf.header.e_machine == 'EM_AARCH64': # 183
            arch = 'arm64'
        elif elf.header.e_machine == 'EM_ARM':
            arch = 'arm'
        elif elf.header.e_machine == 'EM_X86_64': # 62
            arch = 'x64'
        else:
            raise ValueError(f'Unsupported engine architecture: {elf.header.e_machine}')

        # The engine is not mapped into the VM. Inspect file-backed read-only
        # segments (including R-X) so discovery does not depend on section names.
        data = b'\0'.join(segment.data() for segment in elf.iter_segments()
                          if segment['p_type'] == 'PT_LOAD' and segment['p_flags'] & 4
                          and not segment['p_flags'] & 2)
        if not data:
            raise ValueError('ELF: Missing read-only engine data')
        
        sha_hashes = re.findall(b'\x00([a-f\\d]{40})(?=\x00)', data)
        #print(sha_hashes)
        # all possible engine ids
        engine_ids = list(dict.fromkeys(h.decode() for h in sha_hashes))
        
        # beta/dev version of flutter might not use stable dart version (we can get dart version from sdk with found engine_id)
        # support stable, beta and dev channels
        versions = {match[0].decode() for match in re.findall(br'\x00([\d\w\.-]+) \((stable|beta|dev)\)', data)}
        if len(versions) > 1:
            raise ValueError('Ambiguous Dart versions in Flutter engine')
        dart_version = next(iter(versions), None)
        
    # ELF itself does not identify Android versus Linux; the snapshot flags do.
    return engine_ids, dart_version, arch, None

def get_dart_sdk_url_size(engine_ids):
    #url = f'https://storage.googleapis.com/dart-archive/channels/stable/release/3.0.3/sdk/dartsdk-windows-x64-release.zip'
    for engine_id in engine_ids:
        url = f'https://storage.googleapis.com/flutter_infra_release/flutter/{engine_id}/dart-sdk-windows-x64.zip'
        resp = requests.head(url)
        if resp.status_code == 200:
           sdk_size = int(resp.headers['Content-Length'])
           return engine_id, url, sdk_size
    
    return None, None, None

def get_dart_commit(url):
    # in downloaded zip
    # * dart-sdk/revision - the dart commit id of https://github.com/dart-lang/sdk/
    # * dart-sdk/version  - the dart version
    # revision and version zip file records should be in first 4096 bytes
    # using stream in case a server does not support range
    commit_id = None
    dart_version = None
    fp = None
    with requests.get(url, headers={"Range": "bytes=0-4096"}, stream=True) as r:
        if r.status_code // 10 == 20:
            x = next(r.iter_content(chunk_size=4096))
            fp = io.BytesIO(x)
    
    if fp is not None:
        while fp.tell() < 4096-30 and (commit_id is None or dart_version is None):
            #sig, ver, flags, compression, filetime, filedate, crc, compressSize, uncompressSize, filenameLen, extraLen = unpack(fp, '<IHHHHHIIIHH')
            _, _, _, compMethod, _, _, _, compressSize, _, filenameLen, extraLen = unpack('<IHHHHHIIIHH', fp.read(30))
            filename = fp.read(filenameLen)
            #print(filename)
            if extraLen > 0:
                fp.seek(extraLen, io.SEEK_CUR)
            data = fp.read(compressSize)
            
            # expect compression method to be zipfile.ZIP_DEFLATED
            assert compMethod == zipfile.ZIP_DEFLATED, 'Unexpected compression method'
            if filename == b'dart-sdk/revision':
                commit_id = zlib.decompress(data, wbits=-zlib.MAX_WBITS).decode().strip()
            elif filename == b'dart-sdk/version':
                dart_version = zlib.decompress(data, wbits=-zlib.MAX_WBITS).decode().strip()
    
    # TODO: if no revision and version in first 4096 bytes, get the file location from the first zip dir entries at the end of file (less than 256KB)
    return commit_id, dart_version

def extract_dart_info(libapp_file: str, libflutter_file: str, target_arch=None):
    apple = binary_format(libapp_file) == 'macho'
    if apple != is_macho(libflutter_file):
        raise ValueError('App and Flutter engine formats do not match')
    snapshot_hash, flags, arch, snapshot_os = extract_snapshot_target(libapp_file, target_arch)
    #print('snapshot hash', snapshot_hash)
    #print(flags)

    if not apple:
        os_name = snapshot_os
        if os_name == 'windows':
            # The engine is PE even when its AOT payload is ELF. Read only
            # embedded SDK metadata; no PE snapshot loading or execution.
            with open(libflutter_file, 'rb') as stream:
                engine_data = stream.read()
            if len(engine_data) < 64 or not engine_data.startswith(b'MZ'):
                raise ValueError('Expected Windows Flutter engine')
            pe_offset, = unpack('<I', engine_data[60:64])
            if (pe_offset > len(engine_data) - 6 or engine_data[pe_offset:pe_offset+4] != b'PE\0\0' or
                    unpack('<H', engine_data[pe_offset+4:pe_offset+6])[0] != {'x64': 0x8664, 'arm64': 0xaa64}[arch]):
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
