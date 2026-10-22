import io
import os
import re
import requests
import sys
import zipfile
import zlib
from struct import unpack

from elftools.elf.elffile import ELFFile
from elftools.elf.enums import ENUM_E_MACHINE 
from elftools.elf.sections import SymbolTableSection
from macho import MachO, is_macho

def extract_snapshot_hash_flags(libapp_file):
    if is_macho(libapp_file):
        snapshot_hash, flags, _ = MachO(libapp_file).snapshot_info()
        return snapshot_hash, flags
    with open(libapp_file, 'rb') as f:
        elf = ELFFile(f)
        # find "_kDartVmSnapshotData" symbol
        dynsym = elf.get_section_by_name('.dynsym')
        sym = dynsym.get_symbol_by_name('_kDartVmSnapshotData')[0]
        #section = elf.get_section(sym['st_shndx'])
        assert sym['st_size'] > 128
        address = sym['st_value']
        segment = next((s for s in elf.iter_segments() if s['p_type'] == 'PT_LOAD' and
                        s['p_vaddr'] <= address and address - s['p_vaddr'] + 52 <= s['p_filesz']), None)
        if segment is None:
            raise ValueError('ELF snapshot metadata is not file backed')
        f.seek(segment['p_offset'] + address - segment['p_vaddr'] + 20)
        snapshot_hash = f.read(32).decode()
        data = f.read(256) # should be enough
        flags = data[:data.index(b'\0')].decode().strip().split(' ')
    
    return snapshot_hash, flags

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
        elif elf.header.e_machine == 'EM_X86_64': # 62
            arch = 'x64'
        else:
            assert False, f"Unsupport architecture: {elf.header.e_machine}"

        section = elf.get_section_by_name('.rodata')
        data = section.data()
        
        sha_hashes = re.findall(b'\x00([a-f\\d]{40})(?=\x00)', data)
        #print(sha_hashes)
        # all possible engine ids
        engine_ids = [ h.decode() for h in sha_hashes ]
        assert len(engine_ids) == 2, f'found hashes {", ".join(engine_ids)}'
        
        # beta/dev version of flutter might not use stable dart version (we can get dart version from sdk with found engine_id)
        # support stable, beta and dev channels
        m = re.search(br'\x00([\d\w\.-]+) \((stable|beta|dev)\)', data)
        if m is None:
            dart_version = None
        else:
            dart_version = m.group(1).decode()
        
    return engine_ids, dart_version, arch, 'android'

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
    apple = is_macho(libapp_file)
    if apple != is_macho(libflutter_file):
        raise ValueError('App and Flutter engine formats do not match')
    if apple:
        image = MachO(libapp_file, target_arch)
        snapshot_hash, flags, snapshot_os = image.snapshot_info()
        target_arch = image.arch
    else:
        snapshot_hash, flags = extract_snapshot_hash_flags(libapp_file)
    #print('snapshot hash', snapshot_hash)
    #print(flags)

    if not apple:
        architectures = [value for value in ('arm64', 'x64') if value in flags]
        platforms = [value for value in ('android', 'linux', 'windows') if value in flags]
        if len(architectures) != 1 or len(platforms) != 1:
            raise ValueError('Missing or ambiguous snapshot architecture/platform')
        arch, os_name = architectures[0], platforms[0]
        if target_arch not in (None, arch):
            raise ValueError('Requested architecture does not match snapshot')
        with open(libapp_file, 'rb') as stream:
            machine = ELFFile(stream).header.e_machine
        if machine != {'arm64': 'EM_AARCH64', 'x64': 'EM_X86_64'}[arch]:
            raise ValueError('Snapshot architecture does not match ELF header')
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
        engine_ids, dart_version, arch, os_name = extract_libflutter_info(libflutter_file, target_arch)
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
