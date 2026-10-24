#!/usr/bin/python3
import argparse
import glob
import mmap
import os
import platform
import shutil
import subprocess
import sys
import zipfile
import tempfile
import stat
from dartvm_fetch_build import DartLibInfo

CMAKE_CMD = "cmake"
NINJA_CMD = "ninja"

SCRIPT_DIR = os.path.dirname(os.path.realpath(__file__))
BIN_DIR = os.path.join(SCRIPT_DIR, 'bin')
PKG_INC_DIR = os.path.join(SCRIPT_DIR, 'packages', 'include')
PKG_LIB_DIR = os.path.join(SCRIPT_DIR, 'packages', 'lib')
BUILD_DIR = os.path.join(SCRIPT_DIR, 'build')


class BlutterInput:
    def __init__(self, libapp_path: str, dart_info: DartLibInfo, outdir: str, rebuild_blutter: bool, create_vs_sln: bool, no_analysis: bool):
        self.libapp_path = libapp_path
        self.dart_info = dart_info
        self.outdir = outdir
        self.rebuild_blutter = rebuild_blutter
        self.create_vs_sln = create_vs_sln

        vers = dart_info.version.split('.', 2)
        if int(vers[0]) == 2 and int(vers[1]) < 15:
            if not no_analysis:
                print('Dart version <2.15, force "no-analysis" option')
            no_analysis = True
        self.no_analysis = no_analysis

        # Note: null-safety is detected in blutter application, so no need another build of blutter for null-safety
        self.name_suffix = ''
        if no_analysis:
            self.name_suffix += '_no-analysis'
        # derive blutter executable filename
        self.blutter_name = f'blutter_{dart_info.lib_name}{self.name_suffix}'
        self.blutter_file = os.path.join(BIN_DIR, self.blutter_name) + ('.exe' if os.name == 'nt' else '')


def framework_paths(name: str):
    return [f'{name}.framework/{version}{name}' for version in ('', 'Versions/Current/', 'Versions/A/')]


def find_lib_files(indir: str):
    android = tuple(os.path.abspath(os.path.join(indir, name)) for name in ('libapp.so', 'libflutter.so'))
    if all(os.path.isfile(path) for path in android):
        return android
    for app, engine in (('data/app.so', 'flutter_windows.dll'),
                        ('lib/libapp.so', 'lib/libflutter_linux_gtk.so'),
                        ('app.so', 'flutter_windows.dll'),
                        ('libapp.so', 'libflutter_linux_gtk.so')):
        pair = tuple(os.path.abspath(os.path.join(indir, name)) for name in (app, engine))
        if all(os.path.isfile(path) for path in pair):
            return pair
    for prefix in ('', 'Frameworks', 'Contents/Frameworks'):
        def first(candidates):
            return next((os.path.abspath(os.path.join(indir, prefix, path)) for path in candidates
                         if os.path.isfile(os.path.join(indir, prefix, path))), None)
        app = first(['App'] + framework_paths('App'))
        engine = first(['Flutter', 'FlutterMacOS'] + framework_paths('Flutter') + framework_paths('FlutterMacOS'))
        if app and engine:
            return app, engine
    raise ValueError('Cannot find a matching App and Flutter engine pair in ' + indir)


def extract_libs_from_apple_archive(archive: str, out_dir: str):
    # Copy only the selected pair to fixed paths: no archive paths are extracted.
    with zipfile.ZipFile(archive) as zf:
        names = {info.filename for info in zf.infolist()
                 if not info.is_dir() and not stat.S_ISLNK(info.external_attr >> 16)}
        roots = set()
        for name in names:
            for app in framework_paths('App'):
                if name.endswith('/' + app):
                    roots.add(name[:-len(app)])
        pairs = []
        for root in sorted(roots):
            app = next((root + path for path in framework_paths('App') if root + path in names), None)
            engine = next((root + path for target in ('Flutter', 'FlutterMacOS')
                           for path in framework_paths(target) if root + path in names), None)
            if app and engine:
                pairs.append((app, engine))
        if len(pairs) != 1:
            raise ValueError('Expected exactly one Apple App/Flutter framework pair in archive')
        paths = []
        for source, filename in zip(pairs[0], ('App', 'Flutter')):
            target = os.path.join(out_dir, filename)
            with zf.open(source) as src, open(target, 'wb') as dst:
                shutil.copyfileobj(src, dst)
            paths.append(target)
        return tuple(paths)

def extract_libs_from_apk(apk_file: str, out_dir: str, target_arch=None):
    with zipfile.ZipFile(apk_file, "r") as zf:
        abis = {'arm64': 'arm64-v8a', 'x64': 'x86_64', 'arm': 'armeabi-v7a'}
        candidates = [abis[target_arch]] if target_arch else list(abis.values())
        names = set(zf.namelist())
        abi = next((abi for abi in candidates if all(f'lib/{abi}/{name}' in names
                    for name in ('libapp.so', 'libflutter.so'))), None)
        if abi is None:
            raise ValueError('Cannot find a matching app/engine ABI pair in the APK')
        app_info = zf.getinfo(f'lib/{abi}/libapp.so')
        flutter_info = zf.getinfo(f'lib/{abi}/libflutter.so')

        zf.extract(app_info, out_dir)
        zf.extract(flutter_info, out_dir)

        app_file = os.path.join(out_dir, app_info.filename)
        flutter_file = os.path.join(out_dir, flutter_info.filename)
        return app_file, flutter_file

def find_compat_macro(dart_version: str, no_analysis: bool):
    macros = []
    include_path = os.path.join(PKG_INC_DIR, f'dartvm{dart_version}')
    vm_path = os.path.join(include_path, 'vm')
    with open(os.path.join(vm_path, 'class_id.h'), 'rb') as f:
        mm = mmap.mmap(f.fileno(), 0, access = mmap.ACCESS_READ)
        # Rename the default implementation classes of Map and Set https://github.com/dart-lang/sdk/commit/a2de36e708b8a8e15d3bd49eef2cede57e649436
        if mm.find(b'V(LinkedHashMap)') != -1:
            macros.append('-DOLD_MAP_SET_NAME=1')
            # Add immutable maps and sets https://github.com/dart-lang/sdk/commit/e8e9e1d15216788d4112e40f4408c52455d11113
            if mm.find(b'V(ImmutableLinkedHashMap)') == -1:
                macros.append('-DOLD_MAP_NO_IMMUTABLE=1')
        if mm.find(b' kLastInternalOnlyCid ') == -1:
            macros.append('-DNO_LAST_INTERNAL_ONLY_CID=1')
        # Remove TypeRef https://github.com/dart-lang/sdk/commit/2ee6fcf5148c34906c04c2ac518077c23891cd1b
        # in this commit also added RecordType as sub class of AbstractType
        #   so assume Dart Records implementation is completed in this commit (before this commit is inconplete RecordType)
        if mm.find(b'V(TypeRef)') != -1:
            macros.append('-DHAS_TYPE_REF=1')
        # in main branch, RecordType is added in Dart 3.0 while TypeRef is removed in Dart 3.1
        # in Dart 2.19, RecordType might be added to a source code but incomplete
        if dart_version.startswith('3.') and mm.find(b'V(RecordType)') != -1:
            macros.append('-DHAS_RECORD_TYPE=1')
    
    with open(os.path.join(vm_path, 'class_table.h'), 'rb') as f:
        mm = mmap.mmap(f.fileno(), 0, access = mmap.ACCESS_READ)
        # Clean up ClassTable (Merge ClassTable and SharedClassTable back together)
        # https://github.com/dart-lang/sdk/commit/4a4eedd860a8af2b1cb27e68d9feae5550d0f511
        # the commit moved GetUnboxedFieldsMapAt() from SharedClassTable to ClassTable
        if mm.find(b'class SharedClassTable {') != -1:
            macros.append('-DHAS_SHARED_CLASS_TABLE=1')
    
    with open(os.path.join(vm_path, 'stub_code_list.h'), 'rb') as f:
        mm = mmap.mmap(f.fileno(), 0, access = mmap.ACCESS_READ)
        # Add InitLateStaticField and InitLateFinalStaticField stub
        # https://github.com/dart-lang/sdk/commit/37d45743e11970f0eacc0ec864e97891347185f5
        if mm.find(b'V(InitLateStaticField)') == -1:
            macros.append('-DNO_INIT_LATE_STATIC_FIELD=1')
    
    with open(os.path.join(vm_path, 'object_store.h'), 'rb') as f:
        mm = mmap.mmap(f.fileno(), 0, access = mmap.ACCESS_READ)
        # [vm] Simplify and optimize method extractors
        # https://github.com/dart-lang/sdk/commit/b9b341f4a71b3ac8c9810eb24e318287798457ae#diff-545efb05c0f9e7191a855bca5e463f8f7f68079f74056f0040196c666b3bb8f0
        if mm.find(b'build_generic_method_extractor_code)') == -1:
            macros.append('-DNO_METHOD_EXTRACTOR_STUB=1')

    with open(os.path.join(vm_path, 'object.h'), 'rb') as f:
        mm = mmap.mmap(f.fileno(), 0, access = mmap.ACCESS_READ)
        # [vm] Refactor access to Integer value
        # https://github.com/dart-lang/sdk/commit/84fd647969f0d74ab63f0994d95b5fc26cac006a
        if mm.find(b'AsTruncatedInt64Value()') == -1:
            macros.append('-DUNIFORM_INTEGER_ACCESS=1')
    
    if no_analysis:
        macros.append('-DNO_CODE_ANALYSIS=1')
    
    return macros

def cmake_blutter(input: BlutterInput):
    blutter_dir = os.path.join(SCRIPT_DIR, 'blutter')
    builddir = os.path.join(BUILD_DIR, input.blutter_name)
    
    macros = find_compat_macro(input.dart_info.version, input.no_analysis)
    my_env = None
    if platform.system() == 'Darwin':
        mac_ver = int(platform.mac_ver()[0].split('.', 1)[0])
        if mac_ver < 15:
            llvm_path = subprocess.run(['brew', '--prefix', 'llvm@16'], capture_output=True, check=True).stdout.decode().strip()
            clang_file = os.path.join(llvm_path, 'bin', 'clang')
            my_env = {**os.environ, 'CC': clang_file, 'CXX': clang_file+'++'}
    # cmake -GNinja -Bbuild -DCMAKE_BUILD_TYPE=Release
    subprocess.run([CMAKE_CMD, '-GNinja', '-B', builddir, f'-DDARTLIB={input.dart_info.lib_name}', f'-DNAME_SUFFIX={input.name_suffix}', '-DCMAKE_BUILD_TYPE=Release', '--log-level=NOTICE'] + macros, cwd=blutter_dir, check=True, env=my_env)

    # build and install blutter
    subprocess.run([CMAKE_CMD, '--build', builddir], check=True)
    subprocess.run([CMAKE_CMD, '--install', '.'], cwd=builddir, check=True)

def get_dart_lib_info(libapp_path: str, libflutter_path: str, target_arch=None) -> DartLibInfo:
    # getting dart version
    from extract_dart_info import extract_dart_info
    dart_version, snapshot_hash, flags, arch, os_name = extract_dart_info(libapp_path, libflutter_path, target_arch)
    print(f'Dart version: {dart_version}, Snapshot: {snapshot_hash}, Target: {os_name} {arch}')
    print('flags: ' + ' '.join(flags))

    has_compressed_ptrs = 'compressed-pointers' in flags
    return DartLibInfo(dart_version, os_name, arch, has_compressed_ptrs, snapshot_hash)

def build_and_run(input: BlutterInput):
    if not os.path.isfile(input.blutter_file) or input.rebuild_blutter:
        # before fetch and build, check the existence of compiled library first
        #   so the src and build directories can be deleted
        if os.name == 'nt':
            dartlib_file = os.path.join(PKG_LIB_DIR, input.dart_info.lib_name+'.lib')
        else:
            dartlib_file = os.path.join(PKG_LIB_DIR, 'lib'+input.dart_info.lib_name+'.a')
        if not os.path.isfile(dartlib_file):
            from dartvm_fetch_build import fetch_and_build
            fetch_and_build(input.dart_info)
        
        input.rebuild_blutter = True

    # creating Visual Studio solution overrides building
    if input.create_vs_sln:
        macros = find_compat_macro(input.dart_info.version, input.no_analysis)
        blutter_dir = os.path.join(SCRIPT_DIR, 'blutter')
        dbg_output_path = os.path.abspath(os.path.join(input.outdir, 'out'))
        dbg_cmd_args = f'-i {input.libapp_path} -o {dbg_output_path}'

        vscmd_ver = os.getenv('VSCMD_VER')
        assert vscmd_ver is not None, "Need run blutter in Visual Studio Develeper console"
        if vscmd_ver.startswith('18.'):
            generator = 'Visual Studio 18 2026'
        elif vscmd_ver.startswith('17.'):
            generator = 'Visual Studio 17 2022'
        else:
            assert False, "Unknown Visual Studio version"

        subprocess.run([CMAKE_CMD, '-G', generator, '-A', 'Win32' if input.dart_info.arch == 'arm' else 'x64', '-B', input.outdir, f'-DDARTLIB={input.dart_info.lib_name}',
                        f'-DNAME_SUFFIX={input.name_suffix}', f'-DDBG_CMD:STRING={dbg_cmd_args}'] + macros + [blutter_dir], check=True)
        dbg_exe_dir = os.path.join(input.outdir, 'Debug')
        os.makedirs(dbg_exe_dir, exist_ok=True)
        for filename in glob.glob(os.path.join(BIN_DIR, '*.dll')):
            shutil.copy(filename, dbg_exe_dir)
    else:
        if input.rebuild_blutter:
            # do not use SDK path for checking source code because Blutter does not depended on it and SDK might be removed
            cmake_blutter(input)
            assert os.path.isfile(input.blutter_file), "Build complete but cannot find Blutter binary: " + input.blutter_file

        # Remove stale metadata before invoking a possibly cached analyzer.
        script_data = os.path.join(input.outdir, 'script_data.json')
        if os.path.isfile(script_data):
            os.remove(script_data)
        subprocess.run([input.blutter_file, '-i', input.libapp_path, '-o', input.outdir], check=True)
        from generate_scripts import generate_scripts
        if not os.path.isfile(script_data):
            raise RuntimeError('Analyzer did not export script metadata; rerun with --rebuild')
        generate_scripts(script_data)

def main_no_flutter(libapp_path: str, dart_version: str, outdir: str, rebuild_blutter: bool, create_vs_sln: bool, no_analysis: bool):
    version, os_name, arch = dart_version.split('_')
    from extract_dart_info import extract_snapshot_target
    snapshot_hash, flags, snapshot_arch, snapshot_os = extract_snapshot_target(libapp_path, arch)
    if snapshot_arch != arch or snapshot_os != os_name:
        raise ValueError('Specified target does not match snapshot architecture/platform')
    dart_info = DartLibInfo(version, os_name, arch, 'compressed-pointers' in flags, snapshot_hash)
    input = BlutterInput(libapp_path, dart_info, outdir, rebuild_blutter, create_vs_sln, no_analysis)
    build_and_run(input)
    
def main2(libapp_path: str, libflutter_path: str, outdir: str, rebuild_blutter: bool, create_vs_sln: bool, no_analysis: bool, target_arch=None):
    dart_info = get_dart_lib_info(libapp_path, libflutter_path, target_arch)
    input = BlutterInput(libapp_path, dart_info, outdir, rebuild_blutter, create_vs_sln, no_analysis)
    build_and_run(input)

def main(indir: str, outdir: str, rebuild_blutter: bool, create_vs_sln: bool, no_analysis: bool, target_arch=None):
    extension = os.path.splitext(indir)[1].lower()
    if os.path.isfile(indir) and extension in ('.apk', '.ipa', '.zip'):
        scratch = os.path.join(SCRIPT_DIR, 'temp')
        os.makedirs(scratch, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='b4a-input-', dir=scratch) as tmp_dir:
            extract = extract_libs_from_apk if extension == '.apk' else extract_libs_from_apple_archive
            libapp_file, libflutter_file = (extract(indir, tmp_dir, target_arch) if extension == '.apk'
                                           else extract(indir, tmp_dir))
            main2(libapp_file, libflutter_file, outdir, rebuild_blutter, create_vs_sln, no_analysis, target_arch)
    else:
        libapp_file, libflutter_file = find_lib_files(indir)
        main2(libapp_file, libflutter_file, outdir, rebuild_blutter, create_vs_sln, no_analysis, target_arch)


def cli():
    parser = argparse.ArgumentParser(
        prog='b4a.py',
        description='Analyze Flutter Dart AOT snapshots')
    parser.add_argument('indir', help='An APK, IPA, macOS app ZIP, app bundle, or directory containing the AOT and engine binaries')
    parser.add_argument('outdir', help='An output directory')
    parser.add_argument('--arch', choices=('arm64', 'x64', 'arm'), help='Select APK ABI or universal Mach-O architecture (default: arm64 when available)')
    parser.add_argument('--rebuild', action='store_true', default=False, help='Force rebuild the Blutter executable')
    parser.add_argument('--vs-sln', action='store_true', default=False, help='Generate Visual Studio solution at <outdir>')
    parser.add_argument('--no-analysis', action='store_true', default=False, help='Do not build with code analysis')
    # rare usage scenario
    parser.add_argument('--dart-version', help='Run without libflutter (indir become libapp.so) by specify dart version such as "3.4.2_android_arm64"')
    args = parser.parse_args()

    if args.dart_version is None:
        main(args.indir, args.outdir, args.rebuild, args.vs_sln, args.no_analysis, args.arch)
    else:
        main_no_flutter(args.indir, args.dart_version, args.outdir, args.rebuild, args.vs_sln, args.no_analysis)


if __name__ == "__main__":
    cli()
