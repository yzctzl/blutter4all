# B(l)utter
Flutter Mobile Application Reverse Engineering Tool by Compiling Dart AOT Runtime

Supports Dart AOT snapshots in ELF and Mach-O format for ARM64/x64,
and Android ARMv7 ELF snapshots. See the target notes below.
Also the application is currently work only against recent Dart versions.

For high priority missing features, see [TODO](#todo)


## Environment Setup
This application uses C++20 Formatting library. It requires very recent C++ compiler such as g++>=13, Clang>=16.

I recommend using Linux OS (only tested on Deiban sid/trixie) because it is easy to setup.

### Debian Unstable (gcc 13)
**_NOTE:_**
Use ONLY Debian/Ubuntu version that provides gcc>=13 from its own main repository.
Using ported gcc to old Debian/Ubuntu version does not work.

- Install build tools and depenencies
```
apt install python3-pyelftools python3-requests git cmake ninja-build \
    build-essential pkg-config libicu-dev libcapstone-dev
```

### Windows
- Install git and python 3
- Install latest Visual Studio with "Desktop development with C++" and "C++ CMake tools"
- Install required libraries (libcapstone and libicu4c)
```
python scripts\init_env_win.py
```
- Start "x64 Native Tools Command Prompt"

### macOS Sequoia
- Install XCode
- Install required tools
```
brew install cmake ninja pkg-config icu4c capstone
pip3 install pyelftools requests
```

### macOS Ventura and Sonoma (clang 16)
- Install XCode
- Install clang 16 and required tools
```
brew install llvm@16 cmake ninja pkg-config icu4c capstone
pip3 install pyelftools requests
```

## Usage
Extract "lib" directory from apk file
```
python3 blutter.py path/to/app/lib/arm64-v8a out_dir
```
The blutter.py will automatically detect the Dart version from the flutter engine and call executable of blutter to get the information from libapp.so.

If the blutter executable for required Dart version does not exists, the script will automatically checkout Dart source code and compiling it.

## Update
You can use ```git pull``` to update and run blutter.py with ```--rebuild``` option to force rebuild the executable
```
python3 blutter.py path/to/app/lib/arm64-v8a out_dir --rebuild
```

## Output files
- **asm/\*** libapp assemblies with symbols
- **blutter_frida.js** the frida script template for the target application
- **objs.txt** complete (nested) dump of Object from Object Pool
- **pp.txt** all Dart objects in Object Pool


## Directories
- **bin** contains blutter executables for each Dart version in "blutter_dartvm\<ver\>\_\<os\>\_\<arch\>" format
- **blutter** contains source code. need building against Dart VM library
- **build** contains building projects which can be deleted after finishing the build process
- **dartsdk** contains checkout of Dart Runtime which can be deleted after finishing the build process
- **external** contains 3rd party libraries for Windows only
- **packages** contains the static libraries of Dart Runtime
- **scripts** contains python scripts for getting/building Dart


## Generating Visual Studio Solution for Development
I use Visual Studio to delevlop Blutter on Windows. ```--vs-sln``` options can be used to generate a Visual Studio solution.
```
python blutter.py path\to\lib\arm64-v8a build\vs --vs-sln
```

## TODO
- More code analysis
  - Function arguments and return type
  - Some psuedo code for code pattern
- Generate better Frida script
  - More internal classes
  - Object modification
- Obfuscated app (still missing many functions)
- Reading iOS binary
- Input as apk or ipa

### x64 and Linux ARM64 snapshots

The x64 backend accepts Android/Windows/Linux ELF AOT snapshots and macOS x64
Mach-O snapshot dylibs, with compressed or uncompressed pointers as specified
by the snapshot. Linux ARM64 ELF snapshots use the existing ARM64 backend.
Loading is offline and does not run target code.
PE AOT snapshots and arm64e remain deferred.

Format detection uses file contents, not filename extensions. ELF input must
be a zero-based, little-endian shared snapshot image with a dynamic symbol
table. Mach-O input must be a zero-based 64-bit snapshot dylib with a symbol
table; both FAT32 and FAT64 universal containers are accepted. Encrypted images
are rejected. These are offline snapshot readers, not general OS loaders.

Pass an unpacked Windows application directory (`data/app.so` and
`flutter_windows.dll`), a Linux application directory (`lib/libapp.so` and
`lib/libflutter_linux_gtk.so`), or a macOS app bundle. For a universal macOS
binary, select x64 explicitly:

```sh
python blutter.py path/to/windows-or-linux-app output
python blutter.py path/to/Example.app output --arch x64
python blutter.py path/to/android.apk output --arch x64
```

With only the AOT binary available, specify the matching SDK and target:

```sh
python blutter.py path/to/app.so output --dart-version 3.11.5_windows_x64
```

This option checks the specified target against the snapshot and reads pointer
compression from its flags; it does not infer the pointer layout from the OS.

The shared snapshot pipeline exports libraries, classes, fields, objects and
methods. The x64 analyzer recognizes frames, stack checks, pool/thread loads,
calls, static fields, class IDs, integer unboxing, and object/array accesses
where the base type is known. Other instructions retain their original assembly;
ARM64 pattern coverage is broader. Script integration is described below.
Real Windows/Linux ELF and macOS universal Mach-O
samples, Android x64 (Dart 3.10.8), and Linux ARM64 (Dart 3.5.4) have been
exercised on a Linux x64 host; native Windows/macOS host
builds have not been validated for this change.

### Android ARMv7 snapshots

ARM32 ELF AOT snapshots (`armeabi-v7a`) can be loaded and analyzed offline:

```sh
python blutter.py path/to/app.apk output --arch arm
```

The ARM backend uses the SDK's ARM ABI and A32 instructions. It recognizes
frames, stack checks, object pools, calls, class IDs, integer boxing/unboxing,
fixed-size inline allocation, write barriers, async initialization, type-test
stubs, static fields, and selected field/list/typed-data accesses. Paired stub
scopes recover saved CPU/FPU registers. Parameter recovery uses surviving
signatures, observed register/stack sources, and verified optional/named/default
and type-argument protocols. Missing declarations and eliminated defaults remain
partial; unrecognized instructions retain their original assembly.

ARM snapshots require a **32-bit Blutter and Dart runtime**, without pointer
compression. On Linux x86 hosts CMake selects `-m32`; a multilib C++ toolchain
and matching 32-bit ICU and Capstone libraries must be available. A custom
32-bit toolchain can also be supplied with CMake. This path has been exercised
on Linux x64 with Dart 2.19.6 and 3.10.8 ARMv7 samples; other host platforms
have not been runtime-validated. Modern macOS cannot run this
32-bit executable. ARM32 Mach-O and Thumb code are not supported.

### Frida and IDA integration

`blutter.py` exports SDK-derived metadata to `script_data.json` and renders:

- `blutter_frida.js` for Frida **17+**.
- `ida_script/addNames.py` and `ida_dart_struct.h` for IDA **9+**.
- `script_analysis.jsonl`, the shared full analysis companion; keep it next to the scripts.

The same templates handle Android ARM/ARM64/x64 ELF, Linux ARM64/x64 ELF,
Windows x64 ELF, macOS ARM64/x64 Mach-O, and iOS ARM64 Mach-O. Object-slot and
machine-word widths come from the snapshot build, including pointer compression.
PE AOT and arm64e remain deferred.

For Frida, edit `Config.hooks` near the top of the generated script. Hooks are
empty by default. Inside a hook, use `new DartReader(this.context)` and
`readRegister(name)` or `readStackSlot(index)` to inspect a **full tagged Dart
object** at a known location. Stack slot 0 means the last physical stack argument
at function entry; on x64 it skips the return address. This is not declaration
parameter order, and unboxed values must not be interpreted as tagged objects.
Object traversal is bounded; unsupported objects and unreadable fields are
reported explicitly. Unknown native fields are shown as raw storage.

System-loaded modules are matched against generated code fingerprints, without
assuming a fixed module name. For self-mapped desktop ELF, set `Config.imageBase`
or the runtime `_kDartIsolateSnapshotInstructions` address in
`Config.isolateInstructions`. These refer to target virtual addresses, not file
offsets. The script verifies the image before attaching hooks; automatic discovery
of anonymous ELF mappings is not implemented. No Java/ObjC bridge is required.

For IDA, open the matching AOT binary and run `ida_script/addNames.py`. Addresses
are translated using the IDB image base; set `IMAGE_BASE` for a manually mapped
image. The script checks processor, bitness, byte order and code fingerprints
before changing the database. Existing user names, operand formats and conflicting
structures are preserved. Type import errors are reported separately from function
naming. These imports do not reconstruct complete decompiler function prototypes.

Frida exposes `BlutterAPI.findFunctions(query)`, `functionInfo(offsetOrExactName)`,
`analysis(offsetOrExactName)` and `hook(offsetOrExactName, callbacks)`. Custom
objects use recovered field names where available. `BlutterAPI.metadata` contains
class declarations, fields, types, flags and their snapshot/inferred provenance.
Closures show their entry and captured context; native numeric fields are decoded
only when both the declaration and storage bitmap establish the representation.

Full function bodies include declaration/signature information, recovered and
observed parameters, frame size, closure/type-argument locations, every IL record
(including unknown ranges), and resolved call/constant/THR/PP annotations.
They stay on the host and are requested individually; the application does not
need to hold the entire analysis in memory. Install the optional `frida` Python
package (17+) and use the shared host instead of the ordinary Frida CLI when
requesting full analysis:

```sh
python generate_scripts.py output/script_data.json --attach PID_OR_NAME
# For a remote/USB device, add --device DEVICE_ID.
# --script custom.js loads a customized generated script.
```

For example, append this to the generated script (replace the offset):

```js
(async () => {
    const info = await BlutterAPI.analysis('0x123456');
    console.log(JSON.stringify(info.analysis));
    BlutterAPI.hook(info.offset, {
        onEnter() {
            const reader = new BlutterAPI.DartReader(this.context);
            console.log(JSON.stringify(reader.readParameters(info)));
        }
    });
})().catch(console.error);
```

`readParameters` returns observed raw entry locations, with explicit unavailable
markers. It does not interpret unknown tagged/unboxed representations or invent
parameter order. Shared machine-code entries preserve all declaration aliases;
`readParameters(info, index)` selects one explicitly (0 is the primary declaration).
`await BlutterAPI.lookup('structures')` exposes the SDK thread
and object-pool layouts; `lookup('operands')` exposes instruction operand records.
The ordinary `frida -l` workflow still supports objects, function search and
explicit hooks, but on-demand analysis requires the Python host.

IDA additionally imports per-CID class layouts, declaration/parameter/frame
summaries as function comments, and recognized IL plus resolved constants/calls
as instruction comments. Generated comment blocks are replaced on reruns while
preserving user text. Class members use physical slot widths, not guessed native
C pointer types. Existing layouts and function boundaries are preserved; conflicts
are reported. Set `IMPORT_CLASSES` or `IMPORT_ANALYSIS` to false to skip either
pass. Keep `script_analysis.jsonl` one directory above `ida_script/addNames.py`.
IDA imports the companion sequentially instead of embedding millions of Python
objects in the generated source.

The intermediate `script_data.json` is needed for regeneration. After editing templates, regenerate
without rerunning analysis:

```sh
python generate_scripts.py output/script_data.json
```

Direct execution of the C++ binary exports metadata; run the command above to
render scripts. After updating from an older analyzer, rebuild it once with
`--rebuild` so that `script_data.json` is available.

Generation has been checked against nine real sample combinations on Linux.
Frida 17 has additionally been exercised on local x64 controlled-memory fixtures
and native hooks. Cross-platform live Dart hooks and imports into an actual IDA 9
installation still require validation; generated output alone is not runtime
acceptance.
