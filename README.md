# B(l)utter
Flutter Mobile Application Reverse Engineering Tool by Compiling Dart AOT Runtime

Currently the application supports only Android libapp.so (arm64 only).
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

### Desktop x64 snapshots

The x64 backend accepts Windows/Linux ELF AOT snapshots and macOS x64
Mach-O snapshot dylibs. Loading is offline and does not run target code.
PE AOT snapshots and arm64e remain deferred.

Pass an unpacked Windows application directory (`data/app.so` and
`flutter_windows.dll`), a Linux application directory (`lib/libapp.so` and
`lib/libflutter_linux_gtk.so`), or a macOS app bundle. For a universal macOS
binary, select x64 explicitly:

```sh
python blutter.py path/to/windows-or-linux-app output
python blutter.py path/to/Example.app output --arch x64
```

With only the AOT binary available, specify the matching SDK and target:

```sh
python blutter.py path/to/app.so output --dart-version 3.11.5_windows_x64
```

The shared snapshot pipeline exports libraries, classes, fields, objects and
methods. The x64 analyzer recognizes frames, stack checks, pool/thread loads,
calls, static fields, class IDs, integer unboxing, and object/array accesses
where the base type is known. Other instructions retain their original assembly;
ARM64 pattern coverage is broader. The Frida template currently requires ARM64
with compressed pointers. Real Windows/Linux ELF and macOS universal Mach-O
samples have been exercised on a Linux x64 host; native Windows/macOS host
builds have not been validated for this change.

### Android ARMv7 snapshots

ARM32 ELF AOT snapshots (`armeabi-v7a`) can be loaded and analyzed offline:

```sh
python blutter.py path/to/app.apk output --arch arm
```

The ARM backend uses the SDK's ARM ABI and A32 instructions. It recognizes
frames, stack checks, object pools, constants, direct and indirect calls,
register moves, and returns. Unrecognized instructions retain their original
assembly.

ARM snapshots require a **32-bit Blutter and Dart runtime**, without pointer
compression. On Linux x86 hosts CMake selects `-m32`; a multilib C++ toolchain
and matching 32-bit ICU and Capstone libraries must be available. A custom
32-bit toolchain can also be supplied with CMake. This path has been exercised
on Linux x64 with Dart 2.19.6 and 3.10.8 ARMv7 samples; other host platforms
have not been runtime-validated. Modern macOS cannot run this
32-bit executable. ARM32 Mach-O and Thumb code are not supported.
