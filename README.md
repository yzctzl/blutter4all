# blutter4all (b4a)

English | [简体中文](README.zh-CN.md)

A Dart AOT analysis tool for Flutter applications, based on
[Blutter](https://github.com/worawit/blutter).

Thanks to [**Worawit Wangwarunyoo**](https://github.com/worawit) and the
[original contributors](https://github.com/worawit/blutter/graphs/contributors)
for the foundation of this project. b4a builds on their work to expand architecture, platform and
script integration support. The original history and MIT license are preserved.

Much of the new code was written with AI assistance. Its correctness and stability
have not been fully verified. These extensive changes require substantial review
and maintenance, so we maintain b4a separately instead of submitting them upstream.
We take responsibility for the added code and its issues. If you encounter a
problem, [report it with your environment details and application sample](#issues).

## Features

- ARM64 and x64 analysis, plus Android ARMv7 support.
- Offline ELF and Mach-O snapshot loading, including universal Mach-O binaries.
- Android, iOS, macOS, Linux and Windows application targets:

  | Target | Architectures | AOT format |
  | --- | --- | --- |
  | Android | ARMv7, ARM64, x64 | ELF |
  | iOS | ARM64 | Mach-O |
  | macOS | ARM64, x64 | Mach-O |
  | Linux | ARM64, x64 | ELF |
  | Windows | x64 | ELF (`app.so`) |

- Library, class, field, object-pool and function information, annotated assembly,
  and heuristic instruction and parameter recovery.
- [Frida](https://frida.re/) 17+ scripts for object inspection, function search, hooks and analysis queries.
- [IDA](https://hex-rays.com/ida-pro) 9+ scripts for names, thread/pool structures, class layouts and analysis comments.
- APK, IPA, macOS app bundle/ZIP and extracted application directory input.

PE AOT and arm64e are not supported. Analysis coverage varies by Dart version and
application; complete source recovery is not provided.

## Installation

Clone this repository and enter its directory. Install Python 3.9+, Git, CMake,
Ninja, ICU, Capstone and a C++20 compiler with `std::format` support
(GCC 13+ or Clang 16+ with a suitable standard library).

### Linux (Debian/Ubuntu)

Use a distribution that provides GCC 13+ in its repositories:

```sh
sudo apt install python3 python3-venv git cmake ninja-build \
    build-essential pkg-config libicu-dev libcapstone-dev
python3 -m venv .venv
. .venv/bin/activate
pip install 'lief>=1.0,<1.1' requests
```

Android ARMv7 additionally requires a 32-bit compiler toolchain and 32-bit ICU
and Capstone libraries.

### macOS

Install Xcode Command Line Tools and Homebrew, then:

```sh
brew install cmake ninja pkg-config icu4c capstone
python3 -m venv .venv
. .venv/bin/activate
pip install 'lief>=1.0,<1.1' requests
```

Install a newer LLVM toolchain if the system compiler lacks `std::format` support.
Modern macOS cannot run the 32-bit ARMv7 analyzer.

### Windows

Install Python 3.9+, Git and Visual Studio with **Desktop development with C++** and
**C++ CMake tools**. Open an **x64 Native Tools Command Prompt**, then:

```bat
python -m venv .venv
.venv\Scripts\activate
pip install "lief>=1.0,<1.1" requests
python scripts\init_env_win.py
```

## Usage

The first run downloads and builds the matching Dart runtime and analyzer.

```sh
python b4a.py path/to/app.apk output
python b4a.py path/to/app.ipa output
python b4a.py path/to/Example.app output --arch x64
python b4a.py path/to/windows-or-linux-app output
python b4a.py --help
```

Use `--arch arm`, `--arch arm64` or `--arch x64` to select an architecture where
available. Extracted Android library directories are also accepted.

For a standalone AOT snapshot without the Flutter engine, specify its Dart version
and target:

```sh
python b4a.py path/to/app.so output --dart-version 3.11.5_windows_x64
```

After updating the checkout, add `--rebuild` to rebuild the cached analyzer:

```sh
git pull --ff-only
python b4a.py path/to/app.apk output --rebuild
```

## Output and scripts

| Output | Contents |
| --- | --- |
| `asm/` | Annotated assembly organized by library |
| `objs.txt`, `pp.txt` | Object and object-pool dumps |
| `blutter_frida.js` | Frida script |
| `ida_script/` | IDA import script and structure header |
| `script_data.json` | Shared metadata for script generation |
| `script_analysis.jsonl` | Full analysis companion for both scripts |

For **Frida**, edit `Config.hooks` in the generated script. For full analysis
queries, install the optional Python package and attach through the provided host:

```sh
pip install 'frida>=17'
python generate_scripts.py output/script_data.json --attach PID_OR_NAME
```

Add `--device DEVICE_ID` for a USB or remote device. Self-mapped desktop ELF images
require `Config.imageBase` or `Config.isolateInstructions` in the generated script.
Hooks are empty by default.

For **IDA**, open the matching AOT binary and run `ida_script/addNames.py`.
Keep `script_analysis.jsonl` in the output directory, one level above `ida_script/`.
Existing user names and comments are preserved where possible.

After editing either template, regenerate scripts without rerunning analysis:

```sh
python generate_scripts.py output/script_data.json
```

## Issues

[Open an Issue](../../issues/new) with your b4a commit, host OS/Python version,
target OS/architecture, Dart version, command and error log. Include the application
package (APK, IPA or desktop app archive), or the AOT binary (`libapp.so`, `app.so`
or Mach-O `App`) and matching Flutter engine, as attachments or a download link.

## License

[MIT](LICENSE).
