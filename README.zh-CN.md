# blutter4all (b4a)

[English](README.md) | 简体中文

基于 [Blutter](https://github.com/worawit/blutter) 的 Flutter Dart AOT 分析工具。

**目前不支持混淆应用。**

感谢 [**Worawit Wangwarunyoo**](https://github.com/worawit) 和
[原项目贡献者](https://github.com/worawit/blutter/graphs/contributors) 奠定的基础。
b4a 在此基础上扩展架构、平台和脚本集成支持，保留原始提交历史和 MIT 许可证。

大量新增代码借助 AI 编写，正确性和稳定性尚未充分验证。这些大范围改动需要较多审核
和维护，因此我们选择独立维护 b4a，而非提交到上游，并自行承担新增代码及其问题。
遇到问题请[提供环境信息和应用样本，提交 Issue](#问题反馈)。

## 功能

- ARM64、x64 分析，以及 Android ARMv7 支持。
- 离线读取 ELF 和 Mach-O 快照，包括通用 Mach-O 二进制文件。
- 支持以下应用目标：

  | 目标系统 | 架构 | AOT 格式 |
  | --- | --- | --- |
  | Android | ARMv7、ARM64、x64 | ELF |
  | iOS | ARM64 | Mach-O |
  | macOS | ARM64、x64 | Mach-O |
  | Linux | ARM64、x64 | ELF |
  | Windows | x64 | ELF（`app.so`） |

- 导出库、类、字段、对象池和函数信息、带注释的汇编，以及启发式指令识别和参数恢复。
- [Frida](https://frida.re/) 17+ 脚本：对象查看、函数搜索、Hook 和分析结果查询。
- [IDA](https://hex-rays.com/ida-pro) 9+ 脚本：名称、线程/对象池结构、类布局和分析注释。
- 接受 APK、IPA、macOS 应用包/ZIP，以及解压后的应用目录。

暂不支持 PE AOT 和 arm64e。识别覆盖度随 Dart 版本和应用而异，不提供完整源码恢复。

## 安装

克隆本仓库并进入项目目录。需要 Python 3.9+、Git、CMake、Ninja、ICU、Capstone，
以及支持 `std::format` 的 C++20 编译器（GCC 13+，或搭配合适标准库的 Clang 16+）。

### Linux（Debian/Ubuntu）

使用软件源自带 GCC 13+ 的发行版：

```sh
sudo apt install python3 python3-venv git cmake ninja-build \
    build-essential pkg-config libicu-dev libcapstone-dev
python3 -m venv .venv
. .venv/bin/activate
pip install 'lief>=1.0,<1.1' requests
```

分析 Android ARMv7 还需要 32 位编译工具链及 32 位 ICU、Capstone 库。

### macOS

安装 Xcode Command Line Tools 和 Homebrew，然后执行：

```sh
brew install cmake ninja pkg-config icu4c capstone
python3 -m venv .venv
. .venv/bin/activate
pip install 'lief>=1.0,<1.1' requests
```

如果系统编译器不支持 `std::format`，请安装较新的 LLVM 工具链。
现代 macOS 无法运行 32 位 ARMv7 分析器。

### Windows

安装 Python 3.9+、Git 和 Visual Studio，并勾选 **Desktop development with C++**
及 **C++ CMake tools**。打开 **x64 Native Tools Command Prompt**，执行：

```bat
python -m venv .venv
.venv\Scripts\activate
pip install "lief>=1.0,<1.1" requests
python scripts\build\init_env_win.py
```

## 使用

首次运行会下载并编译匹配的 Dart 运行时和分析器。

```sh
python b4a.py path/to/app.apk output
python b4a.py path/to/app.ipa output
python b4a.py path/to/Example.app output --arch x64
python b4a.py path/to/windows-or-linux-app output
python b4a.py --help
```

使用 `--arch arm`、`--arch arm64` 或 `--arch x64` 选择输入中可用的架构。
也可以直接传入解压后的 Android 库目录。

只有 AOT 快照、没有 Flutter 引擎时，需指定 Dart 版本和目标：

```sh
python b4a.py path/to/app.so output --dart-version 3.11.5_windows_x64
```

更新代码后，使用 `--rebuild` 重新编译缓存的分析器：

```sh
git pull --ff-only
python b4a.py path/to/app.apk output --rebuild
```

## 输出和脚本

| 输出 | 内容 |
| --- | --- |
| `asm/` | 按库组织的带注释汇编 |
| `objs.txt`、`pp.txt` | 对象和对象池信息 |
| `blutter_frida.js` | Frida 脚本 |
| `ida_script/` | IDA 导入脚本和结构体头文件 |
| `b4a.json` | Ghidra 和脚本共用的统一数据文件，包含版本标识（[格式说明](B4A_FORMAT.md)） |
| `script_analysis.jsonl` | 从统一数据提取的 Frida/IDA 函数分析配套文件 |

使用 **Frida** 时，编辑生成脚本中的 `Config.hooks`。如需查询完整分析结果，
安装可选 Python 依赖并通过配套程序附加到进程：

```sh
pip install 'frida>=17'
python scripts/generate_scripts.py output/b4a.json --attach PID_OR_NAME
```

USB 或远程设备添加 `--device DEVICE_ID`。对于自行映射 ELF 的桌面应用，
需要在生成脚本中设置 `Config.imageBase` 或 `Config.isolateInstructions`。
默认不启用 Hook。

使用 **IDA** 时，打开对应的 AOT 文件，运行 `ida_script/addNames.py`。
将 `script_analysis.jsonl` 保留在输出目录，即 `ida_script/` 的上一级。
脚本会尽可能保留用户已有的名称和注释。

修改模板后，无需重新分析即可生成脚本：

```sh
python scripts/generate_scripts.py output/b4a.json
```

辅助脚本统一放在 `scripts/`：`build/` 用于 SDK 构建和 Windows 环境准备，
`templates/` 存放 Frida/IDA 模板，`tools/` 存放独立辅助工具。

## 问题反馈

[提交 Issue](../../issues/new) 时，请提供 b4a 提交版本、宿主系统/Python 版本、
目标系统/架构、Dart 版本、执行命令和错误日志。必须附上应用安装包
（APK、IPA 或桌面应用压缩包），或 AOT 文件（`libapp.so`、`app.so` 或 Mach-O `App`）
及匹配的 Flutter 引擎，可通过附件或下载链接提供。

## 许可证

[MIT](LICENSE)。
