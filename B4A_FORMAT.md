# b4a data format, version 1

`b4a.json` is the shared public output of `b4a.py`. Ghidra, IDA, Frida and other
consumers use the same document. It contains both snapshot facts and available
analysis results. It does not contain the original executable.

The native analyzer writes a private `.b4a.raw.json`. Python attaches original-file
identity and mappings, validates the document, and atomically publishes `b4a.json`.
The private file is then removed. Use `b4a.py` for this complete pipeline.

## Document sections

| Field | Meaning |
| --- | --- |
| `format`, `version` | Exactly `"b4a"` and `1`; reject unsupported versions |
| `producer` | Producer name and optional revision; null revision is allowed |
| `dart` | SDK-reported Dart version string |
| `target` | Target architecture, OS, widths, compression, SDK register roles used by existing scripts, snapshot compatibility hash and flags |
| `image` | Original-file identity, selected slice, mapped segments, four snapshot locations and auxiliary code-byte checks |
| `registers` | SDK-defined physical registers for Dart/native SP, FP, LR, THR, PP and arguments descriptor |
| `codeUnits` | Original Code payload ranges and known entry points, consolidated by identical storage range |
| `coverage` | Export diagnostics and declaration analysis counts; not a whole-program recovery percentage |
| `analysisState` | `available` when the analyzer ran, `not_run` for `--no-analysis` |
| `constants` | Class-ID/tag constants from the matching SDK |
| `classes`, `topClasses` | Built-in/object layouts, inheritance, sizes, field bitmaps, instance/static fields and available declarations |
| `functions` | Legacy script view: `[entry, size, displayName]`, including extra entry labels and stubs |
| `structures` | Thread and ObjectPool members: `[byteOffset, name, description]` |
| `operands` | THR/PP observations: `[instruction, operandIndex, structureName, delta]` |
| `analysis` | Declaration records: `[normalEntry, body]`; duplicate addresses are intentional |

All sections are present. Their data may be unavailable or partial, as specified
below. Existing names and descriptions are presentation data, not instructions to
execute. The native analysis algorithms are unchanged by this export format.

## Addresses and identity

Address fields use lowercase `0x` hexadecimal strings. They are unsigned 64-bit
target RVAs, never analyzer-process pointers. All ranges are half-open `[start,end)`.
Integer sizes and offsets are bytes; sizes must be exact JSON integers below 2^53.
Signed FP/local parameter offsets retain their existing signed-byte meaning.

Version 1 accepts little-endian, zero-based ELF/Mach-O snapshot images. `arch` is
`arm64`, `arm` or `x64`; `os` is `android`, `ios`, `macos`, `linux` or `windows`.
This describes existing b4a combinations, not support for every possible pairing.
PE and arm64e remain unsupported. ARM is Android ELF only.

`target.wordSize` is 4 for ARM and 8 otherwise. `slotSize` is the compressed-object
slot width: 4 with compressed pointers, otherwise `wordSize`. ObjectPool slots
and machine stack slots are not compressed-object slots. `entrySlots` is the
SDK's last parameter slot relative to entry SP, not the number of parameters.

`target.snapshotHash` is the 32-digit snapshot compatibility hash; it is not an
application fingerprint or a unique SDK commit. `snapshotFlags` preserves the
actual flags. `image.sha256` is the 64-digit SHA-256 of the original selected image:
the full file for ELF/thin Mach-O, the exact thin slice bytes for FAT32/FAT64.
It is not a hash of relocated memory or a LIEF-rewritten binary.

`image.preferredBase` is `"0x0"`. `fileSize` is the selected image byte length;
`sliceOffset` locates it in the original container. Segment `fileOffset` is relative
to the selected slice, not to its container. Each segment has `rva`, `memorySize`,
`fileOffset`, `fileSize`, and three-character `permissions`, such as `r-x`.
Mappings are non-overlapping and sorted by RVA. ELF uses nonempty PT_LOAD segments;
Mach-O excludes __PAGEZERO. BSS has no file bytes.

`image.vmData`, `vmInstructions`, `isolateData`, `isolateInstructions` are snapshot
symbol RVAs, not the first function addresses. `checks` contains auxiliary
`[rva, sixteenBytesAsHex]` observations retained for existing script verification.
These few bytes do not replace original-file identity checks for importing data.

Static location is the loaded image base plus RVA. Verify original segments and
rebase state rather than guessing from the lowest memory block. Runtime mapping
must be established separately. Do not hash relocated runtime data to verify an
original file. Unknown mappings or mismatched images must not change a database.

## Code units and registers

Each code unit has `start`, `end`, `source`, `kind`, `primaryEntry`, and `entries`.
Ranges come directly from original Code payload metadata and exclude object headers.
They do not use analyzer-split stub lengths, neighboring entries or display names.
`source` is currently `snapshot`; `kind` is `dart`, `stub`, or `unknown` when shared
Code objects disagree. Category does not establish a calling convention.

`entries` contains `{rva,kind}` records. Kinds are `normal`, `monomorphic`, `unchecked`,
and `monomorphic_unchecked`. The same address may have several roles. `primaryEntry`
is a known normal entry or null. All retained entries lie inside the payload.
The payload start alone is not proof of a callable entry. ARM entries/ranges are
4-byte aligned. Identical payload ranges are consolidated without losing entry roles.

Code units must be in file-backed executable mappings. `coverage.codeUnits` reports
exported ranges, omitted unmapped ranges, invalid entry observations, and overlapping
ranges. Distinct overlapping ranges are retained as evidence, not silently truncated;
consumers must resolve or reject them. They must not build overlapping functions
automatically. Unavailable/discarded bodies are not given invented sizes.

A payload can contain padding, data, extra entries and shared slow paths. It is
an ownership boundary, not a ready-made Ghidra function body or a requirement to
disassemble every byte. This export does not prove every .text byte or runtime stub
was recovered. It does not provide exception unwind/stack-map semantics.

`registers` contains `dartSp`, `nativeSp`, `fp`, `lr`, `thread`, `pool`, and
`argumentsDescriptor`. ARM64 uses x0..x30/sp; ARM uses r0..r15; x64 uses physical
register names. LR is null on x64. These roles come from the matching SDK.
Legacy analysis observations may use fp/lr/sp aliases, which refer to target
registers, not Ghidra processor-spec display names.

Consumers implement ABI profiles, call-clobber rules, native transitions and
stub-specific contracts themselves. Per-function parameter observations are optional
evidence, not a prerequisite for the consumer's native Dart ABI implementation.

## Analysis and completeness

Every `analysis` body retains the existing declaration, source, signature, flags,
payload/monomorphic locations, CID/library, and `analyzed` flag. Analyzed bodies
add recovered parameters/incoming observations, partial flags, frame observations,
closure/type-argument observations, IL and annotations. Unknown signature/type is
null, not void; `analyzed=false` does not mean the function has no parameters.

Multiple declarations may share one entry/payload. Preserve all records; do not
convert this array to a last-value-wins address dictionary. `functions` contains
sanitized legacy display names; use the declaration names for original Dart names.
Zero lengths in that legacy view are labels or unavailable bodies, not zero-byte
functions. Use `codeUnits` for original storage ranges.

IL records are `[start,end,kind,text]`. `kind` is the current internal enum, not a
stable cross-version semantic opcode. Text, annotations and printed Dart type names
are for presentation. Do not parse them into ABI, C types, references or replacement
p-code. Where a field already marks inferred/recovered/partial information, preserve
that distinction; unmarked old observations must not be upgraded to proven facts.
Some legacy pool descriptions include analyzer-host addresses or runtime cache
values. They are opaque display text, not persistent target addresses or identities.

`coverage.declarations` and `analyzedDeclarations` count exported declarations,
including aliases, not unique code units. `available` means analysis ran, not that
all functions/parameters were recovered. `--no-analysis` keeps snapshot/layout data
and code units, marks `not_run`, and leaves each declaration unanalyzed.

## Consumers and evolution

`python scripts/generate_scripts.py output/b4a.json` derives the Frida script, IDA script/header
and `script_analysis.jsonl`. The latter is a script cache containing its generation
ID and grouped function bodies/aliases. It contains no additional analysis facts;
Thread/ObjectPool and operand records are no longer redundantly copied into it.
Legacy `script_data.json` can still be supplied manually to regenerate older scripts.

Ghidra reads `b4a.json` directly. The accompanying `ImportB4a.java` streams past
large analysis sections, verifies the original image and imports ARM64 entry labels
and range bookmarks transactionally. It preserves user symbols, rejects overlapping
ranges in this initial importer, and does not yet create function bodies or import
types/IL. Compile checks are not GUI/runtime acceptance.

Consumers may stream sections or create local indexes. Unknown optional fields may
be ignored. Incompatible meaning/type changes require a new `version`; unknown
versions must be rejected. No consumer-specific fields belong in shared snapshot
or analysis facts. New facts are added in the shared exporter rather than a second
Ghidra/IDA-specific exporter. Complete publication is independent of script generation.
