"""Publish and read b4a's tool-independent, versioned analysis document."""
import hashlib
import json
from pathlib import Path
import re
from struct import unpack


def _address(value):
    if not isinstance(value, str) or not re.fullmatch(r'0x[0-9a-f]+', value):
        raise ValueError(f'Invalid target address: {value!r}')
    number = int(value, 16)
    if number >= 1 << 64:
        raise ValueError('Target address exceeds 64 bits')
    return number


def _image_info(path, arch):
    # Reuse the same LIEF selection and snapshot validation as the CLI. Only the
    # FAT container table is consulted for the exact original slice byte count.
    import lief
    if __package__:
        from .extract_dart_info import _read_binary, _snapshot_info
    else:
        from extract_dart_info import _read_binary, _snapshot_info
    image, owner, outer_offset = _read_binary(str(path), arch)
    snapshot_hash, flags, _, os_name = _snapshot_info(str(path), image, outer_offset)
    apple = isinstance(image, lief.MachO.Binary)
    offset = outer_offset + image.fat_offset if apple else 0
    length = path.stat().st_size
    with path.open('rb') as stream:
        magic = stream.read(4)
        if magic in (b'\xca\xfe\xba\xbe', b'\xca\xfe\xba\xbf'):
            count, = unpack('>I', stream.read(4))
            wide = magic[-1] == 0xbf
            record_size = 32 if wide else 20
            if count > (length - 8) // record_size:
                raise ValueError('Truncated universal slice table')
            matches = []
            for _ in range(count):
                record = stream.read(record_size)
                values = unpack('>IIQQII' if wide else '>IIIII', record)
                if values[2] == offset:
                    matches.append(values[3])
            if len(matches) != 1:
                raise ValueError('Cannot identify original Mach-O slice bytes')
            length = matches[0]
        if offset < 0 or not 0 < length <= path.stat().st_size - offset:
            raise ValueError('Invalid image slice range')
        digest = hashlib.sha256()
        stream.seek(offset)
        remaining = length
        while remaining:
            block = stream.read(min(remaining, 1 << 20))
            if not block:
                raise ValueError('Truncated image while hashing')
            digest.update(block)
            remaining -= len(block)
    segments = []
    for segment in image.segments:
        if apple:
            if segment.name == '__PAGEZERO' or not segment.virtual_size:
                continue
            memory_size, file_size = segment.virtual_size, segment.file_size
            permissions = int(segment.init_protection)
            access = ''.join(c if permissions & bit else '-' for c, bit in zip('rwx', (1, 2, 4)))
        else:
            if segment.type != lief.ELF.Segment.TYPE.LOAD or not segment.virtual_size:
                continue
            memory_size, file_size = segment.virtual_size, segment.physical_size
            access = ''.join(c if segment.has(flag) else '-' for c, flag in zip(
                'rwx', (lief.ELF.Segment.FLAGS.R, lief.ELF.Segment.FLAGS.W, lief.ELF.Segment.FLAGS.X)))
        segments.append(dict(rva=hex(segment.virtual_address), memorySize=memory_size,
                             fileOffset=hex(segment.file_offset), fileSize=file_size, permissions=access))
    return dict(format='macho' if apple else 'elf', sha256=digest.hexdigest(),
                preferredBase='0x0', sliceOffset=hex(offset), fileSize=length,
                segments=sorted(segments, key=lambda s: _address(s['rva']))), snapshot_hash, flags, os_name


def validate_data(data):
    """Validate public structural invariants before any consumer makes changes."""
    if data.get('format') != 'b4a' or type(data.get('version')) is not int or data['version'] != 1:
        raise ValueError('Unsupported b4a data format/version')
    for key in ('producer', 'target', 'image', 'registers', 'codeUnits', 'coverage',
                'constants', 'classes', 'topClasses', 'functions', 'structures', 'operands', 'analysis'):
        if key not in data:
            raise ValueError(f'Missing b4a section: {key}')
    target, image = data['target'], data['image']
    arch, word = target['arch'], target['wordSize']
    if arch not in ('arm', 'arm64', 'x64') or word != (4 if arch == 'arm' else 8):
        raise ValueError('Inconsistent b4a architecture/word size')
    if target['endian'] != 'little' or target['slotSize'] != (4 if target['compressed'] else word):
        raise ValueError('Inconsistent b4a byte order/object slot width')
    if target['os'] not in ('android', 'ios', 'macos', 'linux', 'windows'):
        raise ValueError('Unsupported target platform')
    if image['format'] not in ('elf', 'macho') or image['preferredBase'] != '0x0':
        raise ValueError('Unsupported image mapping')
    if not re.fullmatch('[0-9a-f]{64}', image['sha256']):
        raise ValueError('Invalid binary SHA-256')
    if not re.fullmatch('[0-9a-f]{32}', target['snapshotHash']):
        raise ValueError('Invalid snapshot compatibility hash')
    end = 0
    executable = []
    for segment in image['segments']:
        start, file_offset = _address(segment['rva']), _address(segment['fileOffset'])
        size, file_size = segment['memorySize'], segment['fileSize']
        if any(type(n) is not int or not 0 <= n < 1 << 53 for n in (size, file_size)):
            raise ValueError('Invalid segment size')
        if start < end or size == 0 or start + size >= 1 << 64 or file_size > size:
            raise ValueError('Overlapping/invalid image segment')
        if file_offset + file_size > image['fileSize']:
            raise ValueError('Segment extends beyond original image')
        if not re.fullmatch('[r-][w-][x-]', segment['permissions']):
            raise ValueError('Invalid segment permissions')
        end = start + size
        if segment['permissions'][2] == 'x':
            executable.append((start, start + file_size))
    if not executable or not image['segments'] or image['segments'][0]['rva'] != '0x0':
        raise ValueError('Missing zero-based/executable image mapping')
    roles = ('dartSp', 'nativeSp', 'fp', 'lr', 'thread', 'pool', 'argumentsDescriptor')
    for role in roles:
        value = data['registers'][role]
        if value is not None and (not isinstance(value, str) or not re.fullmatch('[a-z][a-z0-9]*', value)):
            raise ValueError('Invalid physical register name')
    previous = -1
    for unit in data['codeUnits']:
        start, end = _address(unit['start']), _address(unit['end'])
        if start < previous or not any(lo <= start < end <= hi for lo, hi in executable):
            raise ValueError('Unsorted or non-file-backed code range')
        previous = start
        if arch != 'x64' and (start % 4 or end % 4):
            raise ValueError('Unaligned ARM code range')
        if unit['source'] != 'snapshot' or unit['kind'] not in ('dart', 'stub', 'unknown'):
            raise ValueError('Invalid code provenance/category')
        entries = set()
        for entry in unit['entries']:
            address = _address(entry['rva'])
            if not start <= address < end or (arch != 'x64' and address % 4):
                raise ValueError('Code entry outside payload or unaligned')
            if entry['kind'] not in ('normal', 'monomorphic', 'unchecked', 'monomorphic_unchecked'):
                raise ValueError('Invalid entry kind')
            entries.add(entry['rva'])
        if unit['primaryEntry'] is not None and unit['primaryEntry'] not in entries:
            raise ValueError('Primary entry missing from entry list')
    if data['analysisState'] not in ('available', 'not_run'):
        raise ValueError('Invalid analysis stage state')
    if not isinstance(data['analysis'], list):
        raise ValueError('Analysis declarations must preserve duplicate entry records')
    return data


def read_data(path):
    with Path(path).open(encoding='utf-8') as stream:
        return validate_data(json.load(stream))


def publish_data(binary, raw, output):
    """Finish SDK facts with original-file identity, then atomically publish."""
    raw, output = Path(raw), Path(output)
    with raw.open(encoding='utf-8') as stream:
        data = json.load(stream)
    if data.get('schema') != 1 or 'codeUnits' not in data or 'registers' not in data:
        raise ValueError('Analyzer export is outdated; rerun b4a with --rebuild')
    info, snapshot_hash, flags, os_name = _image_info(Path(binary), data['target']['arch'])
    if os_name != data['target']['os'] or ('compressed-pointers' in flags) != data['target']['compressed']:
        raise ValueError('Analyzer target does not match original snapshot')
    data.pop('schema')
    data.update(format='b4a', version=1, producer=dict(name='b4a', revision=None))
    data['target'].update(endian='little', snapshotHash=snapshot_hash, snapshotFlags=flags)
    data['image'].update(info)
    # Consolidate physical code storage, retaining every distinct entry role.
    units, omitted, invalid_entries = {}, 0, 0
    executable = [(int(s['rva'], 16), int(s['rva'], 16) + s['fileSize'])
                  for s in info['segments'] if s['permissions'][2] == 'x']
    for unit in data['codeUnits']:
        start, end = _address(unit['start']), _address(unit['end'])
        if not any(lo <= start < end <= hi for lo, hi in executable):
            omitted += 1
            continue
        key = (start, end)
        merged = units.setdefault(key, dict(unit, entries=[]))
        if merged['kind'] != unit['kind']:
            merged['kind'] = 'unknown'
        for entry in unit['entries']:
            if not start <= _address(entry['rva']) < end:
                invalid_entries += 1
            elif entry not in merged['entries']:
                merged['entries'].append(entry)
        if not any(e['rva'] == merged['primaryEntry'] for e in merged['entries']):
            merged['primaryEntry'] = None
    data['codeUnits'] = [units[key] for key in sorted(units)]
    overlaps, active_end = 0, 0
    for unit in data['codeUnits']:
        start, end = int(unit['start'], 16), int(unit['end'], 16)
        overlaps += start < active_end
        active_end = max(active_end, end)
    data['coverage'] = dict(codeUnits=dict(exported=len(units), omittedRanges=omitted,
                                         invalidEntries=invalid_entries, overlappingRanges=overlaps),
                            analyzedDeclarations=sum(bool(body.get('analyzed')) for _, body in data['analysis']),
                            declarations=len(data['analysis']))
    validate_data(data)
    temporary = output.with_name(output.name + '.tmp')
    try:
        with temporary.open('w', encoding='utf-8') as stream:
            json.dump(data, stream, ensure_ascii=True, separators=(',', ':'), allow_nan=False)
            stream.write('\n')
        temporary.replace(output)
    finally:
        temporary.unlink(missing_ok=True)
    raw.unlink()
    return output
