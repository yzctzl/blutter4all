"""Blutter import for IDAPython 9+. Run in the matching AOT image database."""
import json
from pathlib import Path
import ida_auto
import ida_bytes
import ida_funcs
import ida_ida
import ida_idaapi
import ida_kernwin
import ida_name
import ida_nalt
import ida_segment
import ida_typeinf
import ida_ua
import idc

# Target VA zero maps here. Override for a manually mapped AOT image.
IMAGE_BASE = None
OVERWRITE_NAMES = False
IMPORT_CLASSES = True
IMPORT_ANALYSIS = True

# @BLUTTER_DATA@


def address(offset):
    return BASE + int(offset, 16)


def executable(ea, size=1):
    segment = ida_segment.getseg(ea)
    return (segment is not None and segment.perm & ida_segment.SEGPERM_EXEC
            and ea + max(size, 1) <= segment.end_ea)


def validate_image():
    target = DATA['target']
    processor = ida_ida.inf_get_procname().lower()
    expected = 'metapc' if target['arch'] == 'x64' else 'arm'
    bits = 64 if ida_ida.inf_is_64bit() else 32
    if processor != expected or bits != target['wordSize'] * 8 or ida_ida.inf_is_be():
        raise RuntimeError('This IDB has a different architecture or byte order')
    for offset, code in DATA['image']['checks']:
        ea = address(offset)
        expected_bytes = bytes.fromhex(code)
        if not executable(ea, len(expected_bytes)) or ida_bytes.get_bytes(ea, len(expected_bytes)) != expected_bytes:
            raise RuntimeError('AOT image fingerprint mismatch; check the input and IMAGE_BASE')


def import_functions():
    counts = dict(named=0, preserved=0, functions=0, boundaryConflicts=0, failed=0)
    for offset, size, name in DATA['functions']:
        ea = address(offset)
        if not executable(ea, size):
            counts['failed'] += 1
            continue
        existing = ida_funcs.get_func(ea)
        if existing is not None and size:
            if existing.start_ea != ea or existing.end_ea != ea + size:
                counts['boundaryConflicts'] += 1
        if size and existing is None:
            if ida_funcs.add_func(ea, ea + size):
                counts['functions'] += 1
            else:
                counts['failed'] += 1
        name = ida_name.validate_name(name, ida_name.VNT_IDENT)
        if ida_name.get_name(ea) == name:
            continue
        if not OVERWRITE_NAMES and ida_bytes.has_user_name(ida_bytes.get_flags(ea)):
            counts['preserved'] += 1
            continue
        if name and ida_name.set_name(ea, name, ida_name.SN_NOWARN):
            counts['named'] += 1
        else:
            counts['failed'] += 1
    print('Blutter names/functions:', counts)


def import_structure(name, members, width=None):
    width = DATA['target']['wordSize'] if width is None else width
    tif = ida_typeinf.tinfo_t()
    if not tif.get_named_type(None, name):
        # Build once, including comments. Per-member database writes are costly
        # for object pools with hundreds of thousands of machine-word entries.
        details = ida_typeinf.udt_type_data_t()
        word_bits = width * 8
        word_type = ida_typeinf.tinfo_t(ida_typeinf.BTF_UINT32 if word_bits == 32 else ida_typeinf.BTF_UINT64)
        for offset, label, comment in members:
            member = ida_typeinf.udm_t()
            member.name = label
            member.offset = offset * 8
            member.size = word_bits
            member.type = word_type
            member.cmt = comment
            details.push_back(member)
        if (not tif.create_udt(details)
                or tif.set_named_type(None, name) != ida_typeinf.TERR_OK
                or not tif.get_named_type(None, name)):
            raise RuntimeError(f'Cannot create {name}')
    details = ida_typeinf.udt_type_data_t()
    if not tif.get_udt_details(details) or len(details) != len(members):
        raise RuntimeError(f'Existing {name} has a different layout; preserved')
    for member, (offset, label, _) in zip(details, members):
        if (member.offset != offset * 8 or member.name != label
                or member.size != width * 8):
            raise RuntimeError(f'Existing {name} has a different layout; preserved')
    tid = tif.get_tid()
    if tid == ida_idaapi.BADADDR:
        raise RuntimeError(f'No local type ID for {name}')
    return tid


def import_classes():
    slot = DATA['target']['slotSize']
    classes = DATA['classes']
    imported = failed = 0
    for cls in classes:
        if not cls or 'fields' not in cls or cls['size'] <= 0:
            continue
        # Flatten inheritance without pretending compressed references are C
        # pointers. Bitmap slots remain raw, even when a Dart type is known.
        fields = {}
        current = cls
        seen = set()
        while current and current['id'] not in seen:
            seen.add(current['id'])
            for field in current.get('fields', []):
                if not field['static']:
                    fields.setdefault(field['offset'], field)
            parent = current.get('sid', -1)
            current = classes[parent] if 0 <= parent < len(classes) else None
        bitmap = int(cls['fbitmap'], 16)
        members = []
        for offset in range(0, cls['size'], slot):
            field = fields.get(offset)
            label = f'field_{offset:x}'
            storage = 'raw native slot' if bitmap & (1 << (offset // slot)) else 'tagged slot'
            if field:
                label = ida_name.validate_name(field['name'], ida_name.VNT_IDENT) or label
                label += f'_{offset:x}'
                comment = json.dumps(field, ensure_ascii=False)
            else:
                comment = 'header/padding/type arguments or unrecovered field'
            members.append([offset, label, storage + '; ' + comment])
        members[0][2] += '\n' + json.dumps(cls, ensure_ascii=False)
        try:
            import_structure(f"DartClass_{cls['id']}", members, slot)
            imported += 1
        except Exception as error:
            failed += 1
            print(f"Blutter class {cls['id']}: {error}")
    print(f'Blutter class layouts: {imported} imported, {failed} failed')


def merge_comment(ea, text, function=False):
    prefix, suffix = '[Blutter analysis]', '[/Blutter analysis]'
    fn = ida_funcs.get_func(ea) if function else None
    if function and (fn is None or fn.start_ea != ea):
        return False
    old = (ida_funcs.get_func_cmt(fn, True) if function else ida_bytes.get_cmt(ea, False)) or ''
    start = old.find(prefix)
    end = old.find(suffix, start) if start >= 0 else -1
    block = prefix + '\n' + text + '\n' + suffix
    # Replace only our marked block; preserve the user's comments verbatim.
    new = (old[:start] + block + old[end + len(suffix):]
           if start >= 0 and end >= 0 else old + ('\n' if old else '') + block)
    if new == old:
        return True
    return (ida_funcs.set_func_cmt(fn, new, True) if function
            else ida_bytes.set_cmt(ea, new, False))


def import_analysis():
    imported = skipped = 0
    classes = {cls['id']: cls for cls in DATA['classes'] + DATA['topClasses'] if cls}
    path = Path(__file__).resolve().parent.parent / 'script_analysis.jsonl'
    with path.open(encoding='utf-8') as stream:
        if json.loads(stream.readline()) != ['@id', DATA['analysisId']]:
            raise RuntimeError('Analysis companion belongs to a different script generation')
        for line in stream:
            if line.startswith('["@'):
                continue
            offset, body = json.loads(line)
            ea = address(offset)
            if not executable(ea):
                skipped += 1
                continue
            bodies = [body] + body.get('aliases', [])
            summaries = []
            for declaration in bodies:
                summary = {key: value for key, value in declaration.items() if key not in ('il', 'annotations', 'aliases')}
                # Retain declarations and static fields without pretending Dart
                # signatures obey the platform's native C calling convention.
                summary['class'] = classes.get(declaration['cid'])
                summaries.append(summary)
            if not merge_comment(ea, json.dumps(summaries, ensure_ascii=False, indent=2), function=True):
                skipped += 1
            comments = {}
            for declaration in bodies:
                for start, end, kind, text in declaration.get('il', []):
                    if kind:  # Unknown is not a recognized semantic instruction.
                        comments.setdefault(start, set()).add(f'IL [{start}, {end}): {text}')
                for start, text in declaration.get('annotations', []):
                    comments.setdefault(start, set()).add(text)
            for start, texts in comments.items():
                target = address(start)
                if executable(target) and merge_comment(target, '\n'.join(sorted(texts))):
                    imported += 1
                else:
                    skipped += 1
    print(f'Blutter analysis: {imported} instruction comments imported, {skipped} failed/skipped')


def import_operands():
    types = {name: import_structure(name, members) for name, members in DATA['structures'].items()}
    applied = failed = preserved = 0
    insn = ida_ua.insn_t()
    for offset, operand, structure, delta in DATA['operands']:
        ea = address(offset)
        if not executable(ea) or not ida_ua.decode_insn(insn, ea):
            failed += 1
            continue
        if ida_bytes.is_defarg(ida_bytes.get_flags(ea), operand):
            preserved += 1
            continue
        if idc.op_stroff(ea, operand, types[structure], delta):
            applied += 1
        else:
            failed += 1
    print(f'Blutter structure operands: {applied} applied, {preserved} preserved, {failed} failed')


def main():
    global BASE
    if int(ida_kernwin.get_kernel_version().split('.')[0]) < 9:
        raise RuntimeError('Blutter requires IDA 9 or newer')
    BASE = ida_nalt.get_imagebase() if IMAGE_BASE is None else IMAGE_BASE
    validate_image()  # Reject a wrong IDB before making any changes.
    ida_auto.auto_wait()
    import_functions()
    try:
        import_operands()
    except Exception as error:
        print(f'Blutter type import failed (function names were imported): {error}')
    if IMPORT_CLASSES:
        import_classes()
    if IMPORT_ANALYSIS:
        import_analysis()


if __name__ == '__main__':
    main()
