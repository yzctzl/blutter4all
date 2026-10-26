"""Render Frida 17+ and IDAPython 9+ scripts from b4a.json."""
import argparse
import json
from pathlib import Path
import re
import threading
import uuid


TEMPLATES = Path(__file__).resolve().parent / 'scripts'


def generate_scripts(metadata, outdir=None):
    metadata = Path(metadata)
    data = json.loads(metadata.read_text(encoding='utf-8'))
    if data.get('format') == 'b4a':
        from b4a_data import validate_data
        validate_data(data)
    elif data.get('schema') != 1:
        raise ValueError('Unsupported script metadata version; rebuild blutter')
    target = data['target']
    arch = target['arch']
    if arch not in ('arm', 'arm64', 'x64'):
        raise ValueError(f'Unsupported script architecture: {arch}')
    word = target['wordSize']
    slot = target['slotSize']
    if word != (4 if arch == 'arm' else 8) or slot != (4 if target['compressed'] else word):
        raise ValueError('Inconsistent target word/object-slot sizes')
    if not data['image']['checks']:
        raise ValueError('No code fingerprints available to verify the target image')
    # Keep exact integer strings intact. Metadata contains target VAs, never host pointers.
    for offset, code in data['image']['checks']:
        if int(offset, 16) < 0 or not re.fullmatch(r'[0-9a-f]{32}', code):
            raise ValueError('Invalid image fingerprint')
    outdir = Path(outdir) if outdir is not None else metadata.parent
    outdir.mkdir(parents=True, exist_ok=True)
    if 'analysis' not in data:
        raise ValueError('Missing semantic analysis export; rebuild blutter')
    # Stream full bodies to IDA and serve individual bodies to Frida on demand.
    # Do not inject hundreds of MB of IL into a mobile application process.
    analysis_id = uuid.uuid4().hex
    with (outdir / 'script_analysis.jsonl').open('w', encoding='utf-8') as stream:
        stream.write(json.dumps(['@id', analysis_id]) + '\n')
        bodies = data.pop('analysis')
        # Several declarations may share machine code (canonical tear-offs,
        # getters, etc.). Preserve every declaration instead of JSON last-wins.
        aliases = {}
        for offset, body in (bodies.items() if isinstance(bodies, dict) else bodies):
            if offset in aliases:
                aliases[offset].setdefault('aliases', []).append(body)
            else:
                aliases[offset] = body
        for offset, body in aliases.items():
            stream.write(json.dumps([offset, body], ensure_ascii=True, separators=(',', ':')) + '\n')
        del bodies, aliases
    frida = {key: data[key] for key in ('target', 'image', 'constants', 'classes', 'topClasses', 'functions')}
    frida['analysis'] = {}
    frida['analysisId'] = analysis_id
    js = (TEMPLATES / 'frida.template.js').read_text(encoding='utf-8')
    js = js.replace('// @BLUTTER_DATA@', 'const Blutter = JSON.parse(' + json.dumps(json.dumps(frida, ensure_ascii=True, separators=(',', ':'))) + ');')
    (outdir / 'blutter_frida.js').write_text(js, encoding='utf-8')

    # Member offsets come from the SDK. Sanitize C identifiers without changing offsets.
    headers = {}
    ctype = 'unsigned int' if word == 4 else 'unsigned long long'
    for name, members in data['structures'].items():
        lines = [f'typedef struct {name} {{']
        position = 0
        for member in members:
            offset, label, _ = member
            if offset != position:
                raise ValueError(f'Noncontiguous SDK layout: {name}+{offset:#x}')
            label = re.sub(r'[^a-zA-Z0-9_]', '_', label)
            # Offset suffix makes identifiers unique even after sanitization.
            member[1] = f'field_{label}_{offset:x}'
            lines.append(f'    {ctype} {member[1]};')
            position += word
        lines.append(f'}} {name};')
        headers[name] = '\n'.join(lines)
    ida = {key: data[key] for key in ('target', 'image', 'functions', 'structures', 'operands', 'classes', 'topClasses', 'constants')}
    ida['analysisId'] = analysis_id
    dest = outdir / 'ida_script'
    dest.mkdir(exist_ok=True)
    script = (TEMPLATES / 'ida.template.py').read_text(encoding='utf-8')
    # One string literal, not millions of Python call/AST nodes. repr escapes quotes safely.
    script = script.replace('# @BLUTTER_DATA@', 'DATA = json.loads(' + repr(json.dumps(ida, ensure_ascii=True, separators=(',', ':'))) + ')')
    (dest / 'addNames.py').write_text(script, encoding='utf-8')
    (dest / 'ida_dart_struct.h').write_text('\n\n'.join(headers.values()) + '\n', encoding='utf-8')


def attach_frida(outdir, process, device_id=None, script_path=None):
    import frida  # Optional: only needed when attaching, never for generation.
    outdir = Path(outdir)
    positions = {}
    with (outdir / 'script_analysis.jsonl').open('rb') as stream:
        analysis_id = json.loads(stream.readline())[1]
        while True:
            position = stream.tell()
            line = stream.readline()
            if not line:
                break
            offset = json.loads(line[:line.index(b',')].decode('ascii')[1:])
            positions[offset] = (position, len(line))
    device = frida.get_device(device_id) if device_id else frida.get_local_device()
    session = device.attach(int(process) if process.isdecimal() else process)
    done = threading.Event()
    session.on('detached', lambda *args: done.set())
    try:
        script = session.create_script(Path(script_path or outdir / 'blutter_frida.js').read_text(encoding='utf-8'))

        def on_message(message, binary):
            payload = message.get('payload', {})
            if message['type'] != 'send' or not isinstance(payload, dict) or payload.get('type') != 'blutter-analysis':
                print(message.get('stack', payload if message['type'] == 'send' else message), flush=True)
                return
            response = {'type': payload['reply']}
            try:
                if payload.get('id') != analysis_id:
                    raise ValueError('Analysis companion belongs to a different script generation')
                position, length = positions[payload['offset']]
                with (outdir / 'script_analysis.jsonl').open('rb') as stream:
                    stream.seek(position)
                    response['body'] = json.loads(stream.read(length))[1]
            except Exception as error:
                response['error'] = str(error)
            script.post(response)

        script.on('message', on_message)
        script.load()
        print('Blutter attached; full function analysis is available on demand. Ctrl-C to detach.', flush=True)
        done.wait()
    except KeyboardInterrupt:
        pass
    finally:
        try:
            session.detach()
        except frida.InvalidOperationError:  # The target may have exited first.
            pass


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('metadata', help='b4a.json (legacy script_data.json is also accepted)')
    parser.add_argument('-o', '--outdir', help='defaults to the metadata directory')
    parser.add_argument('--attach', metavar='PID_OR_NAME', help='attach using Frida 17+ and serve full analysis')
    parser.add_argument('--device', help='Frida device ID (default: local)')
    parser.add_argument('--script', help='customized generated Frida script to load with --attach')
    args = parser.parse_args()
    if args.attach:
        attach_frida(args.outdir or Path(args.metadata).parent, args.attach, args.device, args.script)
    else:
        generate_scripts(args.metadata, args.outdir)
