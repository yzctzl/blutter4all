// Frida 17+. Metadata is initialized before module observers or hooks run.
const Config = {
    // Desktop self-mapped ELF: set imageBase OR isolateInstructions explicitly.
    imageBase: null,
    isolateInstructions: null,
    modulePath: null, // Optional exact path; ambiguous matching modules are rejected.
    maxDepth: 5,
    maxElements: 100,
    showNullFields: false,
    hooks: [
        // { name: 'exact exported function name', onEnter() {
        //     const reader = new DartReader(this.context);
        //     console.log(JSON.stringify(reader.readRegister('x0')));
        //     console.log(JSON.stringify(reader.readStackSlot(0)));
        // } }
        // Stack slot 0 is the last physical stack argument, not declaration arg 0.
    ]
};
// @BLUTTER_DATA@
const Target = Blutter.target;
const C = Blutter.constants;
const Classes = Blutter.classes;
let imageBase = null;
let moduleObserver = null;
const listeners = [];

function exactInteger(value) {
    const text = value.toString();
    const number = Number(text);
    return Number.isSafeInteger(number) ? number : text;
}

class DartReader {
    constructor(context) {
        this.context = context;
        this.active = new Set();
        this.heapBase = ptr(0);
        if (Target.compressed) {
            // HEAP_BITS packs heap_base >> 32 in its low half on ARM64.
            // x64 instead loads Thread::heap_base for compressed loads.
            this.heapBase = Target.arch === 'arm64'
                ? context.x28.shl(32)
                : context[Target.thread].add(Target.heapBaseOffset).readPointer();
        }
    }

    // Full tagged pointers in entry registers/stack are already decompressed.
    readRegister(name) {
        const value = this.context[name];
        if (value === undefined)
            throw new Error(`No register ${name} in this CPU context`);
        return this.readTagged(value);
    }

    readStackSlot(index) {
        if (!Number.isSafeInteger(index) || index < 0)
            throw new Error('Expected a nonnegative physical stack slot');
        const offset = (Target.entrySlots + index) * Target.wordSize;
        return this.readTagged(this.context[Target.stack].add(offset).readPointer());
    }

    // These are observed machine locations, not guessed Dart declaration order.
    // Keep raw values: a parameter type alone does not prove tagged storage.
    readParameters(selector, declaration = null) {
        const info = typeof selector === 'object' ? selector : functionInfo(selector);
        let body = info.analysis;
        if (body === null)
            return { $unavailable: 'Function has no code analysis' };
        if (body.aliases?.length) {
            if (!Number.isSafeInteger(declaration) || declaration < 0 || declaration > body.aliases.length)
                return { $unavailable: 'Shared entry: select a declaration index (0 = primary, 1+ = aliases)' };
            if (declaration > 0)
                body = body.aliases[declaration - 1];
        }
        if (!body.analyzed)
            return { $unavailable: 'Selected declaration has no code analysis' };
        const locations = body.incoming.length ? body.incoming : body.parameters;
        return locations.map(parameter => {
            const result = { ...parameter, raw: null };
            try {
                if (parameter.entryRegister !== null) {
                    const value = this.context[parameter.entryRegister];
                    if (value === undefined)
                        throw new Error('Register unavailable in Frida CPU context');
                    result.raw = value.toString();
                } else if (body.framePointer && parameter.fpOffset > 0) {
                    // push FP (x64), or push FP/LR (ARM). At onEnter the
                    // callee frame has not yet been established.
                    const bias = Target.wordSize * (Target.arch === 'x64' ? 1 : 2);
                    const offset = parameter.fpOffset - bias;
                    if (offset < Target.entrySlots * Target.wordSize)
                        throw new Error('Location is not an entry argument slot');
                    result.raw = this.context[Target.stack].add(offset).readPointer().toString();
                } else {
                    result.$unavailable = 'No proven entry location';
                }
            } catch (error) {
                result.$error = String(error);
            }
            return result;
        });
    }

    // Storage width differs from machine word width in compressed snapshots.
    taggedSlot(address) {
        if (Target.slotSize === 8)
            return address.readPointer();
        const value = address.readU32();
        if (Target.compressed && (value & 1) !== 0)
            return this.heapBase.add(value); // Heap references are zero-extended.
        return ptr(value);
    }

    smi(value) {
        if (Target.slotSize === 4)
            return value.toInt32() >> 1;
        // Frida Int64.shr is a logical shift; sign-extend explicitly for 64-bit Smis.
        return exactInteger(BigInt.asIntN(64, BigInt(value.toString())) >> 1n);
    }

    length(object, offset) {
        const length = this.smi(this.taggedSlot(object.add(offset)));
        if (!Number.isSafeInteger(length) || length < 0)
            throw new Error(`Invalid container length: ${length}`);
        return length;
    }

    readTagged(value, depth = Config.maxDepth) {
        if ((value.toUInt32() & 1) === 0)
            return this.smi(value);
        const address = value.sub(1);
        const cid = (address.readU32() >>> C.ClassIdTagPos) & C.ClassIdTagMask;
        const cls = Classes[cid];
        if (cls === null || cls === undefined)
            return { $address: value.toString(), $cid: cid, $error: 'Unknown CID' };
        if (cid === C.CidNull)
            return null;
        const identity = `${cls.name}@${value}`;
        if (this.active.has(identity))
            return { $ref: identity };
        if (depth <= 0)
            return { $ref: identity, $truncated: 'depth' };
        this.active.add(identity);
        try {
            return this.object(address, cls, depth);
        } catch (error) {
            return { $ref: identity, $error: String(error) };
        } finally {
            this.active.delete(identity);
        }
    }

    array(address, cls, depth, count = null) {
        const length = this.length(address, cls.lenOffset);
        if (count !== null && count > length)
            throw new Error('Backing array shorter than container length');
        const used = count === null ? length : count;
        const values = [];
        for (let i = 0; i < Math.min(used, Config.maxElements); ++i)
            values.push(this.readTagged(this.taggedSlot(address.add(cls.dataOffset + i * Target.slotSize)), depth - 1));
        if (used > Config.maxElements)
            values.push({ $truncated: used - Config.maxElements });
        return values;
    }

    backingArray(address, cls) {
        const tagged = this.taggedSlot(address.add(cls.dataOffset));
        if ((tagged.toUInt32() & 1) === 0)
            throw new Error('Invalid backing array pointer');
        const backing = tagged.sub(1);
        const cid = (backing.readU32() >>> C.ClassIdTagPos) & C.ClassIdTagMask;
        if (cid !== C.CidArray && cid !== C.CidImmutableArray)
            throw new Error('Backing object is not an array');
        return backing;
    }

    linkedHash(address, cls, depth, isMap) {
        const backing = this.backingArray(address, cls);
        const arrayClass = Classes[C.CidArray];
        const used = this.length(address, cls.usedOffset);
        const deleted = this.length(address, cls.delOffset);
        const step = isMap ? 2 : 1;
        if (used > this.length(backing, arrayClass.lenOffset) || used % step !== 0 || deleted > used / step)
            throw new Error('Invalid hash container bookkeeping');
        const entries = [];
        let scanned = 0;
        for (; scanned < Math.min(used, Config.maxElements * step); scanned += step) {
            const slot = backing.add(arrayClass.dataOffset + scanned * Target.slotSize);
            const key = this.taggedSlot(slot);
            // compact_hash: deleted keys contain the backing array itself, not null.
            if (key.equals(backing.add(1)))
                continue;
            const decoded = this.readTagged(key, depth - 1);
            entries.push(isMap ? [decoded, this.readTagged(this.taggedSlot(slot.add(Target.slotSize)), depth - 1)] : decoded);
        }
        return { $type: isMap ? 'Map' : 'Set', entries, $truncated: scanned < used };
    }

    object(address, cls, depth) {
        switch (cls.id) {
        case C.CidBool: return address.add(cls.valOffset).readU8() !== 0;
        case C.CidMint: return exactInteger(address.add(cls.valOffset).readS64());
        case C.CidDouble: {
            const value = address.add(cls.valOffset).readDouble();
            return Number.isFinite(value) ? value : String(value);
        }
        case C.CidString:
        case C.CidTwoByteString: {
            const length = this.length(address, cls.lenOffset);
            const count = Math.min(length, Config.maxElements);
            const data = address.add(cls.dataOffset);
            let text;
            if (cls.id === C.CidTwoByteString)
                text = data.readUtf16String(count);
            else {
                // Dart OneByteString stores Latin-1, not UTF-8.
                const bytes = new Uint8Array(data.readByteArray(count));
                text = Array.from(bytes, byte => String.fromCharCode(byte)).join('');
            }
            return count === length ? text : { text, $truncated: length - count };
        }
        case C.CidArray:
        case C.CidImmutableArray:
            return this.array(address, cls, depth);
        case C.CidGrowableArray:
            return this.array(this.backingArray(address, cls), Classes[C.CidArray], depth, this.length(address, cls.lenOffset));
        case C.CidMap:
        case C.CidConstMap:
            return this.linkedHash(address, cls, depth, true);
        case C.CidSet:
        case C.CidConstSet:
            return this.linkedHash(address, cls, depth, false);
        case C.CidClosure: {
            const entry = address.add(cls.epOffset).readPointer();
            const offset = imageBase === null ? null : entry.sub(imageBase).toString();
            return { $type: 'Closure', entry: entry.toString(), offset,
                function: Blutter.functions.find(row => row[0] === offset)?.[2] ?? null,
                context: this.readTagged(this.taggedSlot(address.add(cls.contextOffset)), depth - 1) };
        }
        case C.CidContext: {
            // UntaggedContext::num_variables_ is int32_t, not a tagged Smi.
            const count = address.add(cls.countOffset).readS32();
            if (count < 0)
                throw new Error('Invalid context variable count');
            const variables = [];
            for (let i = 0; i < Math.min(count, Config.maxElements); ++i)
                variables.push(this.readTagged(this.taggedSlot(address.add(cls.dataOffset + i * Target.slotSize)), depth - 1));
            return { $type: 'Context', parent: this.readTagged(this.taggedSlot(address.add(cls.parentOffset)), depth - 1),
                variables, $truncated: count > Config.maxElements };
        }
        }
        const typed = [
            [C.CidUint8Array, 1, 'readU8'], [C.CidInt8Array, 1, 'readS8'],
            [C.CidUint16Array, 2, 'readU16'], [C.CidInt16Array, 2, 'readS16'],
            [C.CidUint32Array, 4, 'readU32'], [C.CidInt32Array, 4, 'readS32'],
            [C.CidUint64Array, 8, 'readU64'], [C.CidInt64Array, 8, 'readS64'],
            [C.CidFloat32Array, 4, 'readFloat'], [C.CidFloat64Array, 8, 'readDouble']
        ].find(([cid]) => cid === cls.id);
        if (typed !== undefined) {
            const [, width, method] = typed;
            const length = this.length(address, cls.lenOffset);
            const values = [];
            for (let i = 0; i < Math.min(length, Config.maxElements); ++i) {
                const value = address.add(cls.dataOffset + i * width)[method]();
                values.push(typeof value === 'number' ? (Number.isFinite(value) ? value : String(value)) : exactInteger(value));
            }
            if (length > Config.maxElements)
                values.push({ $truncated: length - Config.maxElements });
            return values;
        }
        if (cls.id < C.NumPredefinedCids)
            return { $type: cls.name, $address: address.add(1).toString(), $unsupported: true };
        return this.instance(address, cls, depth);
    }

    instance(address, cls, depth) {
        const result = { $type: cls.name, $address: address.add(1).toString() };
        const parents = new Set();
        let count = 0;
        while (cls !== undefined && cls !== null && cls.id !== C.CidObject) {
            if (parents.has(cls.id))
                throw new Error('Cyclic class hierarchy');
            parents.add(cls.id);
            const parent = Classes[cls.sid];
            if (!parent || !Number.isSafeInteger(parent.size) || !Number.isSafeInteger(cls.size))
                throw new Error('Missing superclass layout');
            const bitmap = uint64(cls.fbitmap);
            for (let offset = parent.size; offset < cls.size; offset += Target.slotSize) {
                if (count++ >= Config.maxElements) {
                    result.$truncated = 'fields';
                    return result;
                }
                if (offset === cls.argOffset)
                    continue;
                const definition = (cls.fields || []).find(field => !field.static && field.offset === offset);
                const field = definition && definition.name
                    ? `${definition.name}@${offset.toString(16)}` : `off_${offset.toString(16)}`;
                try {
                    const bit = offset / Target.slotSize;
                    if (bit < 64 && bitmap.shr(bit).and(1).toString() === '1') {
                        // Decode native numbers only with a snapshot declaration
                        // AND a bitmap proving the full eight-byte storage range.
                        const slots = 8 / Target.slotSize;
                        const mask = (1 << slots) - 1;
                        const numeric = definition && definition.source === 'snapshot'
                            && ['int', 'double'].includes(definition.type)
                            && offset + 8 <= cls.size && bit + slots <= 64
                            && bitmap.shr(bit).and(mask).toString() === String(mask);
                        if (numeric) {
                            const value = definition.type === 'int'
                                ? exactInteger(address.add(offset).readS64()) : address.add(offset).readDouble();
                            result[field] = typeof value === 'number' && !Number.isFinite(value) ? String(value) : value;
                            offset += 8 - Target.slotSize;
                        } else {
                            result[field] = { $raw: Target.slotSize === 4
                                ? ptr(address.add(offset).readU32()).toString()
                                : address.add(offset).readPointer().toString() };
                        }
                    } else {
                        const value = this.readTagged(this.taggedSlot(address.add(offset)), depth - 1);
                        if (value !== null || Config.showNullFields)
                            result[field] = value;
                    }
                } catch (error) {
                    result[field] = { $error: String(error) };
                }
            }
            cls = parent;
        }
        return result;
    }
}

function findFunctions(query, limit = Config.maxElements) {
    if (!Number.isSafeInteger(limit) || limit < 1)
        throw new Error('Expected a positive result limit');
    const result = [];
    for (const [offset, size, name] of Blutter.functions) {
        if (!name.includes(query))
            continue;
        result.push({ offset, size, name });
        if (result.length === limit)
            break;
    }
    return result;
}

function functionInfo(selector) {
    const key = /^0x[0-9a-f]+$/i.test(selector) ? ptr(selector).toString() : selector;
    const matches = Blutter.functions.filter(row => row[0] === key || row[2] === key);
    if (matches.length === 0 || (matches.length > 1 && !key.startsWith('0x')))
        throw new Error(`Function selector must match one entry (${matches.length} matches): ${selector}`);
    const [offset, size, name] = matches[0];
    const encoded = Blutter.analysis[offset];
    return { offset, size, name,
        aliases: Blutter.functions.filter(row => row[0] === offset).map(row => row[2]),
        analysis: encoded ?? null };
}

let analysisRequest = 0;
function queryAnalysis(offset) {
    const reply = `blutter-analysis-${++analysisRequest}`;
    return new Promise((resolve, reject) => {
        const timer = setTimeout(() => reject(new Error('Full analysis requires the generate_scripts.py --attach host')), 10000);
        recv(reply, response => {
            clearTimeout(timer);
            if (response.error !== undefined) {
                reject(new Error(response.error));
                return;
            }
            resolve(response.body);
        });
        send({ type: 'blutter-analysis', offset, reply, id: Blutter.analysisId });
    });
}

async function analysis(selector) {
    const info = functionInfo(selector);
    if (info.analysis === null)
        Blutter.analysis[info.offset] = await queryAnalysis(info.offset);
    return functionInfo(info.offset);
}

function lookup(kind) {
    if (!['structures', 'operands'].includes(kind))
        throw new Error('Expected structures or operands');
    return queryAnalysis('@' + kind);
}

function hookOffset(hook) {
    if (hook.offset !== undefined && hook.name !== undefined)
        throw new Error('Specify hook offset or name, not both');
    if (hook.name !== undefined)
        return functionInfo(hook.name).offset;
    if (!/^0x[0-9a-f]+$/i.test(hook.offset))
        throw new Error('Expected a hexadecimal hook offset or an exact function name');
    return hook.offset;
}

function hookFunction(selector, callbacks) {
    if (imageBase === null)
        throw new Error('AOT image has not been verified yet');
    const info = functionInfo(selector);
    const address = imageBase.add(info.offset);
    const range = Process.findRangeByAddress(address);
    if (range === null || !range.protection.includes('x'))
        throw new Error('Function entry is not executable');
    const listener = Interceptor.attach(address, callbacks);
    listeners.push(listener);
    return listener;
}

function matchesImage(base) {
    return Blutter.image.checks.every(([offset, hex]) => {
        const address = base.add(offset);
        const range = Process.findRangeByAddress(address);
        if (range === null || !range.protection.includes('x') || address.add(hex.length / 2).compare(range.base.add(range.size)) > 0)
            return false;
        try {
            const actual = new Uint8Array(address.readByteArray(hex.length / 2));
            return Array.from(actual, byte => byte.toString(16).padStart(2, '0')).join('') === hex;
        } catch (_) {
            return false;
        }
    });
}

function attachImage(base) {
    if (!matchesImage(base))
        throw new Error('AOT image fingerprint mismatch; verify imageBase/anchor');
    // Validate all requested hooks before installing the first one.
    const hooks = Config.hooks.map(hook => ({ ...hook, offset: hookOffset(hook) }));
    for (const hook of hooks) {
        const address = base.add(hook.offset);
        const range = Process.findRangeByAddress(address);
        if (range === null || !range.protection.includes('x'))
            throw new Error(`Hook ${hook.offset} is not executable`);
    }
    imageBase = base;
    for (const hook of hooks) {
        const { offset, name, ...callbacks } = hook;
        listeners.push(Interceptor.attach(base.add(offset), callbacks));
    }
    console.log(`Blutter: verified ${Target.os}/${Target.arch} AOT image at ${base}; ${listeners.length} hooks`);
}

function start() {
    if (Process.arch !== Target.arch || Process.pointerSize !== Target.wordSize)
        throw new Error('Script and process architectures differ');
    const platform = { android: 'linux', linux: 'linux', windows: 'windows', macos: 'darwin', ios: 'darwin' }[Target.os];
    if (Process.platform !== platform)
        throw new Error('Script and process platforms differ');
    if (Config.imageBase !== null || Config.isolateInstructions !== null) {
        const base = Config.imageBase !== null ? ptr(Config.imageBase)
            : ptr(Config.isolateInstructions).sub(Blutter.image.isolateInstructions);
        attachImage(base);
        return;
    }
    const candidates = () => Process.enumerateModules().filter(module =>
        (Config.modulePath === null || module.path === Config.modulePath) && matchesImage(module.base));
    const existing = candidates();
    if (existing.length > 1)
        throw new Error('Multiple matching AOT modules; specify modulePath or imageBase');
    if (existing.length === 1)
        attachImage(existing[0].base);
    moduleObserver = Process.attachModuleObserver({
        onAdded(module) {
            if ((Config.modulePath !== null && module.path !== Config.modulePath) || !matchesImage(module.base))
                return;
            if (imageBase !== null) {
                if (!imageBase.equals(module.base))
                    console.error('Blutter: another matching AOT image appeared; existing selection retained');
                return;
            }
            attachImage(module.base);
        },
        onRemoved(module) {
            if (imageBase !== null && imageBase.equals(module.base)) {
                listeners.splice(0).forEach(listener => listener.detach());
                imageBase = null;
            }
        }
    });
    if (imageBase === null)
        console.log('Blutter: waiting for AOT module; self-mapped ELF requires Config.imageBase or Config.isolateInstructions');
}

globalThis.BlutterAPI = {
    DartReader, Config, findFunctions, functionInfo, analysis, lookup, hook: hookFunction,
    // Layouts and function index are local; full bodies are fetched by analysis().
    metadata: Blutter,
    get imageBase() { return imageBase; }
};
start();
