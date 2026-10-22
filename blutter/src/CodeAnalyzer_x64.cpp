#include "pch.h"
#include "ObjectPool.h"
#include "CodeAnalyzer.h"
#include "DartApp.h"
#include "DartThreadInfo.h"
#include <cstdio>
#include <unordered_set>

#ifndef NO_CODE_ANALYSIS
namespace {
using Reg = X64::Register;

bool reg(const cs_x86_op& op, x86_reg value) {
    return op.type == X86_OP_REG && op.reg == value;
}
bool memory(const cs_x86_op& op, x86_reg base) {
    return op.type == X86_OP_MEM && op.mem.base == base &&
        op.mem.index == X86_REG_INVALID && op.mem.segment == X86_REG_INVALID;
}
bool inGroup(const cs_insn* insn, uint8_t group) {
    return std::find(insn->detail->groups, insn->detail->groups + insn->detail->groups_count, group) !=
        insn->detail->groups + insn->detail->groups_count;
}
bool move(unsigned id) { return id == X86_INS_MOV || id == X86_INS_MOVABS; }

bool poolOffset(DartApp& app, const cs_x86_op& op, intptr_t& offset) {
    // Unlike ARM64, x64 PP is tagged. Assembler::LoadWordFromPoolIndex.
    if (!memory(op, CSREG_DART_PP)) return false;
    offset = op.mem.disp + dart::kHeapObjectTag;
    const auto first = dart::ObjectPool::element_offset(0);
    return offset >= first && (offset - first) % dart::kWordSize == 0 &&
        PoolIndexFromOffset(offset) < app.GetObjectPool().Length();
}
}

AsmTexts CodeAnalyzer::convertAsm(AsmInstructions& instructions)
{
    std::vector<AsmText> texts(instructions.Count());
    uint64_t stackLimit = 0;
    int maxParamOffset = 0;
    for (size_t i = 0; i < instructions.Count(); ++i) {
        const auto* insn = instructions.Ptr(i);
        auto& text = texts[i];
        text.addr = insn->address;
        text.dataType = AsmText::None;
        std::snprintf(text.text, sizeof(text.text), "%-16s%s", insn->mnemonic, insn->op_str);
        const auto& x = insn->detail->x86;
        for (unsigned j = 0; j < x.op_count; ++j) {
            const auto& op = x.operands[j];
            if (memory(op, CSREG_DART_THR) && op.mem.disp >= 0) {
                text.dataType = AsmText::ThreadOffset;
                text.threadOffset = op.mem.disp;
                if (!stackLimit && op.mem.disp == AOT_Thread_stack_limit_offset)
                    stackLimit = insn->address;
            }
            // Pool bounds are checked in asm2il, where the app is available.
            if (memory(op, X86_REG_RBP) && op.mem.disp >= 16 && op.mem.disp < 0x10000)
                maxParamOffset = std::max(maxParamOffset, static_cast<int>(op.mem.disp));
        }
        if (insn->id == X86_INS_CALL && x.op_count == 1 && x.operands[0].type == X86_OP_IMM) {
            text.dataType = AsmText::Call;
            text.callAddress = x.operands[0].imm;
        }
    }
    return AsmTexts{std::move(texts), stackLimit, maxParamOffset};
}

void CodeAnalyzer::asm2il(DartFunction* dartFn, AsmInstructions& instructions)
{
    auto& data = *dartFn->GetAnalyzedData();
    const auto count = instructions.Count();
    for (size_t i = 0; i < count; ++i) {
        const auto& x = instructions.Ptr(i)->detail->x86;
        for (unsigned j = 0; j < x.op_count; ++j) {
            intptr_t offset;
            if (poolOffset(app, x.operands[j], offset)) {
                auto& text = data.asmTexts.AtAddr(instructions.Ptr(i)->address);
                text.dataType = AsmText::PoolOffset;
                text.poolOffset = offset;
            }
        }
    }
    // Track only classes justified by a concrete pool object or allocation
    // stub. Facts stop at branch targets, control transfers and register writes.
    // In particular, an odd displacement alone does not prove a Dart field.
    std::array<DartClass*, Reg::kNumberOfRegisters> objects{};
    std::unordered_set<uint64_t> targets;
    for (size_t j = 0; j < count; ++j) {
        const auto* current = instructions.Ptr(j);
        const auto& x = current->detail->x86;
        if (inGroup(current, CS_GRP_JUMP) && x.op_count == 1 && x.operands[0].type == X86_OP_IMM)
            targets.insert(x.operands[0].imm);
    }
    // Lookahead is always bounded by the decoded instruction array. No assumed
    // byte width, sentinel instruction, or speculative reads past the function.
    for (size_t i = 0; i < count;) {
        auto* insn = instructions.Ptr(i);
        if (targets.contains(insn->address)) objects.fill(nullptr);
        const auto& x = insn->detail->x86;
        const auto* op = x.operands;
        auto n = [&](size_t k, unsigned id) {
            return i + k < count && (!k || !targets.contains(instructions.Ptr(i + k)->address)) &&
                instructions.Ptr(i + k)->id == id;
        };
        auto operands = [&](size_t k) { return instructions.Ptr(i + k)->detail->x86.operands; };
        auto ar = [&](size_t length) {
            const auto* last = instructions.Ptr(i + length - 1);
            return AddrRange(insn->address, last->address + last->size);
        };
        auto emit = [&](std::unique_ptr<ILInstr> il, size_t length = 1) {
            DartClass* result = nullptr;
            Reg resultReg;
            if (il->Kind() == ILInstr::MoveReg) {
                const auto* mv = static_cast<MoveRegInstr*>(il.get());
                resultReg = mv->dstReg;
                result = objects[mv->srcReg];
            } else if (il->Kind() == ILInstr::LoadValue) {
                const auto* load = static_cast<LoadValueInstr*>(il.get());
                auto cid = load->val.Value()->RawTypeId();
                if (load->val.storage.kind == VarStorage::Pool) {
                    const auto index = PoolIndexFromOffset(load->val.storage.offset);
                    const auto& pool = app.GetObjectPool();
                    cid = dart::kIllegalCid;
                    if (pool.TypeAt(index) == dart::ObjectPool::EntryType::kTaggedObject) {
                        const auto& object = dart::Object::Handle(pool.ObjectAt(index));
                        if (!object.IsSmi()) cid = object.GetClassId();
                    }
                }
                resultReg = load->dstReg;
                if (cid > 0 && cid < app.classes.size()) result = app.classes[cid];
            } else if (il->Kind() == ILInstr::Call) {
                auto* fn = static_cast<CallInstr*>(il.get())->GetFunction();
                if (fn && fn->ReturnType() != dart::kIllegalCid && fn->ReturnType() < app.classes.size()) {
                    resultReg = Reg{dart::CallingConventions::kReturnReg};
                    result = app.classes[fn->ReturnType()];
                }
            }
            for (size_t j = 0; j < length; ++j) {
                const auto* current = instructions.Ptr(i + j);
                if (inGroup(current, CS_GRP_JUMP) || inGroup(current, CS_GRP_CALL) || inGroup(current, CS_GRP_RET))
                    objects.fill(nullptr);
                const auto& detail = *current->detail;
                for (unsigned k = 0; k < detail.x86.op_count; ++k) {
                    const auto& operand = detail.x86.operands[k];
                    if (operand.type == X86_OP_REG && (operand.access & CS_AC_WRITE)) {
                        const Reg dst{operand.reg};
                        if (dst.IsSet()) objects[dst] = nullptr;
                    }
                }
                for (unsigned k = 0; k < detail.regs_write_count; ++k) {
                    const Reg dst{static_cast<x86_reg>(detail.regs_write[k])};
                    if (dst.IsSet()) objects[dst] = nullptr;
                }
            }
            if (resultReg.IsSet()) objects[resultReg] = result;
            data.AddIL(std::move(il));
            i += length;
        };

        if (n(0, X86_INS_PUSH) && x.op_count == 1 && reg(op[0], X86_REG_RBP) &&
            n(1, X86_INS_MOV) && reg(operands(1)[0], X86_REG_RBP) && reg(operands(1)[1], X86_REG_RSP)) {
            data.useFramePointer = true;
            emit(std::make_unique<EnterFrameInstr>(ar(2)), 2);
            continue;
        }
        if (n(0, X86_INS_MOV) && x.op_count == 2 && reg(op[0], X86_REG_RSP) && reg(op[1], X86_REG_RBP) &&
            n(1, X86_INS_POP) && reg(operands(1)[0], X86_REG_RBP)) {
            emit(std::make_unique<LeaveFrameInstr>(ar(2)), 2);
            continue;
        }
        if (n(0, X86_INS_SUB) && x.op_count == 2 && reg(op[0], X86_REG_RSP) &&
            op[1].type == X86_OP_IMM && op[1].imm > 0 && op[1].imm < 0x100000) {
            data.stackSize = static_cast<uint32_t>(op[1].imm);
            emit(std::make_unique<AllocateStackInstr>(ar(1), data.stackSize));
            continue;
        }
        // CheckStackOverflowInstr::EmitNativeCode: cmp rsp, [THR+limit]; jbe slow.
        if (n(0, X86_INS_CMP) && x.op_count == 2 && reg(op[0], X86_REG_RSP) &&
            memory(op[1], CSREG_DART_THR) && op[1].mem.disp == AOT_Thread_stack_limit_offset && n(1, X86_INS_JBE)) {
            data.firstCheckStackOverflowAddr = insn->address;
            emit(std::make_unique<CheckStackOverflowInstr>(ar(2), operands(1)[0].imm), 2);
            continue;
        }
        if (n(0, X86_INS_RET)) {
            data.last_ret = insn;
            emit(std::make_unique<ReturnInstr>(ar(1)));
            continue;
        }
        if (n(0, X86_INS_CALL) && x.op_count == 1) {
            if (op[0].type == X86_OP_IMM) {
                const auto target = static_cast<uint64_t>(op[0].imm);
                emit(std::make_unique<CallInstr>(ar(1), app.GetFunction(target), target));
                continue;
            }
            // AOT patchable calls may address an immediate pool entry directly.
            intptr_t offset;
            if (poolOffset(app, op[0], offset)) {
                const auto& pool = app.GetObjectPool();
                const auto index = PoolIndexFromOffset(offset);
                if (pool.TypeAt(index) == dart::ObjectPool::EntryType::kImmediate) {
                    const auto target = pool.RawValueAt(index) - app.base();
                    if (auto* fn = app.GetFunction(target)) {
                        emit(std::make_unique<CallInstr>(ar(1), fn, target));
                        continue;
                    }
                }
            }
            if (memory(op[0], CSREG_DART_THR) && GetThreadLeafFunction(op[0].mem.disp)) {
                emit(std::make_unique<CallLeafRuntimeInstr>(ar(1), op[0].mem.disp));
                continue;
            }
        }
        // Resolve only adjacent, complete entry-load/call sequences. Register
        // calls elsewhere remain unknown; there is no speculative propagation
        // through branches or native ABI boundaries.
        if (n(0, X86_INS_MOV) && x.op_count == 2 && op[0].type == X86_OP_REG && op[0].size == 8) {
            size_t call = 1;
            if (reg(op[0], X86_REG_RCX) && n(1, X86_INS_MOV) && reg(operands(1)[0], X86_REG_RBX) &&
                memory(operands(1)[1], CSREG_DART_PP)) call = 2;
            if (n(call, X86_INS_CALL) && reg(operands(call)[0], op[0].reg)) {
                intptr_t offset;
                if (poolOffset(app, op[1], offset)) {
                    const auto& pool = app.GetObjectPool();
                    const auto index = PoolIndexFromOffset(offset);
                    if (pool.TypeAt(index) == dart::ObjectPool::EntryType::kImmediate) {
                        const auto target = pool.RawValueAt(index) - app.base();
                        if (auto* fn = app.GetFunction(target)) {
                            emit(std::make_unique<CallInstr>(ar(call + 1), fn, target), call + 1);
                            continue;
                        }
                    }
                }
                if (call == 1 && memory(op[1], CSREG_DART_THR) && GetThreadLeafFunction(op[1].mem.disp)) {
                    emit(std::make_unique<CallLeafRuntimeInstr>(ar(2), op[1].mem.disp), 2);
                    continue;
                }
            }
        }
        // BranchIfSmi tests only the tag bit. Other TESTs remain assembly.
        if (n(0, X86_INS_TEST) && x.op_count == 2 && op[0].type == X86_OP_REG &&
            op[1].type == X86_OP_IMM && op[1].imm == dart::kSmiTagMask && n(1, X86_INS_JE)) {
            emit(std::make_unique<BranchIfSmiInstr>(ar(2), Reg{op[0].reg}, operands(1)[0].imm), 2);
            continue;
        }
        // LoadStaticField/StoreStaticField use the native-word field table,
        // including on compressed-pointer targets. No heap-object tag here.
        if (n(0, X86_INS_MOV) && x.op_count == 2 && op[0].type == X86_OP_REG && op[0].size == 8 &&
            memory(op[1], CSREG_DART_THR) && op[1].mem.disp == AOT_Thread_field_table_values_offset &&
            n(1, X86_INS_MOV)) {
            const auto* next = operands(1);
            const auto base = op[0].reg;
            if (next[0].type == X86_OP_REG && next[0].size == 8 && memory(next[1], base) &&
                next[1].mem.disp >= 0 && next[1].mem.disp % dart::kWordSize == 0) {
                const auto offset = next[1].mem.disp;
                emit(std::make_unique<LoadStaticFieldInstr>(ar(2), Reg{next[0].reg}, offset), 2);
                continue;
            }
            if (memory(next[0], base) && next[1].type == X86_OP_REG && next[1].size == 8 &&
                next[0].mem.disp >= 0 && next[0].mem.disp % dart::kWordSize == 0) {
                emit(std::make_unique<StoreStaticFieldInstr>(ar(2), Reg{next[1].reg}, next[0].mem.disp), 2);
                continue;
            }
        }
#if !defined(DART_COMPRESSED_POINTERS)
        // LoadInt32/64FromBoxOrSmi optimistically shifts, branches on carry,
        // and reconstructs the tagged Mint address via [dst+dst+value_offset].
        // Validate the branch end and complete addressing mode before folding.
        size_t shift = 0;
        Reg source;
        if (n(0, X86_INS_MOV) && x.op_count == 2 && op[0].type == X86_OP_REG &&
            op[1].type == X86_OP_REG && op[0].size == 8 && op[1].size == 8 && n(1, X86_INS_SAR)) {
            shift = 1;
            source = Reg{op[1].reg};
        }
        if (n(shift, X86_INS_SAR) && n(shift + 1, X86_INS_JAE) &&
            (n(shift + 2, X86_INS_MOV) || n(shift + 2, X86_INS_MOVSXD))) {
            const auto* sar = operands(shift);
            const auto* load = operands(shift + 2);
            if (sar[0].type == X86_OP_REG && sar[0].size == 8 && sar[1].type == X86_OP_IMM &&
                sar[1].imm == dart::kSmiTagSize && (!shift || sar[0].reg == op[0].reg) &&
                reg(load[0], sar[0].reg) && load[0].size == 8 && load[1].type == X86_OP_MEM &&
                load[1].mem.base == sar[0].reg && load[1].mem.index == sar[0].reg &&
                load[1].mem.scale == 1 && load[1].mem.segment == X86_REG_INVALID &&
                load[1].mem.disp == dart::Mint::value_offset() &&
                operands(shift + 1)[0].type == X86_OP_IMM &&
                static_cast<uint64_t>(operands(shift + 1)[0].imm) == ar(shift + 3).end) {
                const auto bits = n(shift + 2, X86_INS_MOVSXD) ? 32 : 64;
                if (!source.IsSet()) source = Reg{sar[0].reg};
                emit(std::make_unique<UnboxIntInstr>(ar(shift + 3), Reg{sar[0].reg}, source, bits), shift + 3);
                continue;
            }
        }
#endif
        if (n(0, X86_INS_MOV) && x.op_count == 2) {
            const bool load = op[0].type == X86_OP_REG && op[1].type == X86_OP_MEM;
            const bool store = op[0].type == X86_OP_MEM && op[1].type == X86_OP_REG;
            if (load || store) {
                const auto& mem = op[load ? 1 : 0];
                const auto& value = op[load ? 0 : 1];
                const Reg base{mem.mem.base};
                const Reg valueReg{value.reg};
                auto* cls = base.IsSet() ? objects[base] : nullptr;
                if (cls && valueReg.IsSet() && mem.mem.segment == X86_REG_INVALID) {
                    const auto offset = mem.mem.disp + dart::kHeapObjectTag;
                    const Reg index{mem.mem.index};
                    if ((cls->Id() == dart::kArrayCid || cls->Id() == dart::kImmutableArrayCid) &&
                        value.size == dart::kCompressedWordSize && offset == dart::Array::data_offset() &&
                        index.IsSet() && mem.mem.scale == dart::kCompressedWordSize / 2) {
                        ArrayOp array{value.size, load, ArrayOp::List};
                        if (load) emit(std::make_unique<LoadArrayElementInstr>(ar(1), valueReg, base, VarStorage{index}, array));
                        else emit(std::make_unique<StoreArrayElementInstr>(ar(1), valueReg, base, VarStorage{index}, array));
                        continue;
                    }
                    if (memory(mem, mem.mem.base) && offset >= dart::kWordSize && offset < cls->Size() &&
                        cls->FindField(offset) && (value.size == 8 || value.size == dart::kCompressedWordSize)) {
                        if (load) emit(std::make_unique<LoadFieldInstr>(ar(1), valueReg, base, offset));
                        else emit(std::make_unique<StoreFieldInstr>(ar(1), valueReg, base, offset));
                        continue;
                    }
                }
            }
        }
        if (move(insn->id) && x.op_count == 2 && op[0].type == X86_OP_REG) {
            const Reg dst{op[0].reg};
            if (dst.IsSet() && op[0].size == dart::kWordSize) {
                if (op[1].type == X86_OP_IMM) {
                    emit(std::make_unique<LoadValueInstr>(ar(1), dst,
                        VarItem{VarStorage::Immediate, new VarInteger(op[1].imm, VarValue::NativeInt)}));
                    continue;
                }
                if (memory(op[1], CSREG_DART_THR)) {
                    VarValue* value = nullptr;
                    if (op[1].mem.disp == dart::Thread::object_null_offset()) value = new VarNull();
                    if (op[1].mem.disp == dart::Thread::bool_true_offset()) value = new VarBoolean(true);
                    if (op[1].mem.disp == dart::Thread::bool_false_offset()) value = new VarBoolean(false);
                    if (value) {
                        emit(std::make_unique<LoadValueInstr>(ar(1), dst, VarItem{VarStorage::NewThread(op[1].mem.disp), value}));
                        continue;
                    }
                }
                intptr_t offset;
                if (poolOffset(app, op[1], offset) && op[1].size == dart::kWordSize) {
                    auto& text = data.asmTexts.AtAddr(insn->address);
                    text.dataType = AsmText::PoolOffset;
                    text.poolOffset = offset;
                    const auto type = app.GetObjectPool().TypeAt(PoolIndexFromOffset(offset));
                    if (type == dart::ObjectPool::EntryType::kTaggedObject || type == dart::ObjectPool::EntryType::kImmediate) {
                        emit(std::make_unique<LoadValueInstr>(ar(1), dst,
                            VarItem{VarStorage::NewPool(offset), getPoolObject(app, offset, dst)}));
                        continue;
                    }
                }
                if (op[1].type == X86_OP_REG && Reg{op[1].reg}.IsSet()) {
                    emit(std::make_unique<MoveRegInstr>(ar(1), dst, Reg{op[1].reg}));
                    continue;
                }
            }
        }
#if defined(DART_COMPRESSED_POINTERS)
        if (n(0, X86_INS_ADD) && x.op_count == 2 && op[0].type == X86_OP_REG && op[0].size == 8 &&
            memory(op[1], CSREG_DART_THR) && op[1].mem.disp == AOT_Thread_heap_base_offset) {
            emit(std::make_unique<DecompressPointerInstr>(ar(1), VarStorage{Reg{op[0].reg}}));
            continue;
        }
#endif
        // Class id load is identified by the complete SDK tags-load/shift pair.
        if (n(0, X86_INS_MOV) && x.op_count == 2 && op[0].type == X86_OP_REG && op[0].size == 4 &&
            op[1].type == X86_OP_MEM && op[1].mem.index == X86_REG_INVALID &&
            Reg{op[1].mem.base}.IsSet() && op[1].mem.disp == -dart::kHeapObjectTag &&
            n(1, X86_INS_SHR) && operands(1)[0].type == X86_OP_REG &&
            operands(1)[0].reg == op[0].reg && operands(1)[1].type == X86_OP_IMM &&
            operands(1)[1].imm == kUntaggedObjectClassIdTagPos) {
            emit(std::make_unique<LoadClassIdInstr>(ar(2), Reg{op[1].mem.base}, Reg{op[0].reg}), 2);
            continue;
        }
        emit(std::make_unique<UnknownInstr>(insn, data.asmTexts.AtAddr(insn->address)));
    }
}
#endif
