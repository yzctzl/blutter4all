#include "pch.h"
#include "ObjectPool.h"
#include "DartDumper.h"
#include <fstream>
#include <format>
#include <set>
#include <ranges>
#include <iostream>
#include <sstream>
#include <numeric>
#include "Disassembler.h"
#include "DartThreadInfo.h"
#include "CodeAnalyzer.h"
#include "vm/stack_frame.h"
#include "vm/heap/safepoint.h"

// TODO: move arm64 specific code to *_arm64 file

static std::unordered_map<std::string, std::string> OP_MAP {
	{ "==", "eq" },
	{ "<", "lt" }, { ">", "gt" },
	{ "<=", "lte" }, { ">=", "gte" },
	{ "=", "assign" },
	{ "[]", "at" }, { "[]=", "at_assign" },
	{ "++", "increment" }, { "--", "decrement" },
	{ "+", "add" }, { "-", "sub" }, { "*", "mul" }, { "~/", "div" }, { "/", "divf" },
	{ "%", "mod" },
	{ "&", "LAnd" }, { "|", "LOr" }, { "^", "xor" }, { "~", "not" }, {">>", "shar"}, {"<<", "shal"}, {">>", "shr"}
};

static std::string getFunctionName4Ida(const DartFunction& dartFn, const std::string& cls_prefix)
{
	auto fnName = dartFn.Name();
	if (dartFn.IsClosure() && fnName == "<anonymous closure>") {
		return "_anon_closure";
	}

	auto periodPos = fnName.find('.');
	std::string prefix;
	if (dartFn.IsStatic() && dartFn.Kind() == DartFunction::NORMAL && periodPos != std::string::npos) {
		// this one is extension
		prefix = fnName.substr(0, periodPos + 1);
		if (prefix.starts_with("_extension#")) {
			// anonymous extension. '#' is invalid name in IDA.
			std::replace(prefix.begin(), prefix.end(), '#', '@');
		}
		fnName = fnName.substr(periodPos + 1);
	}

	if (OP_MAP.contains(fnName)) {
		return prefix + "op_" + OP_MAP[fnName];
	}
	if (fnName.empty())
		return std::format("function_{:x}", dartFn.Address());
	const auto last = fnName.back();
	if (last == '=') {
		fnName.pop_back();
		return prefix + fnName + "_assign";
	}
	else if (last == '-') {
		fnName.pop_back();
		return prefix + fnName + "_neg";
	}
	else if (last == '!') {
		fnName.pop_back();
		return prefix + fnName + "_not";
	}

	switch (dartFn.Kind()) {
	case DartFunction::CONSTRUCTOR: {
		std::string name = dartFn.IsStatic() ? "factory_ctor" : "ctor";
		ASSERT(fnName.starts_with(cls_prefix));
		if (fnName.size() > cls_prefix.length() && fnName[cls_prefix.length()] == '.') {
			name += '_';
			name += &fnName[cls_prefix.length() + 1];
		}
		return name;
	}
	case DartFunction::SETTER:
		return "set_" + fnName;
	case DartFunction::GETTER:
		return "get_" + fnName;
	default:
		break;
	}

	return prefix + fnName;
}


// Export facts once. Tool APIs and source-language escaping live in Python/templates.
void DartDumper::DumpScriptData(const std::filesystem::path& filename)
{
	auto temporary = filename;
	temporary += ".tmp";
	std::filesystem::remove(filename);
	try {
		std::ofstream of(temporary);
		of.exceptions(std::ios::badbit | std::ios::failbit);
		of << "{\"schema\":1,\"dart\":" << Util::JsonQuote(Dart_VersionString()) << ",\"target\":{";
#if defined(TARGET_ARCH_ARM64)
		of << "\"arch\":\"arm64\",";
#elif defined(TARGET_ARCH_X64)
		of << "\"arch\":\"x64\",";
#else
		of << "\"arch\":\"arm\",";
#endif
		Disassembler disassembler;
#if defined(TARGET_ARCH_ARM)
		// Frida exposes r10, not Capstone's optional ARM alias "sl".
		of << "\"thread\":" << Util::JsonQuote(std::format("r{}", static_cast<int>(dart::THR)))
			<< ",\"pool\":" << Util::JsonQuote(std::format("r{}", static_cast<int>(dart::PP)));
#else
		of << "\"thread\":" << Util::JsonQuote(disassembler.GetRegName(CSREG_DART_THR))
			<< ",\"pool\":" << Util::JsonQuote(disassembler.GetRegName(CSREG_DART_PP));
#endif
		of << ",\"stack\":" << Util::JsonQuote(disassembler.GetRegName(CSREG_DART_SP))
			<< ",\"entrySlots\":" << dart::kLastParamSlotFromEntrySp << ',';
#if defined(DART_TARGET_OS_ANDROID)
		of << "\"os\":\"android\",";
#elif defined(DART_TARGET_OS_MACOS_IOS)
		of << "\"os\":\"ios\",";
#elif defined(DART_TARGET_OS_MACOS)
		of << "\"os\":\"macos\",";
#elif defined(DART_TARGET_OS_WINDOWS)
		of << "\"os\":\"windows\",";
#else
		of << "\"os\":\"linux\",";
#endif
		of << "\"wordSize\":" << dart::kWordSize
			<< ",\"slotSize\":" << dart::kCompressedWordSize;
#if defined(DART_COMPRESSED_POINTERS)
		of << ",\"compressed\":true,\"heapBaseOffset\":" << AOT_Thread_heap_base_offset;
#else
		of << ",\"compressed\":false";
#endif
		of << "},\"registers\":{";
		auto registerName = [](dart::Register reg) {
#if defined(TARGET_ARCH_X64)
			return std::string(CpuRegister{reg}.Name());
#elif defined(TARGET_ARCH_ARM64)
			return std::format("x{}", static_cast<int>(reg));
#else
			return std::format("r{}", static_cast<int>(reg));
#endif
		};
		of << "\"dartSp\":" << Util::JsonQuote(registerName(dart::SPREG))
			<< ",\"fp\":" << Util::JsonQuote(registerName(dart::FPREG))
			<< ",\"thread\":" << Util::JsonQuote(registerName(dart::THR))
			<< ",\"pool\":" << Util::JsonQuote(registerName(dart::PP))
			<< ",\"argumentsDescriptor\":" << Util::JsonQuote(registerName(dart::ARGS_DESC_REG));
#if defined(TARGET_ARCH_ARM64)
		of << ",\"nativeSp\":\"sp\",\"lr\":\"x30\"";
#elif defined(TARGET_ARCH_ARM)
		of << ",\"nativeSp\":\"r13\",\"lr\":\"r14\"";
#else
		of << ",\"nativeSp\":\"rsp\",\"lr\":null";
#endif
		of << "},\"codeUnits\":[";
		dumpCodeUnits(of);
#ifdef NO_CODE_ANALYSIS
		of << "],\"analysisState\":\"not_run\",";
#else
		of << "],\"analysisState\":\"available\",";
#endif
		const auto snapshotRva = [&](const uint8_t* address) {
			return address ? Util::JsonQuote(std::format("{:#x}", address - static_cast<const uint8_t*>(app.lib_base))) : "null";
		};
		of << "\"image\":{\"vmData\":"
			<< snapshotRva(app.vm_snapshot_data)
			<< ",\"vmInstructions\":"
			<< snapshotRva(app.vm_snapshot_instructions)
			<< ",\"isolateData\":"
			<< Util::JsonQuote(std::format("{:#x}", static_cast<uint64_t>(app.isolate_snapshot_data - static_cast<const uint8_t*>(app.lib_base))))
			<< ",\"isolateInstructions\":"
			<< Util::JsonQuote(std::format("{:#x}", static_cast<uint64_t>(app.isolate_snapshot_instructions - static_cast<const uint8_t*>(app.lib_base))))
			<< ",\"checks\":[";
		// Code bytes identify the input independently of ASLR; never export host pointers.
		int checks = 0;
		for (const auto& [address, fn] : app.functions) {
			if (fn->PayloadSize() < 16)
				continue;
			if (checks++) of << ',';
			const auto offset = fn->PayloadAddress();
			std::string bytes;
			for (int i = 0; i < 16; ++i)
				bytes += std::format("{:02x}", *(reinterpret_cast<const uint8_t*>(app.base() + offset) + i));
			of << '[' << Util::JsonQuote(std::format("{:#x}", offset)) << ',' << Util::JsonQuote(bytes) << ']';
			if (checks == 3) break;
		}
		of << "]},";
		dumpScriptLayouts(of);
		of << ",\"functions\":[\n";
		bool first = true;
		auto function = [&](uint64_t address, intptr_t size, const std::string& name) {
			if (!first) of << ",\n";
			first = false;
			of << '[' << Util::JsonQuote(std::format("{:#x}", address)) << ',' << std::max<intptr_t>(0, size)
				<< ',' << Util::JsonQuote(name) << ']';
		};
		for (auto lib : app.libs) {
			for (auto cls : lib->classes) {
				const auto owner = cls->Ptr() == dart::Class::null() ? lib->GetName()
					: std::format("{}_{}", lib->GetName(), cls->Name());
				for (auto fn : cls->Functions()) {
					const auto address = fn->Address();
					const auto name = std::format("{}::{}_{:x}", owner, getFunctionName4Ida(*fn, cls->Name()), address);
					function(address, fn->Size(), name);
					if (fn->HasMorphicCode()) {
						const auto payload = fn->PayloadAddress();
						const auto mono = fn->MonomorphicAddress();
						if (payload && payload != address) function(payload, 0, name + "_miss");
						if (mono && mono != address && mono != payload) function(mono, 0, name + "_check");
					}
				}
			}
		}
		for (const auto& [address, stub] : app.stubs)
			function(address, stub->Size(), std::format("{}_{:x}", stub->FullName(), address));
		of << "],\"structures\":{";
		dumpScriptStructures(of);
		of << "},\"operands\":[\n";
		dumpScriptOperands(of);
		of << "],\"analysis\":[";
		dumpScriptAnalysis(of);
		of << "]}\n";
		of.close();
		std::filesystem::rename(temporary, filename);
	}
	catch (...) {
		std::error_code ec;
		std::filesystem::remove(temporary, ec);
		throw;
	}
}

// Read original Code metadata, independently of analyzer-created stub splits and
// display names. Several Code objects may share one payload; the publisher merges
// those records without losing their entry points.
void DartDumper::dumpCodeUnits(std::ostream& of)
{
	class CodeVisitor final : public dart::ObjectVisitor {
	public:
		std::vector<dart::CodePtr> codes;
		void VisitObject(dart::ObjectPtr object) override {
			if (object->IsCode())
				codes.push_back(dart::Code::RawCast(object));
		}
	} visitor;
	{
		dart::HeapIterationScope scope(dart::Thread::Current());
		scope.IterateOldObjects(&visitor);
	}
	auto& code = dart::Code::Handle();
	bool first = true;
	for (const auto ptr : visitor.codes) {
		code = ptr;
		const auto payload = code.PayloadStart();
		const auto size = static_cast<intptr_t>(code.Size());
		// VM-generated host stubs and discarded bodies are not input-file code.
		if (size <= 0 || payload < static_cast<uintptr_t>(app.base()) ||
			payload - app.base() >= (uint64_t{1} << 30))
			continue;
		const auto start = payload - app.base();
		if (!first) of << ',';
		first = false;
		of << "{\"start\":" << Util::JsonQuote(std::format("{:#x}", start))
			<< ",\"end\":" << Util::JsonQuote(std::format("{:#x}", start + size))
			<< ",\"source\":\"snapshot\",\"kind\":" << Util::JsonQuote(code.IsStubCode() ? "stub" : "dart")
			<< ",\"primaryEntry\":" << Util::JsonQuote(std::format("{:#x}", code.EntryPoint() - app.base()))
			<< ",\"entries\":[";
		bool firstEntry = true;
		auto entry = [&](uintptr_t address, const char* kind) {
			if (!firstEntry) of << ',';
			firstEntry = false;
			of << "{\"rva\":" << Util::JsonQuote(std::format("{:#x}", address - app.base()))
				<< ",\"kind\":" << Util::JsonQuote(kind) << '}';
		};
		entry(code.EntryPoint(), "normal");
		entry(code.MonomorphicEntryPoint(), "monomorphic");
		entry(code.UncheckedEntryPoint(), "unchecked");
		entry(code.MonomorphicUncheckedEntryPoint(), "monomorphic_unchecked");
		of << "]}";
	}
}

void DartDumper::dumpScriptAnalysis(std::ostream& of)
{
	auto registerName = [](CpuRegister reg) {
		if (!reg.IsSet()) return std::string("null");
#if defined(TARGET_ARCH_ARM64)
		if (!reg.IsDecimal()) {
			if (static_cast<int>(reg) == 29) return Util::JsonQuote("fp");
			if (static_cast<int>(reg) == 30) return Util::JsonQuote("lr");
			return Util::JsonQuote(std::format("x{}", static_cast<int>(reg)));
		}
#elif defined(TARGET_ARCH_ARM)
		if (!reg.IsDecimal()) {
			if (reg == CpuRegister{dart::SPREG}) return Util::JsonQuote("sp");
			if (static_cast<int>(reg) == 14) return Util::JsonQuote("lr");
			return Util::JsonQuote(std::format("r{}", static_cast<int>(reg)));
		}
#endif
		return Util::JsonQuote(reg.Name());
	};
	bool first = true;
	auto parameter = [&](const FnParamInfo& param) {
		of << "{\"description\":" << Util::JsonQuote(param.ToString())
			<< ",\"name\":" << Util::JsonQuote(param.name)
			<< ",\"type\":" << (param.type ? Util::JsonQuote(param.type->ToString()) : "null")
			<< ",\"entryRegister\":" << registerName(param.paramReg)
			<< ",\"fpOffset\":" << param.paramOffset
			<< ",\"valueRegister\":" << registerName(param.valReg)
			<< ",\"localOffset\":" << param.localOffset
			<< ",\"default\":" << (param.val ? Util::JsonQuote(param.val->ToString()) : "null") << '}';
	};
	for (auto lib : app.libs) {
		for (auto cls : lib->classes) {
			for (auto fn : cls->Functions()) {
				if (!first) of << ',';
				first = false;
				const bool recovered = fn->Ptr() == dart::Function::null();
				std::ostringstream declaration;
				fn->PrintHead(declaration);
				of << '[' << Util::JsonQuote(std::format("{:#x}", fn->Address()))
					<< ",{\"name\":" << Util::JsonQuote(fn->FullName())
					<< ",\"kind\":" << (recovered ? "null" : std::to_string(static_cast<int>(fn->Kind())))
					<< ",\"payload\":" << Util::JsonQuote(std::format("{:#x}", fn->PayloadAddress()))
					<< ",\"monomorphic\":" << Util::JsonQuote(std::format("{:#x}", fn->MonomorphicAddress()))
					<< ",\"library\":" << Util::JsonQuote(lib->url)
					<< ",\"cid\":" << (cls->Ptr() == dart::Class::null() ? "null" : std::to_string(cls->Id()))
					<< ",\"declaration\":" << Util::JsonQuote(declaration.str())
					<< ",\"declarationSource\":" << Util::JsonQuote(recovered ? "recovered" : "snapshot");
				if (recovered) {
					of << ",\"signature\":null,\"flags\":null";
				}
				else {
					of << ",\"signature\":{\"returnType\":"
						<< (fn->Signature().ReturnType() ? Util::JsonQuote(fn->Signature().ReturnType()->ToString()) : "null")
						<< ",\"optional\":" << fn->NumOptionalParam()
						<< ",\"named\":" << (fn->HasNamedParam() ? "true" : "false") << ",\"parameters\":[";
					bool firstParam = true;
					for (const auto& param : fn->Params()) {
						if (!firstParam) of << ',';
						firstParam = false;
						of << "{\"name\":" << Util::JsonQuote(param.name)
							<< ",\"type\":" << (param.type ? Util::JsonQuote(param.type->ToString()) : "null")
							<< ",\"required\":" << (param.isRequired ? "true" : "false") << '}';
					}
					of << "]},\"flags\":{";
					of << "\"static\":" << (fn->IsStatic() ? "true" : "false")
						<< ",\"closure\":" << (fn->IsClosure() ? "true" : "false")
						<< ",\"async\":" << (fn->IsAsync() ? "true" : "false")
						<< ",\"native\":" << (fn->IsNative() ? "true" : "false")
						<< ",\"ffi\":" << (fn->IsFfi() ? "true" : "false")
						<< ",\"const\":" << (fn->IsConst() ? "true" : "false")
						<< ",\"abstract\":" << (fn->IsAbstract() ? "true" : "false") << '}';
				}
				auto data = fn->GetAnalyzedData();
				of << ",\"analyzed\":" << (data ? "true" : "false");
				if (data) {
					of << ",\"stackSize\":" << data->stackSize
						<< ",\"stackOverflowCheck\":" << Util::JsonQuote(std::format("{:#x}", data->firstCheckStackOverflowAddr))
						<< ",\"framePointer\":" << (data->useFramePointer ? "true" : "false")
						<< ",\"returnType\":" << (data->returnType ? Util::JsonQuote(data->returnType->ToString()) : "null")
						<< ",\"parametersPartial\":" << (data->params.isPartial ? "true" : "false")
						<< ",\"fixedParameters\":" << static_cast<int>(data->params.numFixedParam)
						<< ",\"namedParameters\":" << (data->params.isNamedParam ? "true" : "false")
						<< ",\"parameters\":[";
					for (size_t i = 0; i < data->params.params.size(); ++i) {
						if (i) of << ',';
						parameter(data->params.params[i]);
					}
					of << "],\"incoming\":[";
					for (size_t i = 0; i < data->incomingParameters.size(); ++i) {
						if (i) of << ',';
						parameter(data->incomingParameters[i]);
					}
					of << "],\"closureContext\":{\"register\":"
						<< registerName(data->closureContextReg)
						<< ",\"localOffset\":" << data->closureContextLocalOffset
						<< "},\"typeArguments\":{\"register\":"
						<< registerName(data->typeArgumentReg)
						<< ",\"localOffset\":" << data->typeArgumentLocalOffset << "},\"il\":[";
					for (size_t i = 0; i < data->il_insns.size(); ++i) {
						if (i) of << ',';
						auto& il = data->il_insns[i];
						of << '[' << Util::JsonQuote(std::format("{:#x}", il->Start()))
							<< ',' << Util::JsonQuote(std::format("{:#x}", il->End()))
							<< ',' << static_cast<int>(il->Kind()) << ',' << Util::JsonQuote(il->ToString()) << ']';
					}
					of << "],\"annotations\":[";
					bool firstAnnotation = true;
					for (const auto& text : data->asmTexts.Data()) {
						std::string comment;
						switch (text.dataType) {
						case AsmText::ThreadOffset: comment = "THR::" + GetThreadOffsetName(text.threadOffset); break;
						case AsmText::PoolOffset: comment = getPoolObjectDescription(text.poolOffset); break;
						case AsmText::Boolean: comment = text.boolVal ? "true" : "false"; break;
						case AsmText::Call:
							if (auto target = app.GetFunction(text.callAddress)) comment = target->FullName();
							break;
						}
						if (comment.empty()) continue;
						if (!firstAnnotation) of << ',';
						firstAnnotation = false;
						of << '[' << Util::JsonQuote(std::format("{:#x}", text.addr)) << ',' << Util::JsonQuote(comment) << ']';
					}
					of << ']';
				}
				of << "}]";
			}
		}
	}
}

void DartDumper::dumpScriptStructures(std::ostream& of)
{
	of << "\"DartThread\":[";
	for (intptr_t offset = 0; offset <= GetThreadMaxOffset(); offset += dart::kWordSize) {
		if (offset) of << ',';
		const auto& name = GetThreadOffsetName(static_cast<int>(offset));
		of << '[' << offset << ',' << Util::JsonQuote(name.empty() ? std::format("pad_{:x}", offset) : name) << ",\"\"]\n";
	}
	of << "],\"DartObjectPool\":[";
	// ObjectPool entries use machine words, including in compressed snapshots.
	const auto headerSize = dart::ObjectPool::element_offset(0);
	for (intptr_t offset = 0; offset < headerSize; offset += dart::kWordSize) {
		if (offset) of << ',';
		of << '[' << offset << ',' << Util::JsonQuote(std::format("pad_{:x}", offset)) << ",\"\"]";
	}
	const auto& pool = app.GetObjectPool();
	const auto num = pool.Length();
	auto& obj = dart::Object::Handle();
	for (intptr_t i = 0; i < num; ++i) {
		const auto offset = dart::ObjectPool::element_offset(i);
		std::string name, description;
		auto objType = pool.TypeAt(i);
		if (objType == dart::ObjectPool::EntryType::kTaggedObject) {
			obj = pool.ObjectAt(i);
			if (obj.IsUnlinkedCall()) {
				const auto targetIndex = UnlinkedCallTargetIndex(i);
				name = std::format("UnlinkedCall_{:#x}_unknown", offset);
				if (targetIndex >= 0 && targetIndex < num) {
					// since Dart 3.10, target type might be kTaggedObject
					auto unlinkTargetType = pool.TypeAt(targetIndex);
					if (unlinkTargetType == dart::ObjectPool::EntryType::kImmediate) {
						const auto imm = pool.RawValueAt(targetIndex);
						auto dartFn = app.GetFunction(imm - app.base());
						if (dartFn != nullptr) {
							name = std::format("UnlinkedCall_{:#x}_{:#x}", offset, dartFn->Address());
						}
						else {
							name = std::format("UnlinkedCall_{:#x}_unknown", offset);
						}
					}
					else {
						ASSERT(unlinkTargetType == dart::ObjectPool::EntryType::kTaggedObject);
						name = std::format("UnlinkedCall_{:#x}_tagged", offset);
						obj = pool.ObjectAt(targetIndex);
						description = ObjectToString(obj);
					}
				}
			}
			else {
				// TODO: more meaningful variable name
				name = std::format("Obj_{:#x}", offset);
				auto comment = ObjectToString(obj);
				description = comment;
			}
		}
		else if (objType == dart::ObjectPool::EntryType::kImmediate) {
			name = std::format("IMM_{:#x}_{:#x}", pool.RawValueAt(i), offset);
		}
		else if (objType == dart::ObjectPool::EntryType::kNativeFunction) {
			// the name of NativeFunction can be retrieved from dart::NativeSymbolResolver::LookupSymbolName
			//   but normally flutter code never access it
			// if we use the name, we should cache it because many Pool Objects reference same NativeFunction
			name = std::format("NativeFn_{:#x}_{:#x}", pool.RawValueAt(i), offset);
		}
		else {
			name = std::format("RAW_{:#x}_{:#x}", pool.RawValueAt(i), offset);
		}

		of << ",[" << offset << "," << Util::JsonQuote(name) << ","
			<< Util::JsonQuote(description) << "]\n";
	}

	of << "]";
}

void DartDumper::dumpScriptOperands(std::ostream& of)
{
	Disassembler disassembler;
	bool first = true;
	for (auto lib : app.libs) {
		if (lib->isInternal) continue;
		for (auto cls : lib->classes) {
			for (auto fn : cls->Functions()) {
				if (!fn->PayloadSize()) continue;
				auto insns = disassembler.Disasm(reinterpret_cast<const uint8_t*>(app.base() + fn->PayloadAddress()), fn->PayloadSize(), fn->PayloadAddress());
				for (size_t i = 0; i < insns.Count(); ++i) {
					auto insn = insns.At(i);
					for (uint8_t j = 0; j < insn.op_count(); ++j) {
						const auto base = insn.MemoryBase(j);
						if (base != CSREG_DART_THR && base != CSREG_DART_PP) continue;
						// Only constant base+displacement accesses can name a structure member.
#if defined(TARGET_ARCH_X64)
						const auto& x = insn.ptr()->detail->x86;
						if (insn.ops[j].mem.index != X86_REG_INVALID || insn.ops[j].mem.segment != X86_REG_INVALID || x.addr_size != dart::kWordSize) continue;
#elif defined(TARGET_ARCH_ARM)
						if (insn.ptr()->detail->arm.writeback || insn.ops[j].mem.index != ARM_REG_INVALID) continue;
#else
						if (insn.ptr()->detail->arm64.writeback || insn.ops[j].mem.index != ARM64_REG_INVALID) continue;
#endif
						if (!first) of << ",\n";
						first = false;
						const bool pool = base == CSREG_DART_PP;
						of << '[' << Util::JsonQuote(std::format("{:#x}", insn.address())) << ',' << static_cast<int>(j)
							<< ',' << Util::JsonQuote(pool ? "DartObjectPool" : "DartThread") << ',' << (pool ? kPoolPointerTag : 0) << ']';
						break;
					}
				}
			}
		}
	}
}

void DartDumper::dumpScriptLayouts(std::ostream& of)
{
	of << "\"constants\":{";
	of << "\"ClassIdTagPos\":" << kUntaggedObjectClassIdTagPos << ",\n";
	of << "\"ClassIdTagMask\":" << ((1u << dart::UntaggedObject::kClassIdTagSize) - 1) << ",\n";

	of << "\"NumPredefinedCids\":" << dart::kNumPredefinedCids << ",\n";
	of << "\"CidObject\":" << dart::kInstanceCid << ",\n";
	of << "\"CidNull\":" << dart::kNullCid << ",\n";
	of << "\"CidSmi\":" << dart::kSmiCid << ",\n";
	of << "\"CidMint\":" << dart::kMintCid << ",\n";
	of << "\"CidDouble\":" << dart::kDoubleCid << ",\n";
	of << "\"CidBool\":" << dart::kBoolCid << ",\n";
	of << "\"CidString\":" << dart::kOneByteStringCid << ",\n";
	of << "\"CidTwoByteString\":" << dart::kTwoByteStringCid << ",\n";
	of << "\"CidArray\":" << dart::kArrayCid << ",\n";
	of << "\"CidImmutableArray\":" << dart::kImmutableArrayCid << ",\n";
	of << "\"CidConstMap\":" << dart::kConstMapCid << ",\n";
	of << "\"CidConstSet\":" << dart::kConstSetCid << ",\n";
	of << "\"CidGrowableArray\":" << dart::kGrowableObjectArrayCid << ",\n";
	of << "\"CidSet\":" << dart::kSetCid << ",\n";
	of << "\"CidMap\":" << dart::kMapCid << ",\n";
	of << "\"CidClosure\":" << dart::kClosureCid << ",\n";
	of << "\"CidUint8Array\":" << dart::kTypedDataUint8ArrayCid << ",\n";
	of << "\"CidInt8Array\":" << dart::kTypedDataInt8ArrayCid << ",\n";
	of << "\"CidUint16Array\":" << dart::kTypedDataUint16ArrayCid << ",\n";
	of << "\"CidInt16Array\":" << dart::kTypedDataInt16ArrayCid << ",\n";
	of << "\"CidUint32Array\":" << dart::kTypedDataUint32ArrayCid << ",\n";
	of << "\"CidInt32Array\":" << dart::kTypedDataInt32ArrayCid << ",\n";
	of << "\"CidUint64Array\":" << dart::kTypedDataUint64ArrayCid << ",\n";
	of << "\"CidInt64Array\":" << dart::kTypedDataInt64ArrayCid << ",\n";
	of << "\"CidFloat32Array\":" << dart::kTypedDataFloat32ArrayCid << ",\n";
	of << "\"CidFloat64Array\":" << dart::kTypedDataFloat64ArrayCid << ",\n";
	of << "\"CidContext\":" << dart::kContextCid << "},\n";

	of << "\"classes\":[\n";
	bool first = true;
	for (auto dartCls : app.classes) {
		if (!first) of << ",\n";
		first = false;
		if (!dartCls) {
			of << "null";
			continue;
		}

		if (dartCls->Id() < dart::kNumPredefinedCids) {
			switch (dartCls->Id()) {
			case dart::kBoolCid:
				of << "{\"id\":" << dartCls->Id() << ",";
				of << "\"name\":\"bool\",";
				// value_ offset in raw_object.h is inaccessible
				of << "\"valOffset\":" << AOT_Instance_InstanceSize << "}";
				break;
			case dart::kMintCid:
				of << "{\"id\":" << dartCls->Id() << ",";
				of << "\"name\":\"int\",";
				of << "\"valOffset\":" << AOT_Mint_value_offset << "}";
				break;
			case dart::kDoubleCid:
				of << "{\"id\":" << dartCls->Id() << ",";
				of << "\"name\":\"double\",";
				of << "\"valOffset\":" << AOT_Double_value_offset << "}";
				break;
			case dart::kOneByteStringCid:
				of << "{\"id\":" << dartCls->Id() << ",";
				of << "\"name\":\"String\",";
				of << "\"lenOffset\":" << AOT_String_length_offset << ",";
				of << "\"dataOffset\":" << AOT_OneByteString_data_offset << "}";
				break;
			case dart::kTwoByteStringCid:
				of << "{\"id\":" << dartCls->Id() << ",";
				of << "\"name\":\"TwoByteString\",";
				of << "\"lenOffset\":" << AOT_String_length_offset << ",";
				of << "\"dataOffset\":" << AOT_TwoByteString_data_offset << "}";
				break;
			case dart::kArrayCid:
			case dart::kImmutableArrayCid:
				of << "{\"id\":" << dartCls->Id() << ",";
				of << "\"name\":\"List\",";
				//dart::Array::kBytesPerElement is same as a compressed pointer size
				of << "\"lenOffset\":" << AOT_Array_length_offset << ",";
				of << "\"dataOffset\":" << AOT_Array_data_offset << ",";
				of << "\"typeOffset\":" << AOT_Array_type_arguments_offset << "}";
				break;
			case dart::kGrowableObjectArrayCid:
				of << "{\"id\":" << dartCls->Id() << ",";
				of << "\"name\":\"GrowableList\",";
				of << "\"lenOffset\":" << AOT_GrowableObjectArray_length_offset << ",";
				of << "\"dataOffset\":" << AOT_GrowableObjectArray_data_offset << ",";
				of << "\"typeOffset\":" << AOT_GrowableObjectArray_type_arguments_offset << "}";
				break;
			case dart::kSetCid:
#ifndef OLD_MAP_NO_IMMUTABLE
			case dart::kConstSetCid:
#endif
				of << "{\"id\":" << dartCls->Id() << ",";
				of << "\"name\":\"Set\",";
				of << "\"usedOffset\":" << AOT_LinkedHashBase_used_data_offset << ",";
				of << "\"delOffset\":" << AOT_LinkedHashBase_deleted_keys_offset << ",";
				of << "\"dataOffset\":" << AOT_LinkedHashBase_data_offset << ",";
				of << "\"typeOffset\":" << AOT_LinkedHashBase_type_arguments_offset << "}";
				break;
			case dart::kMapCid:
#ifndef OLD_MAP_NO_IMMUTABLE
			case dart::kConstMapCid:
#endif
				of << "{\"id\":" << dartCls->Id() << ",";
				of << "\"name\":\"Map\",";
				of << "\"usedOffset\":" << AOT_LinkedHashBase_used_data_offset << ",";
				of << "\"delOffset\":" << AOT_LinkedHashBase_deleted_keys_offset << ",";
				of << "\"dataOffset\":" << AOT_LinkedHashBase_data_offset << ",";
				of << "\"typeOffset\":" << AOT_LinkedHashBase_type_arguments_offset << "}";
				break;
			case dart::kClosureCid:
				of << "{\"id\":" << dartCls->Id() << ",";
				of << "\"name\":\"Closure\",";
				of << "\"fnOffset\":" << AOT_Closure_function_offset << ",";
#ifdef DART_SINGLE_SNAPSHOT
				// Context is the last element; its index varies with type arguments.
				of << "\"elementsOffset\":" << AOT_Closure_elements_start_offset << ",";
				of << "\"lengthOffset\":" << AOT_Closure_length_and_flags_offset << ",";
				of << "\"lengthShift\":" << dart::UntaggedClosure::kLengthBitsPos << ",";
#else
				of << "\"contextOffset\":" << AOT_Closure_context_offset << ",";
#endif
				of << "\"epOffset\":" << AOT_Closure_entry_point_offset << "}";
				break;
			case dart::kContextCid:
				of << "{\"id\":" << dartCls->Id() << ",\"name\":\"Context\",\"countOffset\":" << AOT_Context_num_variables_offset
					<< ",\"parentOffset\":" << AOT_Context_parent_offset << ",\"dataOffset\":" << AOT_Context_elements_start_offset << "}";
				break;
			case dart::kTypedDataFloat32ArrayCid:
			case dart::kTypedDataFloat64ArrayCid:
			case dart::kTypedDataUint8ArrayCid:
			case dart::kTypedDataUint16ArrayCid:
			case dart::kTypedDataUint32ArrayCid:
			case dart::kTypedDataUint64ArrayCid:
			case dart::kTypedDataInt8ArrayCid:
			case dart::kTypedDataInt16ArrayCid:
			case dart::kTypedDataInt32ArrayCid:
			case dart::kTypedDataInt64ArrayCid:
				of << "{\"id\":" << dartCls->Id() << ",";
				of << "\"name\":" << Util::JsonQuote(dartCls->Name()) << ",";
				of << "\"lenOffset\":" << AOT_TypedDataBase_length_offset << ",";
				// current version name is "AOT_TypedData_payload_offset" but old version name is "AOT_TypedData_data_offset"
				// function from UntaggedTypedData is always same
				of << "\"dataOffset\":" << dart::UntaggedTypedData::payload_offset() << "}";
				break;
			case dart::kInstanceCid:
				of << "{\"id\":" << dartCls->Id() << ",";
				of << "\"name\":\"Object\",";
				of << "\"size\":" << AOT_Instance_InstanceSize << "}";
				break;
			default:
				of << "{\"id\":" << dartCls->Id() << ",";
				of << "\"name\":" << Util::JsonQuote(dartCls->Name()) << "}";
				break;
			}
		}
		else {
			of << "{";
			of << "\"id\":" << dartCls->Id() << ",";
			of << "\"name\":" << Util::JsonQuote(dartCls->Name()) << ",";
			of << "\"fbitmap\":" << Util::JsonQuote(std::format("{:#x}", dartCls->FieldBitmap())) << ",";
			of << "\"sid\":" << (dartCls->Parent() ? dartCls->Parent()->Id() : dart::kInstanceCid) << ",";
			of << "\"size\":" << dartCls->Size() << ",";
			of << "\"argOffset\":" << dartCls->TypeArgumentOffset();
			dumpScriptClassFields(of, *dartCls);
			of << "}";
		}
	}
	of << "],\"topClasses\":[";
	first = true;
	for (auto cls : app.topClasses) {
		if (!cls) continue;
		if (!first) of << ',';
		first = false;
		of << "{\"id\":" << cls->Id() << ",\"name\":" << Util::JsonQuote(cls->Name());
		dumpScriptClassFields(of, *cls);
		of << '}';
	}
	of << ']';
}

void DartDumper::dumpScriptClassFields(std::ostream& of, DartClass& cls)
{
	std::ostringstream declaration;
	cls.PrintHead(declaration);
	of << ",\"declaration\":" << Util::JsonQuote(declaration.str())
		<< ",\"library\":" << Util::JsonQuote(cls.Library().url) << ",\"fields\":[";
	bool firstField = true;
	for (auto field : cls.Fields()) {
		if (!firstField) of << ',';
		firstField = false;
		of << "{\"offset\":" << field->Offset() << ",\"name\":" << Util::JsonQuote(field->Name())
			<< ",\"type\":" << Util::JsonQuote(field->TypeName())
			<< ",\"source\":" << Util::JsonQuote(field->Ptr() == nullptr ? "inferred" : "snapshot")
			<< ",\"static\":" << (field->IsStatic() ? "true" : "false")
			<< ",\"late\":" << (field->IsLate() ? "true" : "false")
			<< ",\"final\":" << (field->IsFinal() ? "true" : "false")
			<< ",\"const\":" << (field->IsConst() ? "true" : "false") << '}';
	}
	of << ']';
}

const std::string& DartDumper::getQuoteString(dart::Object& obj)
{
	const auto ptr = (intptr_t)obj.ptr();
	auto& txt = quoteStringCache[ptr];
	// because string is always quotes, empty string means inserting a new one
	if (txt.empty()) {
		txt = Util::UnescapeWithQuote(obj.ToCString());
	}
	return txt;
}

void DartDumper::DumpCode(const char* out_dir)
{
	std::filesystem::create_directory(out_dir);

	Disassembler disasmer;

	for (auto dartLib : app.libs) {
		if (dartLib->isInternal)
			continue;

		auto out_file = dartLib->CreatePath(out_dir);
		std::ofstream of(out_file);
		dartLib->PrintCommentInfo(of);

		for (auto dartCls : dartLib->classes) {
			dartCls->PrintHead(of);

			if (!dartCls->Fields().empty())
				of << "\n";
			for (auto dartField : dartCls->Fields()) {
				dartField->Print(of);
			}

			if (!dartCls->Functions().empty())
				of << "\n";
			for (auto dartFn : dartCls->Functions()) {
				dartFn->PrintHead(of);

#ifndef NO_CODE_ANALYSIS
				// use as app is loaded at zero
				if (auto data = dartFn->GetAnalyzedData(); data && dartFn->Size() > 0) {
					auto& asmTexts = data->asmTexts.Data();
					auto& il_insns = data->il_insns;
					auto il_itr = il_insns.begin();
					AddrRange range;
					ASSERT(!asmTexts.empty());
					for (auto& asmText : asmTexts) {
						std::string extra;
						switch (asmText.dataType) {
						case AsmText::ThreadOffset:
							extra = "THR::" + GetThreadOffsetName(asmText.threadOffset);
							break;
						case AsmText::PoolOffset:
							extra = getPoolObjectDescription(asmText.poolOffset);
							break;
						case AsmText::Boolean:
							extra = asmText.boolVal ? "true" : "false";
							break;
						case AsmText::Call: {
							auto* fn = app.GetFunction(asmText.callAddress);
							if (fn) {
								extra = fn->FullName();
								auto retCid = fn->ReturnType();
								if (retCid != dart::kIllegalCid) {
									if (auto retCls = app.FindClass(retCid))
										extra += std::format(" -> {} (size={:#x})", retCls->FullName(), retCls->Size());
								}
							}
							break;
						}
						}

						of << "    // ";

						if (range.Has(asmText.addr)) {
							of << "    ";
						}
						else {
							while (il_itr != il_insns.end() && (*il_itr)->Start() < asmText.addr) {
								if ((*il_itr)->Kind() != ILInstr::Unknown) {
									of << std::format("{:#x}: {}\n", (*il_itr)->Start(), (*il_itr)->ToString());
									of << "    // ";
								}
								++il_itr;
							}
							if (il_itr != il_insns.end() && (*il_itr)->Start() == asmText.addr) {
								if ((*il_itr)->Kind() != ILInstr::Unknown) {
									of << std::format("{:#x}: {}\n", asmText.addr, (*il_itr)->ToString());
									of << "    //     ";
									range = (*il_itr)->Range();
								}
								++il_itr;
							}
						}

						if (extra.empty())
							of << std::format("{:#x}: {}\n", asmText.addr, &asmText.text[0]);
						else
							of << std::format("{:#x}: {}  ; {}\n", asmText.addr, &asmText.text[0], extra);
					}
				}
#endif // NO_CODE_ANALYSIS

				dartFn->PrintFoot(of);
			}

			dartCls->PrintFoot(of);
		}
	}
}

// collect instance ptr to dump the full contents in DumpObjects()
static std::set<intptr_t> knownObjectPtrs;

std::string DartDumper::ObjectToString(dart::Object& obj, bool simpleForm, bool nestedObj, int depth)
{
	const auto cid = obj.GetClassId();
	//auto dartCls = app_.classes[obj.GetClassId()];

	if (obj.IsString()) {
		auto& val = getQuoteString(obj);
		if (simpleForm || depth > 0)
			return val;
		return "String: " + val;
	}

	// use TypedData or TypedDataBase ?
	if (obj.IsTypedData()) {
		//dart::kTypedDataInt32ArrayCid;
		auto& arr = dart::TypedData::Cast(obj);
		const auto arr_len = arr.Length();
		auto ptr = arr.DataAddr(0);
		std::string txt;
		if (arr_len > 0) {
			switch (arr.ElementType()) {
#define ACCUMLATE(type) { \
	auto data = (type*)ptr; \
	txt = std::accumulate(data + 1, data + arr_len, std::format("[{:#x}", data[0]), [](std::string x, type y) { return x + ", " + std::format("{:#x}", y); } ); \
}
			case dart::kInt8ArrayElement:
				ACCUMLATE(int8_t);
				break;
			case dart::kUint8ArrayElement:
			case dart::kUint8ClampedArrayElement:
				ACCUMLATE(uint8_t);
				break;
			case dart::kInt16ArrayElement:
				ACCUMLATE(int16_t);
				break;
			case dart::kUint16ArrayElement:
				ACCUMLATE(uint16_t);
				break;
			case dart::kInt32ArrayElement:
				ACCUMLATE(int32_t);
				break;
			case dart::kUint32ArrayElement:
				ACCUMLATE(uint32_t);
				break;
			case dart::kInt64ArrayElement:
				ACCUMLATE(int64_t);
				break;
			case dart::kUint64ArrayElement:
				ACCUMLATE(uint64_t);
				break;
#undef ACCUMLATE
#define ACCUMLATE(type) { \
	auto data = (type*)ptr; \
	txt = std::accumulate(data + 1, data + arr_len, std::format("[{}", data[0]), [](std::string x, type y) { return x + ", " + std::format("{}", y); } ); \
}
			case dart::kFloat32ArrayElement:
				ACCUMLATE(float);
				break;
			case dart::kFloat64ArrayElement:
				ACCUMLATE(double);
				break;
#undef ACCUMLATE
			case dart::kFloat32x4ArrayElement:
			case dart::kInt32x4ArrayElement:
			case dart::kFloat64x2ArrayElement:
				FATAL("TODO: simd array");
			}

			txt += ']';
		}
		//arr.ElementSizeInBytes();
		return std::format("{}({}) {}", app.GetClass(cid)->Name(), arr_len, txt);
	}

	switch (cid) {
	case dart::kSmiCid:
		if (simpleForm || depth > 0)
			return std::format("{:#x}", dart::Smi::Cast(obj).Value());
		return std::format("Smi: {:#x}", dart::Smi::Cast(obj).Value());
	case dart::kMintCid:
		if (simpleForm || depth > 0)
			return std::format("{:#x}", MintValue(dart::Mint::Cast(obj)));
		return std::format("Mint: {:#x}", MintValue(dart::Mint::Cast(obj)));
	case dart::kDoubleCid:
		if (simpleForm || depth > 0)
			return std::format("{}", dart::Double::Cast(obj).value());
		return std::format("Double: {}", dart::Double::Cast(obj).value());
	case dart::kBoolCid:
		return dart::Bool::Cast(obj).value() ? "true" : "false";
	case dart::kNullCid:
		return "Null";
	case dart::kSentinelCid:
		return "Sentinel";
	case dart::kSubtypeTestCacheCid:
		return "SubtypeTestCache";
	case dart::kFunctionCid: {
		// stub never be in Object Pool
		auto fnBase = app.GetFunction(dart::Function::Cast(obj).entry_point() - app.base());
		if (fnBase == nullptr || fnBase->IsStub()) {
			return std::format("Function: [unknown] ({:#x})", dart::Function::Cast(obj).entry_point() - app.base());
		}
		auto dartFn = fnBase->AsFunction();
		if (dartFn->IsClosure()) {
			auto parentFn = dartFn->GetOutermostFunction();
			if (parentFn) {
				// AOT anonymous closure contains only static information
				return std::format("AnonymousClosure: {}({:#x}), in {} ({:#x})",
					dartFn->IsStatic() ? "static " : "", dartFn->Address(),
					parentFn->FullName(), parentFn->Address());
			}
			else {
				return std::format("AnonymousClosure: {}({:#x}), of {}",
					dartFn->IsStatic() ? "static " : "", dartFn->Address(),
					dartFn->Class().FullNameWithPackage());
			}
		}
		return std::format("Function: {} ({:#x})", dartFn->FullName(), dartFn->Address());
	}
	case dart::kClosureCid: {
		// TODO: show owner
		const auto& closure = dart::Closure::Cast(obj);
		if (!app.functions.contains(closure.entry_point() - app.base())) {
			std::cout << std::format("[!] missing closure at {:#x}\n", closure.entry_point() - app.base());
		}
		//RELEASE_ASSERT(app.functions.contains(closure.entry_point() - app.base()));
		return std::format("{} ({:#x})", closure.ToCString(), closure.entry_point());
	}
	case dart::kCodeCid: {
		const auto& code = dart::Code::Cast(obj);
		const auto ep = code.EntryPoint() - app.base();
		if (app.stubs.contains(ep)) {
			const auto stub = app.stubs[ep];
			return std::format("Stub: {} ({:#x})", stub->Name().c_str(), ep);
		}
		return std::format("Code: {} ({:#x})", code.ToCString(), ep);
	}
	case dart::kArrayCid:
	case dart::kImmutableArrayCid: {
		// Note: since Dart 3.7, Ojbect Pool is mutable. so, Array is used too
		// Objects in Object Pool immutable, so only immutable array is used for array
		// Most of no type arguments in Object Pool are Argument Descriptor
		const auto& arr = dart::Array::Cast(obj);
		const auto arr_len = arr.Length();
		const auto typeArg = app.typeDb->FindOrAdd(arr.GetTypeArguments());
		// without type arguments, assume it is argument descriptor. show it even simple form is true.
		if (simpleForm && typeArg->Length() > 0)
			return std::format("List{}({})", typeArg->ToString(), arr_len);

		std::ostringstream ss;
		if (arr_len > 0) {
			// in ImmutableList here, only Dart type (native type is not used)
			auto arrPtr = dart::Array::DataOf(arr.ptr());
			for (intptr_t i = 0; i < arr_len; i++) {
				if (i != 0)
					ss << ", ";

				if (arrPtr->IsHeapObject()) {
					obj = arrPtr->Decompress(app.heap_base());
					ss << ObjectToString(obj, simpleForm, nestedObj, depth + 1);
				}
				else {
					obj = arrPtr->DecompressSmi();
					ss << std::hex << std::showbase << dart::Smi::Cast(obj).Value();
				}
				arrPtr++;
			}
		}
		return std::format("List{}({}) [{}]", typeArg->ToString(), arr_len, ss.str());
	}
#ifdef HAS_RECORD_TYPE
	case dart::kRecordCid: {
		const auto& record = dart::Record::Cast(obj);
		std::ostringstream ss;
		const auto type = app.typeDb->FindOrAdd(DartGetRecordType(record));
		ss << "Record" << type->ToString() << " = (";
		auto& field = dart::Object::Handle();
		const auto num_fields = record.num_fields();
		for (intptr_t i = 0; i < num_fields; i++) {
			if (i != 0) ss << ", ";
			field = record.FieldAt(i);
			ss << ObjectToString(field, simpleForm, nestedObj, depth + 1);
		}
		ss << ")";
		return ss.str();
	}
#endif
	case dart::kTypeArgumentsCid:
		return "TypeArguments: " + app.typeDb->FindOrAdd(dart::TypeArguments::RawCast(obj.ptr()))->ToString();
	case dart::kTypeCid:
		return "Type: " + app.typeDb->FindOrAdd(dart::Type::RawCast(obj.ptr()))->ToString();
#ifdef HAS_RECORD_TYPE
	case dart::kRecordTypeCid:
		return "RecordType: " + app.typeDb->FindOrAdd(dart::RecordType::RawCast(obj.ptr()))->ToString();
#endif
	case dart::kTypeParameterCid:
		return "TypeParameter: " + app.typeDb->FindOrAdd(dart::TypeParameter::RawCast(obj.ptr()))->ToString();
	case dart::kFunctionTypeCid:
		return "FunctionType: " + app.typeDb->FindOrAdd(dart::FunctionType::RawCast(obj.ptr()))->ToString();
#ifdef HAS_TYPE_REF
	case dart::kTypeRefCid:
#endif
	case dart::kTypeParametersCid:
		// might be in a Type but not in Object Pool directly
		return std::format("{} (ptr: {:#x})", obj.ToCString(), (uintptr_t)obj.ptr());
	case dart::kFieldCid: {
		const auto& field = dart::Field::Cast(obj);
		return std::format("{} (offset: {:#x})", field.ToCString(), field.TargetOffset());
	}
	case dart::kConstMapCid: {
		auto& map = dart::Map::Cast(obj);
		const auto typeArg = app.typeDb->FindOrAdd(map.GetTypeArguments());
		if (simpleForm)
			return std::format("Map{}({})", typeArg->ToString(), map.Length());

		std::ostringstream ss;
		std::string indent(depth * 2 + 2, ' ');
		ss << std::format("Map{}({}) {{\n", typeArg->ToString(), map.Length());
		dart::Map::Iterator iter(map);
		auto& key = dart::Object::Handle();
		auto& val = dart::Object::Handle();
		int cnt = 0;
		while (iter.MoveNext()) {
			if (cnt++) ss << ",\n";
			key = iter.CurrentKey();
			val = iter.CurrentValue();
			// key always be simple form
			ss << indent << ObjectToString(key, true, false, depth + 1) << ": " << ObjectToString(val, simpleForm, nestedObj, depth + 1);
		}
		if (cnt) ss << "\n";
		ss << std::string(depth * 2, ' ') << "}";
		return ss.str();
	}
	case dart::kConstSetCid: {
		auto& set = dart::Set::Cast(obj);
		const auto typeArg = app.typeDb->FindOrAdd(set.GetTypeArguments());
		if (simpleForm)
			return std::format("Set{}({})", typeArg->ToString(), set.Length());

		std::ostringstream ss;
		ss << std::format("Set{}({}) {{ ", typeArg->ToString(), set.Length());
		dart::Set::Iterator iter(set);
		auto& key = dart::Object::Handle();
		int cnt = 0;
		while (iter.MoveNext()) {
			if (cnt++)
				ss << ", ";
			key = iter.CurrentKey();
			ss << ObjectToString(key, simpleForm, nestedObj, depth + 1);
		}
		ss << " }";
		return ss.str();
	}
	case dart::kLibraryPrefixCid: {
		const auto& libPrefix = dart::LibraryPrefix::Cast(obj);
		const auto& name = dart::String::Handle(libPrefix.name());
		RELEASE_ASSERT(libPrefix.num_imports() == 1);
		// don't know what importer is
		//const auto& importer = dart::Library::Handle(libPrefix.importer());
		const auto& imports = dart::Array::Handle(libPrefix.imports());
		const auto& importObj = dart::Object::Handle(imports.At(0));
		RELEASE_ASSERT(importObj.GetClassId() == dart::kNamespaceCid);
		const auto& ns = dart::Namespace::Cast(importObj);
		const auto& lib = dart::Library::Handle(ns.target());
		const auto& libName = dart::String::Handle(lib.url());
		return std::format("LibraryPrefix: {}, target lib: {} ({})", name.ToCString(), libName.ToCString(), lib.toplevel_class().untag()->id());
	}
	case dart::kInt32x4Cid: {
		const auto& simd = dart::Int32x4::Cast(obj);
		return std::format("Int32x4: ({}, {}, {}, {})", simd.x(), simd.y(), simd.z(), simd.w());
	}
	case dart::kFloat32x4Cid: {
		const auto& simd = dart::Float32x4::Cast(obj);
		return std::format("Float32x4: ({}, {}, {}, {})", simd.x(), simd.y(), simd.z(), simd.w());
	}
	case dart::kFloat64x2Cid: {
		const auto& simd = dart::Float64x2::Cast(obj);
		return std::format("Float64x2: ({}, {})", simd.x(), simd.y());
	}
	case dart::kInstanceCid:
		return std::format("Obj!Object@{:x}", (uint32_t)(intptr_t)obj.ptr());
	// TODO: enum subclass
	}

	// many cids are instance. handling them after special classes.
	ASSERT(obj.IsInstance());

	if (cid < dart::kNumPredefinedCids) {
		FATAL("Unhandle internal class %s (%ld)", app.GetClass(cid)->Name().c_str(), cid);
	}

	// TODO: print library and package prefix
	knownObjectPtrs.insert((intptr_t)obj.ptr());
	return dumpInstance(obj, simpleForm, nestedObj, depth);
}

std::string DartDumper::dumpInstance(dart::Object& obj, bool simpleForm, bool nestedObj, int depth)
{
	auto dartCls = app.classes[obj.GetClassId()];
	ASSERT(dartCls->Id() >= dart::kNumPredefinedCids);

	std::string closeIndent(depth * 2, ' ');
	std::string indent(closeIndent.length() + 2, ' ');

	const auto ptr = dart::UntaggedObject::ToAddr(obj.ptr());
	DartType* dtype = app.typeDb->FindOrAdd(*dartCls, dart::Instance::Cast(obj));
	if (simpleForm || (!nestedObj && depth > 0)) {
		return std::format("Obj!{}@{:x}", dtype->ToString(), (uint32_t)(intptr_t)obj.ptr());
	}

	std::vector<DartClass*> parents;
	auto superCls = dartCls->Parent();
	while (superCls->Id() != dart::kInstanceCid) {
		parents.push_back(superCls);
		superCls = superCls->Parent();
	}

	std::ostringstream ss;
	int fieldCnt = 0;
	ss << std::format("Obj!{}@{:x} : {{\n", dtype->ToString(), (uint32_t)(intptr_t)obj.ptr());
	auto offset = dart::Instance::NextFieldOffset();
	for (auto parent : parents | std::views::reverse) {
		if (offset < parent->Size()) {
			// parent fields depth MUST increment by 2 because 1 is for "Super!..."
			auto txt = dumpInstanceFields(obj, *parent, ptr, offset, simpleForm, nestedObj, depth + 2);
			offset = parent->Size();
			if (!txt.empty()) {
				if (fieldCnt++)
					ss << ",\n";
				ss << indent << "Super!" << parent->FullName() << " : {\n";
				ss << txt << "\n";
				ss << indent << "}";
			}
		}
	}

	auto fieldTxt = dumpInstanceFields(obj, *dartCls, ptr, offset, simpleForm, nestedObj, depth + 1);
	if (!fieldTxt.empty()) {
		if (fieldCnt++)
			ss << ",\n";
		ss << fieldTxt;
	}
	if (fieldCnt)
		ss << "\n";
	ss << closeIndent << "}";

	return ss.str();
}

std::string DartDumper::dumpInstanceFields(dart::Object& obj, DartClass& dartCls, intptr_t ptr, intptr_t offset, bool simpleForm, bool nestedObj, int depth)
{
	std::stringstream ss;
	std::string indent(depth * 2, ' ');

	const auto bitmap = dartCls.UnboxedFieldsBitmap();
	while (offset < dartCls.Size()) {
		std::string txtField;
		// TODO: match the offset to field name if possible
		if (bitmap.Get(offset / dart::kCompressedWordSize)) {
			// AOT uses native integer if it is less than 31 bits (compressed pointer)
			// integer (4/8 bytes) or double (8 bytes)
			if (dart::kCompressedWordSize == 4)
				RELEASE_ASSERT(bitmap.Get((offset + dart::kCompressedWordSize) / dart::kCompressedWordSize));
			auto p = reinterpret_cast<uint64_t*>(ptr + offset);
			// it is rare to find integer that larger than 0x1000_0000_0000_0000
			if (*p <= 0x1000000000000000 || *p >= 0xffffffffffff0000) {
				txtField = std::format("off_{:x}: int({:#x})", offset, *p);
			}
			else {
				txtField = std::format("off_{:x}: double({})", offset, *((double*)p));
			}
			offset += sizeof(uint64_t) - dart::kCompressedWordSize;
		}
		else if (offset != dartCls.TypeArgumentsOffset()) {
			// compressed object ptr
			auto p = reinterpret_cast<dart::CompressedObjectPtr*>(ptr + offset);
			if (*p != dart::CompressedObjectPtr(nullptr)) {
				if (p->IsHeapObject()) {
					auto objPtr2 = p->Decompress(app.heap_base());
					if (objPtr2 != nullptr && objPtr2.GetClassId() != dart::kNullCid) {
						obj = objPtr2;
						if (simpleForm || objPtr2.GetClassId() < dart::kNumPredefinedCids)
							txtField = std::format("off_{:x}: {}", offset, ObjectToString(obj, simpleForm, nestedObj, depth));
						else
							txtField = std::format("off_{:x}_{}", offset, ObjectToString(obj, simpleForm, nestedObj, depth));
					}
				}
				else {
					obj = p->DecompressSmi();
					txtField = std::format("off_{:x}_Smi: {:#x}", offset, dart::Smi::Cast(obj).Value());
				}
			}
		}
		offset += dart::kCompressedWordSize;

		if (!txtField.empty()) {
			if (ss.tellp() != 0)
				ss << ",\n";
			ss << indent << txtField;
		}
	}

	return ss.str();
}

std::string DartDumper::getPoolObjectDescription(intptr_t offset, bool simpleForm)
{
	const auto& pool = app.GetObjectPool();
	intptr_t idx = PoolIndexFromOffset(offset);
	offset = PoolInstructionOffset(offset);
	auto objType = pool.TypeAt(idx);
	// see how the EntryType is handled from vm/object_service.cc - ObjectPool::PrintJSONImpl()
	if (objType == dart::ObjectPool::EntryType::kTaggedObject) {
		auto& obj = dart::Object::Handle(pool.ObjectAt(idx));
		if (obj.IsUnlinkedCall()) {
			// EmitInstanceCallAOT places the entry before data on x64.
			const auto targetIndex = UnlinkedCallTargetIndex(idx);
			if (targetIndex < 0 || targetIndex >= pool.Length())
				return std::format("[pp+{:#x}] {}", offset, ObjectToString(obj, simpleForm));
			// Since Dart 3.10, target type might be kTaggedObject.
			auto unlinkTargetType = pool.TypeAt(targetIndex);
			if (unlinkTargetType == dart::ObjectPool::EntryType::kImmediate) {
				const auto imm = pool.RawValueAt(targetIndex);
				auto dartFn = app.GetFunction(imm - app.base());
				if (dartFn != nullptr) {
					return std::format("[pp+{:#x}] UnlinkedCall: {:#x} - {}", offset, dartFn->Address(), dartFn->FullName().c_str());
				}
				else {
					return std::format("[pp+{:#x}] UnlinkedCall: {:#x} - [unknown function]", offset, imm - app.base());
				}
			}
			else {
				ASSERT(unlinkTargetType == dart::ObjectPool::EntryType::kTaggedObject);
				auto& obj2 = dart::Object::Handle(pool.ObjectAt(targetIndex));
				return std::format("[pp+{:#x}] UnlinkedCall: {}", offset, ObjectToString(obj2, simpleForm));
			}
		}
		return std::format("[pp+{:#x}] {}", offset, ObjectToString(obj, simpleForm));
	}
	else if (objType == dart::ObjectPool::EntryType::kImmediate) {
		dart::uword imm = pool.RawValueAt(idx);
		if (imm <= 0x1000000000000000 || imm >= 0xffffffffffff0000) {
			return std::format("[pp+{:#x}] IMM: {:#x}", offset, imm);
		}
		else {
			return std::format("[pp+{:#x}] IMM: double({}) from {:#x}", offset, *((double*)&imm), imm);
		}
	}
	else if (objType == dart::ObjectPool::EntryType::kNativeFunction) {
		auto pc = pool.RawValueAt(idx);
		uintptr_t start = 0;
		auto name = dart::NativeSymbolResolver::LookupSymbolName(pc, &start);
		if (name != NULL) {
			auto txt = std::format("[pp+{:#x}] NativeFn: {} at {:#x}", offset, name, pc);
			dart::NativeSymbolResolver::FreeSymbolName(name);
			return txt;
		}
		else {
			return std::format("[pp+{:#x}] NativeFn: [no name] at {:#x}", offset, pc);
		}
	}
	else {
		throw std::runtime_error(std::format("unknown pool object type: {}", (int)objType).c_str());
	}
}

void DartDumper::DumpObjectPool(const char* filename)
{
	std::ofstream of(filename);
	const auto& pool = app.GetObjectPool();
	intptr_t num = pool.Length();

	const auto& rawObj = pool.ptr()->untag();
	const auto raw_addr = dart::UntaggedObject::ToAddr(rawObj);
	of << std::format("pool heap offset: {:#x}\n", raw_addr - app.heap_base());

	for (intptr_t i = 0; i < num; i++) {
		const auto offset = dart::ObjectPool::element_offset(i);
		auto txt = getPoolObjectDescription(offset, false);
		of << txt << "\n";
#if defined(TARGET_ARCH_ARM64)
		if (txt.compare(txt.find(']'), 15, "] UnlinkedCall:") == 0)
			i++; // ARM64 prints its following entry together with call data.
#endif
	}
}

void DartDumper::DumpObjects(const char* filename)
{
	std::ofstream of(filename);

	auto& obj = dart::Object::Handle();
	for (auto objPtr : knownObjectPtrs) {
		obj = dart::ObjectPtr(objPtr);
		const bool simpleForm = false;
		const bool nestedObj = true;
		of << dumpInstance(obj, simpleForm, nestedObj, 0);
		of << "\n\n";
	}
}
