#include "pch.h"
#include "ObjectPool.h"
#include "CodeAnalyzer.h"
#include "DartApp.h"
#include "DartThreadInfo.h"

#ifndef NO_CODE_ANALYSIS

VarValue* getPoolObject(DartApp& app, intptr_t offset, CpuRegister dstReg)
{
	intptr_t idx = PoolIndexFromOffset(offset);
	auto& pool = app.GetObjectPool();
	auto objType = pool.TypeAt(idx);
	// see how the EntryType is handled from vm/object_service.cc - ObjectPool::PrintJSONImpl()
	if (objType == dart::ObjectPool::EntryType::kTaggedObject) {
		//val = (uintptr_t)pool.ObjectAt(idx);
		auto ptr = pool.ObjectAt(idx);
		// Smi is special case. Have to handle first
		if (!ptr.IsHeapObject()) {
			return new VarInteger(dart::RawSmiValue(dart::Smi::RawCast(ptr)), dart::kSmiCid);
		}

		if (ptr.IsRawNull())
			return new VarNull();

		auto& obj = dart::Object::Handle(ptr);
		if (obj.IsString())
			return new VarString(dart::String::Cast(obj).ToCString());

		// use TypedData or TypedDataBase ?
		if (obj.IsTypedData()) {
			//dart::kTypedDataInt32ArrayCid;
			//auto& data = dart::TypedData::Cast(obj);
			return new VarExpression(std::format("{}", obj.ToCString()), (int32_t)obj.GetClassId());
		}

		switch (obj.GetClassId()) {
		case dart::kSmiCid:
			return new VarInteger(dart::Smi::Cast(obj).Value(), dart::kSmiCid);
		case dart::kMintCid:
			return new VarInteger(MintValue(dart::Mint::Cast(obj)), dart::kMintCid);
		case dart::kDoubleCid:
			return new VarDouble(dart::Double::Cast(obj).value());
		case dart::kBoolCid:
			return new VarBoolean(dart::Bool::Cast(obj).value());
		case dart::kNullCid:
			return new VarNull();
		case dart::kCodeCid: {
			const auto& code = dart::Code::Cast(obj);
			auto stub = app.GetFunction(code.EntryPoint() - app.base());
			ASSERT(stub);
			return new VarFunctionCode(*stub);
		}
		case dart::kFieldCid: {
			const auto& field = dart::Field::Cast(obj);
			auto dartCls = app.GetClass(field.Owner().untag()->id());
			auto dartField = dartCls->FindField(field.TargetOffset());
			//auto dartField = app.GetStaticField(field.TargetOffset());
			ASSERT(dartField);
			return new VarField(*dartField);
		}
		case dart::kArrayCid:
		case dart::kImmutableArrayCid:
			return new VarArray(dart::Array::Cast(obj).ptr());
		// should function and closure be their var types?
		case dart::kFunctionCid:
		case dart::kClosureCid:
		case dart::kConstMapCid:
			// TODO: map
		case dart::kConstSetCid:
			// TODO: set
			return new VarExpression(std::format("{}", obj.ToCString()), (int32_t)obj.GetClassId());
#ifdef HAS_RECORD_TYPE
		case dart::kRecordCid: {
			// temporary expression for Record object (need full object for analysis)
			//const auto& rec = dart::Record::Cast(obj);
			return new VarExpression(std::format("{}", obj.ToCString()), (int32_t)obj.GetClassId());
		}
#endif
		case dart::kTypeParametersCid:
			throw std::runtime_error("Type parameter in Object Pool");
		case dart::kTypeCid:
			return new VarType(*app.TypeDb()->FindOrAdd(dart::Type::Cast(obj).ptr()));
#ifdef HAS_RECORD_TYPE
		case dart::kRecordTypeCid:
			return new VarRecordType(*app.TypeDb()->FindOrAdd(dart::RecordType::Cast(obj).ptr()));
#endif
		case dart::kTypeParameterCid:
			return new VarTypeParameter(*app.TypeDb()->FindOrAdd(dart::TypeParameter::Cast(obj).ptr()));
		case dart::kFunctionTypeCid:
			return new VarFunctionType(*app.TypeDb()->FindOrAdd(dart::FunctionType::Cast(obj).ptr()));
		case dart::kTypeArgumentsCid: {
			return new VarTypeArgument(*app.TypeDb()->FindOrAdd(dart::TypeArguments::Cast(obj).ptr()));
		}
		case dart::kSentinelCid:
			return new VarSentinel();
		case dart::kUnlinkedCallCid: {
			// x64 emits entrypoint before call data; ARM64 emits it after.
			const auto targetIndex = UnlinkedCallTargetIndex(idx);
			if (targetIndex >= 0 && targetIndex < pool.Length() &&
				pool.TypeAt(targetIndex) == dart::ObjectPool::EntryType::kImmediate) {
				auto fn = app.GetFunction(pool.RawValueAt(targetIndex) - app.base());
				if (fn && fn->IsStub()) return new VarUnlinkedCall(*fn->AsStub());
			}
			return new VarExpression(obj.ToCString(), dart::kUnlinkedCallCid);
		}
		case dart::kSubtypeTestCacheCid:
			return new VarSubtypeTestCache();
		case dart::kInt32x4Cid:
		case dart::kFloat32x4Cid:
		case dart::kFloat64x2Cid:
			return new VarExpression(std::format("{}", obj.ToCString()), (int32_t)obj.GetClassId());
		case dart::kLibraryPrefixCid:
			// TODO: handle LibraryPrefix object
		case dart::kInstanceCid:
			return new VarInstance(app.GetClass(dart::kInstanceCid));
		}

		if (obj.IsInstance()) {
			auto dartCls = app.GetClass(obj.GetClassId());
			if (dartCls->Id() < dart::kNumPredefinedCids) {
				std::cerr << std::format("Unhandle predefined class {} ({})\n", dartCls->Name(), dartCls->Id());
			}
			return new VarInstance(dartCls);
		}

		throw std::runtime_error("unhandle object class in getPoolObject");
		//auto txt = std::format("XXX: {}", obj.ToCString());
		//return new VarExpression(txt);
	}
	else if (objType == dart::ObjectPool::EntryType::kImmediate) {
		auto imm = pool.RawValueAt(idx);
		if (dstReg.IsDecimal())
			return new VarDouble(*((double*)&imm), VarType::NativeDouble);
		return new VarInteger(imm, VarValue::NativeInt);
	}
	else if (objType == dart::ObjectPool::EntryType::kNativeFunction) {
		//val = pool.RawValueAt(idx);
		throw std::runtime_error("getting native function pool object from Dart code");
	}
	else {
		throw std::runtime_error(std::format("unknown pool object type: {}", (int)objType).c_str());
	}
}

AnalyzedFnData::AnalyzedFnData(DartApp& app, DartFunction& dartFn, AsmTexts asmTexts)
	: app(app), dartFn(dartFn), asmTexts(std::move(asmTexts))
{
	// Without a declaration, observed entry loads cannot prove unused parameters.
	params.isPartial = dartFn.Ptr() == dart::Function::null();
}

void CodeAnalyzer::AnalyzeAll()
{
	Disassembler disasmer;

	for (auto lib : app.libs) {
		if (lib->isInternal)
			continue;
		for (auto cls : lib->classes) {
			for (auto dartFn : cls->Functions()) {
				if (dartFn->Size() <= 0)
					continue;

				// start from PayloadAddress or Address?
				// the assemblies will be deleted after finish analysis because assembly with details consume too much memory
				auto asm_insns = disasmer.Disasm((uint8_t*)dartFn->MemAddress(), dartFn->Size(), dartFn->Address());

				if (asm_insns.Count() == 0)
					throw std::runtime_error("Cannot decode function at " + std::to_string(dartFn->Address()));

				dartFn->SetAnalyzedData(std::make_unique<AnalyzedFnData>(app, *dartFn, convertAsm(asm_insns)));

				asm2il(dartFn, asm_insns);
			}
		}
	}
}

#endif // NO_CODE_ANALYSIS

std::string FnParamInfo::ToString() const
{
	std::string txt = type ? type->ToString() : "dynamic";
	txt += ' ';
	txt += name.empty() ? "_" : name;
	if (val) {
		txt += " = ";
		txt += val->ToString();
	}
	if (paramReg.IsSet() || paramOffset || valReg.IsSet() || localOffset) {
		txt += " /* ";
		if (paramReg.IsSet()) {
			txt += paramReg.Name();
		}
		else if (paramOffset) {
			txt += std::format("fp+{:#x}", paramOffset);
		}
		if ((paramReg.IsSet() || paramOffset) && (valReg.IsSet() || localOffset))
			txt += " => ";
		if (valReg.IsSet()) {
			txt += valReg.Name();
			if (localOffset)
				txt += ", ";
		}
		if (localOffset)
			txt += std::format("fp-{:#x}", -localOffset);
		txt += " */";
	}
	return txt;
}

FnParamInfo* FnParams::findValReg(CpuRegister reg)
{
	for (auto& param : params) {
		if (param.valReg == reg) {
			return &param;
		}
	}
	return nullptr;
}

bool FnParams::movValReg(CpuRegister dstReg, CpuRegister srcReg)
{
	for (auto& param : params) {
		if (param.valReg == srcReg) {
			param.valReg = dstReg;
			return true;
		}
	}
	return false;
}

std::string FnParams::ToString() const
{
	std::string txt;
	for (int i = 0; i < params.size(); i++) {
		if (i != 0)
			txt += ", ";
		if (i == numFixedParam)
			txt += isNamedParam ? '{' : '[';

		txt += params[i].ToString();
	}

	if (numFixedParam < params.size())
		txt += isNamedParam ? '}' : ']';

	return isPartial ? txt + " /* partial */" : txt;
}
