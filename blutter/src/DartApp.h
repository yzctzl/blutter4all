#pragma once
#include "DartLibrary.h"
#include "DartClass.h"
#include "DartFunction.h"
#include "DartStub.h"
#include <unordered_map>
#include <memory>

class DartApp
{
public:
	explicit DartApp(const char* path);
	DartApp() = delete;
	~DartApp();

	void EnterScope();
	void ExitScope();

	void LoadInfo();

	intptr_t base() const { return (intptr_t)lib_base; }
	uint32_t offset(intptr_t addr) const { return (uint32_t)(addr - base()); }
	uintptr_t heap_base() const { return heap_base_; }

	DartClass* GetClass(intptr_t cid);
	DartClass* FindClass(intptr_t cid) const {
		return cid >= 0 && static_cast<size_t>(cid) < classes.size() ? classes[cid] : nullptr;
	}
	DartFnBase* GetFunction(uint64_t addr);
	DartFnBase* FindFunctionExact(uint64_t addr) const {
		if (auto found = functions.find(addr); found != functions.end())
			return found->second;
		if (auto found = stubs.find(addr); found != stubs.end())
			return found->second;
		return nullptr;
	}
	DartField* GetStaticField(intptr_t offset) { return staticFields.at(offset); }
	DartField* FindStaticField(intptr_t offset) const {
		auto found = staticFields.find(offset);
		return found != staticFields.end() ? found->second : nullptr;
	}

	dart::ObjectPool& GetObjectPool() { return *ppool; }
	DartTypeDb* TypeDb() { return typeDb.get(); }

	intptr_t DartIntCid() const { return dartIntCid; }
	intptr_t DartFutureCid() const { return dartFutureCid; }

private:
	DartLibrary* addLibraryClass(const dart::Library& library, const dart::Class& cls);
	DartLibrary* addLibrary(const dart::Library& library);
	void loadFromClassTable(dart::IsolateGroup* ig);
	void loadStubs(dart::ObjectStore* store);
	DartFunction* addFunctionNoCheck(const dart::Function& func);
	void addFunction(uintptr_t ep_addr, const dart::Function& func);
	void findFunctionInHeap();
	void finalizeFunctionsInfo();
	void loadFromObjectPool();
	void walkObject(dart::Object& obj); // to check field types from existed object

	std::shared_ptr<void> image_owner;
	const void* lib_base;
	const uint8_t* vm_snapshot_data;
	const uint8_t* vm_snapshot_instructions;
	const uint8_t* isolate_snapshot_data;
	const uint8_t* isolate_snapshot_instructions;

	dart::Isolate* isolate;
	uintptr_t heap_base_;
	dart::ObjectPool* ppool;
	bool inScope;

	// nativeLib contains all classes that has no library
	DartLibrary nativeLib;
	std::vector<DartLibrary*> libs;
	// some class might be null
	std::vector<DartClass*> classes;
	std::vector<DartClass*> topClasses;
	std::unordered_map<uint64_t, DartFunction*> functions;
	std::unordered_map<uint64_t, DartStub*> stubs;
	std::unordered_map<uint64_t, DartField*> staticFields;
	std::unique_ptr<DartTypeDb> typeDb;

	// the dart Bulit-in type class id
	intptr_t dartIntCid;
	intptr_t dartDoubleCid;
	intptr_t dartStringCid;
	intptr_t dartBoolCid;
	intptr_t dartRecordCid; // dart verion >= 3.0
	intptr_t dartListCid;
	intptr_t dartSetCid;
	intptr_t dartMapCid;
	intptr_t dartRunesCid;
	intptr_t dartFutureCid;

	intptr_t throwStubAddr;

	friend class CodeAnalyzer;
	friend class DartAnalyzer;
	friend class DartDumper;
	friend class FridaWriter;
};

