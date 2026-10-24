#include "pch.h"
#include "DartLibrary.h"
#include "DartClass.h"
#include <filesystem>
#include <string_view>

DartLibrary::DartLibrary(const dart::Library& lib) : ptr(lib.ptr()), topClass(NULL)
{
	auto& dtext = dart::String::Handle();
	dtext = lib.name();
	name = dtext.ToCString();
	dtext = lib.url();
	url = dtext.ToCString();

	if (lib.is_dart_scheme())
		isInternal = true;
	//else if (url.starts_with("package:flutter/src/") || url.starts_with("package:typed_data/src/") || url.starts_with("package:collection/src/"))
	//	isInternal = true;
	else
		isInternal = false;

	// add all classes belong to this library
	auto& cls = dart::Class::Handle();
	cls = lib.toplevel_class();
	topClass = AddClass(cls);
	id = topClass->Id();

	dart::DictionaryIterator iter(lib);
	while (iter.HasNext()) {
		auto objPtr = iter.GetNext();
		// only 4 possible types but functions and fields are in top level class
		if (objPtr.IsClass()) {
			cls = dart::Class::RawCast(objPtr);
			AddClass(cls);
		}
		else if (objPtr.IsFunction()) {
			// TODO: check if top level class contain this function
		}
		else if (objPtr.IsField()) {
			// TODO: check if top level class contain this field
		}
		else if (objPtr.IsLibraryPrefix()) {
			throw std::runtime_error("library prefix in AOT");
		}
		else {
			throw std::runtime_error("unknown type in library");
		}
	}
}

DartLibrary::~DartLibrary()
{
	for (auto cls : classes) {
		delete cls;
	}
}

// Keep normal library paths readable. Invalid URIs get a stable, unique name
// rather than becoming host paths (including Windows drive/stream names).
static std::filesystem::path libraryPath(const std::string& url, uint32_t id)
{
	std::string relative;
	if (url.starts_with("package:")) {
		relative = url.substr(8);
	}
	else if (url.starts_with("file:///")) {
		const auto tool = url.find("/.dart_tool/");
		if (tool != std::string::npos) {
			relative = url.substr(tool + 1);
		}
		else {
			// Retain the last directory to distinguish lib/main.dart from
			// test/main.dart without exposing an absolute build-machine path.
			const auto last = url.rfind('/');
			const auto parent = last > 7 ? url.rfind('/', last - 1) : last;
			relative = url.substr(parent + 1);
		}
	}
	else if (url.starts_with("dart:")) {
		relative = "dart/" + url.substr(5) + ".dart";
	}
	else {
		relative = url + ".dart";
	}

	bool valid = !relative.empty() && relative.front() != '/' && relative.back() != '/';
	size_t start = 0;
	while (valid && start < relative.size()) {
		const auto end = relative.find('/', start);
		const auto part = relative.substr(start, end - start);
		valid = !part.empty() && part != "." && part != ".." &&
			part.back() != '.' && part.back() != ' ';
		for (unsigned char c : part) {
			if (c < 0x20 || std::string_view("<>:\\|?*\"").find(c) != std::string_view::npos)
				valid = false;
		}
		auto stem = part.substr(0, part.find('.'));
		for (auto& c : stem) {
			if (c >= 'a' && c <= 'z') c -= 'a' - 'A';
		}
		if (stem.ends_with(' ') || stem == "CONIN$" || stem == "CONOUT$" ||
			stem == "CON" || stem == "PRN" || stem == "AUX" || stem == "NUL")
			valid = false;
		if (stem.starts_with("COM") || stem.starts_with("LPT")) {
			const auto number = stem.substr(3);
			// Windows also recognizes the superscript digits 1, 2 and 3.
			if ((number.size() == 1 && number[0] >= '1' && number[0] <= '9') ||
				number == "\xc2\xb9" || number == "\xc2\xb2" || number == "\xc2\xb3")
				valid = false;
		}
		if (end == std::string::npos)
			break;
		start = end + 1;
	}
	if (!valid || url.empty())
		return std::filesystem::path("_unknown") / std::format("lib_{:x}.dart", id);
	if (!relative.ends_with(".dart"))
		relative += ".dart";
	return relative;
}

std::string DartLibrary::GetName()
{
	auto out = libraryPath(url, id).generic_string();
	out.erase(out.size() - 5);
	std::replace(out.begin(), out.end(), '/', '$');
	if (url.starts_with("dart:") && out.starts_with("dart$"))
		out[4] = '_';
	return out;
}

DartClass* DartLibrary::AddClass(const dart::Class& cls)
{
	auto dartCls = new DartClass(*this, cls);
	classes.push_back(dartCls);
	return dartCls;
}

std::string DartLibrary::CreatePath(const char* base_dir)
{
	const auto root = std::filesystem::weakly_canonical(base_dir);
	const auto path = root / libraryPath(url, id);
	auto checkPath = [&] {
		const auto resolved = std::filesystem::weakly_canonical(path);
		if (std::filesystem::is_symlink(path) ||
			std::mismatch(root.begin(), root.end(), resolved.begin(), resolved.end()).first != root.end())
			throw std::runtime_error("Library output path escapes output directory");
	};
	// Resolve existing symlinks as well as '..' before creating directories.
	checkPath();
	std::filesystem::create_directories(path.parent_path());
	checkPath();
	return path.string();
}

void DartLibrary::PrintCommentInfo(std::ostream& of)
{
	of << std::format("// lib: {}, url: {}\n", name.c_str(), url.c_str());
}
