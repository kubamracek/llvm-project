//===- clang/Basic/DirectoryEntry.h - Directory references ------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
///
/// \file
/// Defines interfaces for clang::DirectoryEntry and clang::DirectoryEntryRef.
///
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_BASIC_DIRECTORYENTRY_H
#define LLVM_CLANG_BASIC_DIRECTORYENTRY_H

#include "clang/Basic/LLVM.h"
#include "llvm/ADT/DenseMapInfo.h"
#include "llvm/ADT/Hashing.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/ErrorOr.h"

namespace clang {
namespace FileMgr {

template <class RefTy> class MapEntryOptionalStorage;

} // end namespace FileMgr

/// Cached information about one directory (either on disk or in
/// the virtual file system).
class DirectoryEntry {
  friend class FileManager;

  // FIXME: We should not be storing a directory entry name here.
  StringRef Name; // Name of the directory.

public:
  StringRef getName() const { return Name; }
};

/// A reference to a \c DirectoryEntry  that includes the name of the directory
/// as it was accessed by the FileManager's client.
class DirectoryEntryRef {
public:
  const DirectoryEntry &getDirEntry() const { return *ME->getValue(); }

  StringRef getName() const { return ME->getKey(); }

  /// Hash code is based on the DirectoryEntry, not the specific named
  /// reference.
  friend llvm::hash_code hash_value(DirectoryEntryRef Ref) {
    return llvm::hash_value(&Ref.getDirEntry());
  }

  using MapEntry = llvm::StringMapEntry<llvm::ErrorOr<DirectoryEntry &>>;

  const MapEntry &getMapEntry() const { return *ME; }

  /// Check if RHS referenced the file in exactly the same way.
  bool isSameRef(DirectoryEntryRef RHS) const { return ME == RHS.ME; }

  DirectoryEntryRef() = delete;
  DirectoryEntryRef(MapEntry &ME) : ME(&ME) {}

private:
  friend class FileMgr::MapEntryOptionalStorage<DirectoryEntryRef>;
  struct optional_none_tag {};

  // Private constructor for use by OptionalStorage.
  DirectoryEntryRef(optional_none_tag) : ME(nullptr) {}
  bool hasOptionalValue() const { return ME; }

  friend struct llvm::DenseMapInfo<DirectoryEntryRef>;
  struct dense_map_empty_tag {};
  struct dense_map_tombstone_tag {};

  // Private constructors for use by DenseMapInfo.
  DirectoryEntryRef(dense_map_empty_tag)
      : ME(llvm::DenseMapInfo<const MapEntry *>::getEmptyKey()) {}
  DirectoryEntryRef(dense_map_tombstone_tag)
      : ME(llvm::DenseMapInfo<const MapEntry *>::getTombstoneKey()) {}
  bool isSpecialDenseMapKey() const {
    return isSameRef(DirectoryEntryRef(dense_map_empty_tag())) ||
           isSameRef(DirectoryEntryRef(dense_map_tombstone_tag()));
  }

  const MapEntry *ME;
};

namespace FileMgr {

/// Customized storage for refs derived from map entires in FileManager, using
/// the private optional_none_tag to keep it to the size of a single pointer.
template <class RefTy> class MapEntryOptionalStorage {
  using optional_none_tag = typename RefTy::optional_none_tag;
  RefTy MaybeRef;

public:
  MapEntryOptionalStorage() : MaybeRef(optional_none_tag()) {}

  template <class... ArgTypes>
  explicit MapEntryOptionalStorage(llvm::optional_detail::in_place_t,
                                   ArgTypes &&...Args)
      : MaybeRef(std::forward<ArgTypes>(Args)...) {}

  void reset() { MaybeRef = optional_none_tag(); }

  bool hasValue() const { return MaybeRef.hasOptionalValue(); }

  RefTy &getValue() LLVM_LVALUE_FUNCTION {
    assert(hasValue());
    return MaybeRef;
  }
  RefTy const &getValue() const LLVM_LVALUE_FUNCTION {
    assert(hasValue());
    return MaybeRef;
  }
#if LLVM_HAS_RVALUE_REFERENCE_THIS
  RefTy &&getValue() && {
    assert(hasValue());
    return std::move(MaybeRef);
  }
#endif

  template <class... Args> void emplace(Args &&...args) {
    MaybeRef = RefTy(std::forward<Args>(args)...);
  }

  MapEntryOptionalStorage &operator=(RefTy Ref) {
    MaybeRef = Ref;
    return *this;
  }
};

} // end namespace FileMgr
} // end namespace clang

namespace llvm {
namespace optional_detail {

/// Customize OptionalStorage<DirectoryEntryRef> to use DirectoryEntryRef and
/// its optional_none_tag to keep it the size of a single pointer.
template <>
class OptionalStorage<clang::DirectoryEntryRef>
    : public clang::FileMgr::MapEntryOptionalStorage<clang::DirectoryEntryRef> {
  using StorageImpl =
      clang::FileMgr::MapEntryOptionalStorage<clang::DirectoryEntryRef>;

public:
  OptionalStorage() = default;

  template <class... ArgTypes>
  explicit OptionalStorage(in_place_t, ArgTypes &&...Args)
      : StorageImpl(in_place_t{}, std::forward<ArgTypes>(Args)...) {}

  OptionalStorage &operator=(clang::DirectoryEntryRef Ref) {
    StorageImpl::operator=(Ref);
    return *this;
  }
};

static_assert(sizeof(Optional<clang::DirectoryEntryRef>) ==
                  sizeof(clang::DirectoryEntryRef),
              "Optional<DirectoryEntryRef> must avoid size overhead");

static_assert(
    std::is_trivially_copyable<Optional<clang::DirectoryEntryRef>>::value,
    "Optional<DirectoryEntryRef> should be trivially copyable");

} // end namespace optional_detail

/// Specialisation of DenseMapInfo for DirectoryEntryRef.
template <> struct DenseMapInfo<clang::DirectoryEntryRef> {
  static inline clang::DirectoryEntryRef getEmptyKey() {
    return clang::DirectoryEntryRef(
        clang::DirectoryEntryRef::dense_map_empty_tag());
  }

  static inline clang::DirectoryEntryRef getTombstoneKey() {
    return clang::DirectoryEntryRef(
        clang::DirectoryEntryRef::dense_map_tombstone_tag());
  }

  static unsigned getHashValue(clang::DirectoryEntryRef Val) {
    return hash_value(Val);
  }

  static bool isEqual(clang::DirectoryEntryRef LHS,
                      clang::DirectoryEntryRef RHS) {
    // Catch the easy cases: both empty, both tombstone, or the same ref.
    if (LHS.isSameRef(RHS))
      return true;

    // Confirm LHS and RHS are valid.
    if (LHS.isSpecialDenseMapKey() || RHS.isSpecialDenseMapKey())
      return false;

    // Compare the two dir entries.
    return &LHS.getDirEntry() == &RHS.getDirEntry();
  }
};

} // end namespace llvm

#endif // LLVM_CLANG_BASIC_DIRECTORYENTRY_H
