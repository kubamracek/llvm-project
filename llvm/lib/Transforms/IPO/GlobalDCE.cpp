//===-- GlobalDCE.cpp - DCE unreachable internal functions ----------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This transform is designed to eliminate unreachable internal globals from the
// program.  It uses an aggressive algorithm, searching out globals that are
// known to be alive.  After it finds all of the globals which are needed, it
// deletes whatever is left over.  This allows it to delete recursive chunks of
// the program which are unreachable.
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/IPO/GlobalDCE.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/TypeMetadataUtils.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/InitializePasses.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Transforms/Utils/CtorUtils.h"
#include "llvm/Transforms/Utils/GlobalStatus.h"

using namespace llvm;

#define DEBUG_TYPE "globaldce"
#undef LLVM_DEBUG
#define LLVM_DEBUG(x) if (VerboseGlobalDCE) { x ; }

bool VerboseGlobalDCE = false;

static cl::opt<bool>
    ClEnableVFE("enable-vfe", cl::Hidden, cl::init(true), cl::ZeroOrMore,
                cl::desc("Enable virtual function elimination"));

STATISTIC(NumAliases  , "Number of global aliases removed");
STATISTIC(NumFunctions, "Number of functions removed");
STATISTIC(NumIFuncs,    "Number of indirect functions removed");
STATISTIC(NumVariables, "Number of global variables removed");
STATISTIC(NumVFuncs,    "Number of virtual functions removed");

namespace {
  class GlobalDCELegacyPass : public ModulePass {
  public:
    static char ID; // Pass identification, replacement for typeid
    GlobalDCELegacyPass() : ModulePass(ID) {
      initializeGlobalDCELegacyPassPass(*PassRegistry::getPassRegistry());
    }

    // run - Do the GlobalDCE pass on the specified module, optionally updating
    // the specified callgraph to reflect the changes.
    //
    bool runOnModule(Module &M) override {
      if (skipModule(M))
        return false;

      // We need a minimally functional dummy module analysis manager. It needs
      // to at least know about the possibility of proxying a function analysis
      // manager.
      FunctionAnalysisManager DummyFAM;
      ModuleAnalysisManager DummyMAM;
      DummyMAM.registerPass(
          [&] { return FunctionAnalysisManagerModuleProxy(DummyFAM); });

      auto PA = Impl.run(M, DummyMAM);
      return !PA.areAllPreserved();
    }

  private:
    GlobalDCEPass Impl;
  };
}

char GlobalDCELegacyPass::ID = 0;
INITIALIZE_PASS(GlobalDCELegacyPass, "globaldce",
                "Dead Global Elimination", false, false)

// Public interface to the GlobalDCEPass.
ModulePass *llvm::createGlobalDCEPass() {
  return new GlobalDCELegacyPass();
}

/// Returns true if F is effectively empty.
static bool isEmptyFunction(Function *F) {
  BasicBlock &Entry = F->getEntryBlock();
  for (auto &I : Entry) {
    if (isa<DbgInfoIntrinsic>(I))
      continue;
    if (auto *RI = dyn_cast<ReturnInst>(&I))
      return !RI->getReturnValue();
    break;
  }
  return false;
}

/// Compute the set of GlobalValue that depends from V.
/// The recursion stops as soon as a GlobalValue is met.
void GlobalDCEPass::ComputeDependencies(Value *V,
                                        SmallPtrSetImpl<GlobalValue *> &Deps) {
  if (auto *I = dyn_cast<Instruction>(V)) {
    Function *Parent = I->getParent()->getParent();
    Deps.insert(Parent);
  } else if (auto *GV = dyn_cast<GlobalValue>(V)) {
    Deps.insert(GV);
  } else if (auto *CE = dyn_cast<Constant>(V)) {
    // Avoid walking the whole tree of a big ConstantExprs multiple times.
    auto Where = ConstantDependenciesCache.find(CE);
    if (Where != ConstantDependenciesCache.end()) {
      auto const &K = Where->second;
      Deps.insert(K.begin(), K.end());
    } else {
      SmallPtrSetImpl<GlobalValue *> &LocalDeps = ConstantDependenciesCache[CE];
      for (User *CEUser : CE->users())
        ComputeDependencies(CEUser, LocalDeps);
      Deps.insert(LocalDeps.begin(), LocalDeps.end());
    }
  }
}

void GlobalDCEPass::UpdateGVDependencies(GlobalValue &GV) {
  SmallPtrSet<GlobalValue *, 8> Deps;
  for (User *User : GV.users())
    ComputeDependencies(User, Deps);
  Deps.erase(&GV); // Remove self-reference.
  for (GlobalValue *GVU : Deps) {
    // If this is a dep from a vtable to a virtual function, and we have
    // complete information about all virtual call sites which could call
    // though this vtable, then skip it, because the call site information will
    // be more precise.
    if (VFESafeVTables.count(GVU) && isa<Function>(&GV)) {
      bool OffsetFound = false;
      if (auto VTable = dyn_cast<GlobalVariable>(GVU)) {
        // Gather the !type metadata
        SmallVector<MDNode *, 2> Types;
        VTable->getMetadata(LLVMContext::MD_type, Types);
        if (VTable->isDeclaration() || Types.empty()) continue;

        // Check if the offset is found
        for (MDNode *Type : Types) {
          uint64_t OffsetInType = cast<ConstantInt>(cast<ConstantAsMetadata>(Type->getOperand(0))->getValue())->getZExtValue();
          Constant *Ptr = getPointerAtOffset(VTable->getInitializer(), OffsetInType, *VTable->getParent());
          Ptr = Ptr ? Ptr->stripPointerCasts() : nullptr;
          if (Ptr == &GV) { OffsetFound = true; break; }
        }
      }

      if (OffsetFound) {
        LLVM_DEBUG(dbgs() << "Ignoring dep " << GVU->getName() << " -> "
                          << GV.getName() << "\n");
        continue;
      }
    }
    GVDependencies[GVU].insert(&GV);
  }
}

/// Mark Global value as Live
void GlobalDCEPass::MarkLive(GlobalValue &GV,
                             SmallVectorImpl<GlobalValue *> *Updates) {
  auto const Ret = AliveGlobals.insert(&GV);
  if (!Ret.second)
    return;

  if (Updates)
    Updates->push_back(&GV);
  if (Comdat *C = GV.getComdat()) {
    for (auto &&CM : make_range(ComdatMembers.equal_range(C))) {
      MarkLive(*CM.second, Updates); // Recursion depth is only two because only
                                     // globals in the same comdat are visited.
    }
  }
}

void GlobalDCEPass::ScanVTables(Module &M) {
  SmallVector<MDNode *, 2> Types;
  LLVM_DEBUG(dbgs() << "Building type info -> vtable map\n");

  auto *LTOPostLinkMD =
      cast_or_null<ConstantAsMetadata>(M.getModuleFlag("LTOPostLink"));
  bool LTOPostLink =
      LTOPostLinkMD &&
      (cast<ConstantInt>(LTOPostLinkMD->getValue())->getZExtValue() != 0);

  for (GlobalVariable &GV : M.globals()) {
    Types.clear();
    GV.getMetadata(LLVMContext::MD_type, Types);
    if (GV.isDeclaration() || Types.empty())
      continue;

    // Use the typeid metadata on the vtable to build a mapping from typeids to
    // the list of (GV, offset) pairs which are the possible vtables for that
    // typeid.
    for (MDNode *Type : Types) {
      Metadata *TypeID = Type->getOperand(1).get();

      uint64_t Offset =
          cast<ConstantInt>(
              cast<ConstantAsMetadata>(Type->getOperand(0))->getValue())
              ->getZExtValue();

      TypeIdMap[TypeID].insert(std::make_pair(&GV, Offset));
    }

    // If the type corresponding to the vtable is private to this translation
    // unit, we know that we can see all virtual functions which might use it,
    // so VFE is safe.
    if (auto GO = dyn_cast<GlobalObject>(&GV)) {
      GlobalObject::VCallVisibility TypeVis = GO->getVCallVisibility();
      if (TypeVis == GlobalObject::VCallVisibilityTranslationUnit ||
          (LTOPostLink &&
           TypeVis == GlobalObject::VCallVisibilityLinkageUnit)) {
        LLVM_DEBUG(dbgs() << GV.getName() << " is safe for VFE\n");
        VFESafeVTables.insert(&GV);
      }
    }
  }
}

void GlobalDCEPass::ScanVTableLoad(Function *Caller, Metadata *TypeId,
                                   uint64_t CallOffset) {
  for (auto &VTableInfo : TypeIdMap[TypeId]) {
    GlobalVariable *VTable = VTableInfo.first;
    uint64_t VTableOffset = VTableInfo.second;

    Constant *Ptr =
        getPointerAtOffset(VTable->getInitializer(), VTableOffset + CallOffset,
                           *Caller->getParent());
    if (!Ptr) {
      LLVM_DEBUG(dbgs() << "can't find pointer in vtable!\n");
      LLVM_DEBUG(dbgs() << "TypeId: " << *TypeId << "\n");
      LLVM_DEBUG(dbgs() << "VTableOffset: " << VTableOffset << "\n");
      LLVM_DEBUG(dbgs() << "CallOffset: " << CallOffset << "\n");
      LLVM_DEBUG(dbgs() << "VTable: " << *VTable << "\n");
      VFESafeVTables.erase(VTable);
      abort();
      return;
    }

    if (auto Callee = dyn_cast<Function>(Ptr->stripPointerCasts())) {
      LLVM_DEBUG(dbgs() << "vfunc dep " << Caller->getName() << " -> "
                        << Callee->getName() << "\n");
      GVDependencies[Caller].insert(Callee);
    } else if (auto Callee = dyn_cast<GlobalVariable>(Ptr->stripPointerCasts())) {
      if (Callee->getName().endswith(".ptrauth")) {
        GVDependencies[Caller].insert(Callee);
      } else {
        LLVM_DEBUG(dbgs() << "GV but not ptrauth!\n");
        LLVM_DEBUG(dbgs() << *Caller << "\n");
        LLVM_DEBUG(dbgs() << *Ptr << "\n");
        LLVM_DEBUG(dbgs() << *(Ptr->stripPointerCasts()) << "\n");
        LLVM_DEBUG(dbgs() << "VTableOffset: " << VTableOffset << "\n");
        LLVM_DEBUG(dbgs() << "CallOffset: " << CallOffset << "\n");
        LLVM_DEBUG(dbgs() << "VTable: " << *VTable << "\n");
        abort();
      }
    } else if (auto CI = dyn_cast<ConstantInt>(Ptr)) {
      continue;
    } else {
      LLVM_DEBUG(dbgs() << "vtable entry is not function pointer!\n");
      LLVM_DEBUG(dbgs() << *Ptr << "\n");
      LLVM_DEBUG(dbgs() << *(Ptr->stripPointerCasts()) << "\n");
      abort();

      VFESafeVTables.erase(VTable);
      return;
    }
  }
}

void GlobalDCEPass::ScanTypeCheckedLoadIntrinsics(Module &M) {
  LLVM_DEBUG(dbgs() << "Scanning type.checked.load intrinsics\n");
  Function *TypeCheckedLoadFunc =
      M.getFunction(Intrinsic::getName(Intrinsic::type_checked_load));

  if (!TypeCheckedLoadFunc)
    return;

  for (auto U : TypeCheckedLoadFunc->users()) {
    auto CI = dyn_cast<CallInst>(U);
    if (!CI)
      continue;

    auto *Offset = dyn_cast<ConstantInt>(CI->getArgOperand(1));
    Value *TypeIdValue = CI->getArgOperand(2);
    auto *TypeId = cast<MetadataAsValue>(TypeIdValue)->getMetadata();

    if (Offset) {
      ScanVTableLoad(CI->getFunction(), TypeId, Offset->getZExtValue());
    } else {
      // type.checked.load with a non-constant offset, so assume every entry in
      // every matching vtable is used.
      for (auto &VTableInfo : TypeIdMap[TypeId]) {
        VFESafeVTables.erase(VTableInfo.first);
      }
    }
  }
}

void GlobalDCEPass::AddVirtualFunctionDependencies(Module &M) {
  if (!ClEnableVFE)
    return;

  // If the Virtual Function Elim module flag is present and set to zero, then
  // the vcall_visibility metadata was inserted for another optimization (WPD)
  // and we may not have type checked loads on all accesses to the vtable.
  // Don't attempt VFE in that case.
  auto *Val = mdconst::dyn_extract_or_null<ConstantInt>(
      M.getModuleFlag("Virtual Function Elim"));
  if (!Val || Val->getZExtValue() == 0)
    return;

  ScanVTables(M);

  if (VFESafeVTables.empty())
    return;

  ScanTypeCheckedLoadIntrinsics(M);

  LLVM_DEBUG(
    dbgs() << "VFE safe vtables:\n";
    for (auto *VTable : VFESafeVTables)
      dbgs() << "  " << VTable->getName() << "\n";
  );
}

static int compareNames(Constant *const *A, Constant *const *B) {
  Value *AStripped = (*A)->stripPointerCasts();
  Value *BStripped = (*B)->stripPointerCasts();
  return AStripped->getName().compare(BStripped->getName());
}

static GlobalVariable *setUsedInitializer(GlobalVariable &V,
                               const SmallPtrSetImpl<GlobalValue *> &Init) {
  if (Init.empty()) {
    V.eraseFromParent();
    return nullptr;
  }

  // Type of pointer to the array of pointers.
  PointerType *Int8PtrTy = Type::getInt8PtrTy(V.getContext(), 0);

  SmallVector<Constant *, 8> UsedArray;
  for (GlobalValue *GV : Init) {
    Constant *Cast
      = ConstantExpr::getPointerBitCastOrAddrSpaceCast(GV, Int8PtrTy);
    UsedArray.push_back(Cast);
  }
  // Sort to get deterministic order.
  array_pod_sort(UsedArray.begin(), UsedArray.end(), compareNames);
  ArrayType *ATy = ArrayType::get(Int8PtrTy, UsedArray.size());

  Module *M = V.getParent();
  V.removeFromParent();
  GlobalVariable *NV =
      new GlobalVariable(*M, ATy, false, GlobalValue::AppendingLinkage,
                         ConstantArray::get(ATy, UsedArray), "");
  NV->takeName(&V);
  NV->setSection("llvm.metadata");
  delete &V;
  return NV;
}

PreservedAnalyses GlobalDCEPass::run(Module &M, ModuleAnalysisManager &MAM) {
  VerboseGlobalDCE = getenv("VERBOSE_GLOBALDCE") != nullptr;
  LLVM_DEBUG(dbgs() << "GlobalDCEPass::run\n");

  bool Changed = false;

  // The algorithm first computes the set L of global variables that are
  // trivially live.  Then it walks the initialization of these variables to
  // compute the globals used to initialize them, which effectively builds a
  // directed graph where nodes are global variables, and an edge from A to B
  // means B is used to initialize A.  Finally, it propagates the liveness
  // information through the graph starting from the nodes in L. Nodes note
  // marked as alive are discarded.

  // Remove empty functions from the global ctors list.
  Changed |= optimizeGlobalCtorsList(M, isEmptyFunction);

  // Collect the set of members for each comdat.
  for (Function &F : M)
    if (Comdat *C = F.getComdat())
      ComdatMembers.insert(std::make_pair(C, &F));
  for (GlobalVariable &GV : M.globals())
    if (Comdat *C = GV.getComdat())
      ComdatMembers.insert(std::make_pair(C, &GV));
  for (GlobalAlias &GA : M.aliases())
    if (Comdat *C = GA.getComdat())
      ComdatMembers.insert(std::make_pair(C, &GA));

  // Add dependencies between virtual call sites and the virtual functions they
  // might call, if we have that information.
  AddVirtualFunctionDependencies(M);

  auto *LTOPostLinkMD =
      cast_or_null<ConstantAsMetadata>(M.getModuleFlag("LTOPostLink"));
  bool LTOPostLink =
      LTOPostLinkMD &&
      (cast<ConstantInt>(LTOPostLinkMD->getValue())->getZExtValue() != 0);

  auto *Used = M.getGlobalVariable("llvm.used");
  auto *UsedConditional = M.getNamedMetadata("llvm.used.conditional"); 
  if (UsedConditional && UsedConditional->getNumOperands() == 0)
      UsedConditional = nullptr;
  SmallPtrSet<GlobalValue *, 8> NewUsedArray;
  if (LTOPostLink && Used) {
    // Construct a set of conditionally used targets.
    SmallPtrSet<GlobalValue *, 8> UsedConditionalTargets;
    if (UsedConditional) {
      for (auto *M : UsedConditional->operands()) {
        assert(M->getNumOperands() == 3);
        auto *V = mdconst::extract_or_null<GlobalValue>(M->getOperand(0));
        if (!V) continue;
        UsedConditionalTargets.insert(V);
      }
    }

    // Strip away all conditionally used targets from @llvm.used.
    const ConstantArray *Init = cast<ConstantArray>(Used->getInitializer());
    for (Value *Op : Init->operands()) {
      GlobalValue *G = cast<GlobalValue>(Op->stripPointerCasts());
      // G is one of the conditional targets, don't mark it as live.
      if (UsedConditionalTargets.contains(G)) continue;
      NewUsedArray.insert(G);
    }
    Used = setUsedInitializer(*Used, NewUsedArray);
  }

  // Loop over the module, adding globals which are obviously necessary.
  for (GlobalObject &GO : M.global_objects()) {
    Changed |= RemoveUnusedGlobalValue(GO);
    // Functions with external linkage are needed if they have a body.
    // Externally visible & appending globals are needed, if they have an
    // initializer.
    if (!GO.isDeclaration())
      if (!GO.isDiscardableIfUnused()) {
        //errs() << "GlobalDCE root: " << GO.getName() << "\n";
        MarkLive(GO);
      }

    UpdateGVDependencies(GO);
  }

  // Compute direct dependencies of aliases.
  for (GlobalAlias &GA : M.aliases()) {
    Changed |= RemoveUnusedGlobalValue(GA);
    // Externally visible aliases are needed.
    if (!GA.isDiscardableIfUnused())
      MarkLive(GA);

    UpdateGVDependencies(GA);
  }

  // Compute direct dependencies of ifuncs.
  for (GlobalIFunc &GIF : M.ifuncs()) {
    Changed |= RemoveUnusedGlobalValue(GIF);
    // Externally visible ifuncs are needed.
    if (!GIF.isDiscardableIfUnused())
      MarkLive(GIF);

    UpdateGVDependencies(GIF);
  }

  {
  // Propagate liveness from collected Global Values through the computed
  // dependencies.
  SmallVector<GlobalValue *, 8> NewLiveGVs{AliveGlobals.begin(),
                                           AliveGlobals.end()};
  while (!NewLiveGVs.empty()) {
    GlobalValue *LGV = NewLiveGVs.pop_back_val();
    for (auto *GVD : GVDependencies[LGV]) {
      //errs() << LGV->getName() << " live therefore also alive: " << GVD->getName() << "\n";
      MarkLive(*GVD, &NewLiveGVs);
    }
  }
  }

  bool VerboseUsedConditional = getenv("VERBOSE_USED_CONDITIONAL") != nullptr;

  if (LTOPostLink && Used && UsedConditional) {
    if (VerboseUsedConditional) errs() << "Optimizing UsedConditional" << "\n";
    for (auto *M : UsedConditional->operands()) {
      assert(M->getNumOperands() == 3);
      auto *V = mdconst::extract_or_null<GlobalValue>(M->getOperand(0));
      if (!V) continue;
      auto *T = mdconst::extract_or_null<ConstantInt>(M->getOperand(1));
      if (!T) continue;
      APInt type = T->getValue();

      SmallPtrSet<GlobalValue *, 8> Others;
      if (M->getOperand(2) == nullptr) {
        Others.insert(nullptr);
      } else {
        if (auto *SingleOther = mdconst::dyn_extract_or_null<GlobalValue>(M->getOperand(2))) {
          Others.insert(SingleOther);
        } else {
          Metadata *MultipleOthers = M->getOperand(2).get();
          MDNode *node = dyn_cast_or_null<MDNode>(MultipleOthers);
          for (auto &x : node->operands()) {
            auto *y = x.get();
            if (!y) continue;
            if (VerboseUsedConditional) y->dump();
            auto *C = mdconst::extract_or_null<Constant>(y);
            C = C->stripPointerCasts();
            auto *O = cast<GlobalValue>(C);
            Others.insert(O);
          }
        }
      }

      bool allOthersAlive = true;
      bool anyOtherAlive = false;
      if (VerboseUsedConditional) errs() << "Conditional: " << V->getName() << "\n";
      for (auto *GV : Others) {
        bool live = AliveGlobals.count(GV) != 0;
        if (live) if (VerboseUsedConditional) errs() << "  <- " << GV->getName() << "\n";
        if (live) anyOtherAlive = true;
        else allOthersAlive = false;
      }

      if (type == 0) {
        if (anyOtherAlive) {
          //errs() << "  LIVE" << "\n";
          NewUsedArray.insert(V);
          MarkLive(*V);
        }
      } else if (type == 1) {
        if (allOthersAlive) {
          //errs() << "  LIVE" << "\n";
          NewUsedArray.insert(V);
          MarkLive(*V);
        }
      }
    }

    Used = setUsedInitializer(*Used, NewUsedArray);
    MarkLive(*Used);

    //M.eraseNamedMetadata(UsedConditional);
  }

  {
  // Propagate liveness from collected Global Values through the computed
  // dependencies.
  SmallVector<GlobalValue *, 8> NewLiveGVs{AliveGlobals.begin(),
                                           AliveGlobals.end()};
  while (!NewLiveGVs.empty()) {
    GlobalValue *LGV = NewLiveGVs.pop_back_val();
    for (auto *GVD : GVDependencies[LGV])
      MarkLive(*GVD, &NewLiveGVs);
  }
  }

  // Now that all globals which are needed are in the AliveGlobals set, we loop
  // through the program, deleting those which are not alive.
  //

  // The first pass is to drop initializers of global variables which are dead.
  std::vector<GlobalVariable *> DeadGlobalVars; // Keep track of dead globals
  for (GlobalVariable &GV : M.globals())
    if (!AliveGlobals.count(&GV)) {
      DeadGlobalVars.push_back(&GV);         // Keep track of dead globals
      if (GV.hasInitializer()) {
        Constant *Init = GV.getInitializer();
        GV.setInitializer(nullptr);
        if (isSafeToDestroyConstant(Init))
          Init->destroyConstant();
      }
    }

  // The second pass drops the bodies of functions which are dead...
  std::vector<Function *> DeadFunctions;
  for (Function &F : M)
    if (!AliveGlobals.count(&F)) {
      DeadFunctions.push_back(&F);         // Keep track of dead globals
      if (!F.isDeclaration())
        F.deleteBody();
    }

  // The third pass drops targets of aliases which are dead...
  std::vector<GlobalAlias*> DeadAliases;
  for (GlobalAlias &GA : M.aliases())
    if (!AliveGlobals.count(&GA)) {
      DeadAliases.push_back(&GA);
      GA.setAliasee(nullptr);
    }

  // The fourth pass drops targets of ifuncs which are dead...
  std::vector<GlobalIFunc*> DeadIFuncs;
  for (GlobalIFunc &GIF : M.ifuncs())
    if (!AliveGlobals.count(&GIF)) {
      DeadIFuncs.push_back(&GIF);
      GIF.setResolver(nullptr);
    }

  // Now that all interferences have been dropped, delete the actual objects
  // themselves.
  auto EraseUnusedGlobalValue = [&](GlobalValue *GV) {
    LLVM_DEBUG(dbgs() << "Removing global " << GV->getName() << "\n");
    RemoveUnusedGlobalValue(*GV);
    GV->eraseFromParent();
    Changed = true;
  };

  NumFunctions += DeadFunctions.size();
  for (Function *F : DeadFunctions) {
    if (!F->use_empty()) {
      // Virtual functions might still be referenced by one or more vtables,
      // but if we've proven them to be unused then it's safe to replace the
      // virtual function pointers with null, allowing us to remove the
      // function itself.
      ++NumVFuncs;
      F->replaceNonMetadataUsesWith(ConstantPointerNull::get(F->getType()));
      LLVM_DEBUG(dbgs() << "Removing vfunc " << F->getName() << "\n");
    }
    EraseUnusedGlobalValue(F);
  }

  NumVariables += DeadGlobalVars.size();
  for (GlobalVariable *GV : DeadGlobalVars)
    EraseUnusedGlobalValue(GV);

  NumAliases += DeadAliases.size();
  for (GlobalAlias *GA : DeadAliases)
    EraseUnusedGlobalValue(GA);

  NumIFuncs += DeadIFuncs.size();
  for (GlobalIFunc *GIF : DeadIFuncs)
    EraseUnusedGlobalValue(GIF);

  // Make sure that all memory is released
  AliveGlobals.clear();
  ConstantDependenciesCache.clear();
  GVDependencies.clear();
  ComdatMembers.clear();
  TypeIdMap.clear();
  VFESafeVTables.clear();

  Used = M.getGlobalVariable("llvm.used");
  if (Used)
    LLVM_DEBUG(dbgs() << "GlobalDCE done.\nllvm.used = " << *M.getGlobalVariable("llvm.used") << "\n");

  if (Changed)
    return PreservedAnalyses::none();
  return PreservedAnalyses::all();
}

// RemoveUnusedGlobalValue - Loop over all of the uses of the specified
// GlobalValue, looking for the constant pointer ref that may be pointing to it.
// If found, check to see if the constant pointer ref is safe to destroy, and if
// so, nuke it.  This will reduce the reference count on the global value, which
// might make it deader.
//
bool GlobalDCEPass::RemoveUnusedGlobalValue(GlobalValue &GV) {
  if (GV.use_empty())
    return false;
  GV.removeDeadConstantUsers();
  return GV.use_empty();
}
