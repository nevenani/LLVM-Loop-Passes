#include <vector>
#include <unordered_map>
#include <unordered_set>

#include "llvm/Pass.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Analysis/InstructionSimplify.h"

#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Constants.h"

#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/Transforms/Utils/Local.h"

#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"

using namespace std;
using namespace llvm;

namespace {

struct OurLoopFissionPass : public LoopPass {
  static char ID;

  OurLoopFissionPass() : LoopPass(ID) {}

  vector<BasicBlock *> LoopBasicBlocks;

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<LoopInfoWrapperPass>();
    AU.addRequired<DependenceAnalysisWrapperPass>();

    // NE stavljamo AU.setPreservesCFG(),
    // jer pass menja CFG.
  }

  BasicBlock *findIfBasicBlock(
      const vector<BasicBlock *> &BBs,
      bool findFirst) {

    BasicBlock *LastBranchBlock = nullptr;

    for (size_t i = 1; i < BBs.size(); i++) {
      for (Instruction &I : *BBs[i]) {

        if (isa<ICmpInst>(&I)) {
          if (findFirst) {
            return BBs[i];
          }

          LastBranchBlock = BBs[i];
        }
      }
    }

    return LastBranchBlock;
  }

  bool hasDependencies(
      Loop *L,
      DependenceInfo &DI) {

    vector<Instruction *> MemoryInsts;
    vector<Instruction *> FirstPartInsts;
    vector<Instruction *> SecondPartInsts;

    BasicBlock *FirstIf =
        findIfBasicBlock(LoopBasicBlocks, true);

    if (!FirstIf) {
      return true;
    }

    bool inFirstPart = true;

    for (BasicBlock *BB : LoopBasicBlocks) {

      if (BB == FirstIf) {
        inFirstPart = false;
      }

      for (Instruction &I : *BB) {

        if (isa<LoadInst>(&I) ||
            isa<StoreInst>(&I)) {

          MemoryInsts.push_back(&I);
        }

        if (isa<PHINode>(&I)) {
          continue;
        }

        if (inFirstPart) {
          FirstPartInsts.push_back(&I);
        } else {
          SecondPartInsts.push_back(&I);
        }
      }
    }

    //
    // Memorijske zavisnosti
    //
    for (size_t i = 0;
         i < MemoryInsts.size();
         i++) {

      for (size_t j = i + 1;
           j < MemoryInsts.size();
           j++) {

        Instruction *InstA =
            MemoryInsts[i];

        Instruction *InstB =
            MemoryInsts[j];

        if (DI.depends(
                InstA,
                InstB,
                true)) {

          errs()
              << " [FISSION ZABRANJEN] "
              << "Detektovana memorijska zavisnost izmedju:\n";

          errs()
              << "   " << *InstA
              << "\n";

          errs()
              << "   " << *InstB
              << "\n";

          return true;
        }
      }
    }

    //
    // SSA zavisnosti
    //
    for (Instruction *I1 :
         FirstPartInsts) {

      for (User *U :
           I1->users()) {

        Instruction *UI =
            dyn_cast<Instruction>(U);

        if (!UI) {
          continue;
        }

        for (Instruction *I2 :
             SecondPartInsts) {

          if (UI == I2) {

            errs()
                << " [FISSION ZABRANJEN] "
                << "Instrukcija u drugom delu "
                << "koristi vrednost iz prvog dela:\n";

            errs()
                << "   " << *I2
                << "\n";

            return true;
          }
        }
      }
    }

    return false;
  }

  void deleteAllBlocksFrom(
      BasicBlock *Current,
      BasicBlock *BlockToStop,
      unordered_set<BasicBlock *> &BlocksToDelete) {

    if (!Current ||
        Current == BlockToStop) {
      return;
    }

    if (BlocksToDelete.find(Current) !=
        BlocksToDelete.end()) {
      return;
    }

    BlocksToDelete.insert(Current);

    Instruction *TI =
        Current->getTerminator();

    if (!TI) {
      return;
    }

    for (unsigned i = 0;
         i < TI->getNumSuccessors();
         i++) {

      BasicBlock *Successor =
          TI->getSuccessor(i);

      if (Successor ==
          BlockToStop) {
        continue;
      }

      deleteAllBlocksFrom(
          Successor,
          BlockToStop,
          BlocksToDelete);
    }
  }

  void unlinkAndDeleteBlocks(
      const unordered_set<BasicBlock *> &BlocksToDelete) {

    //
    // Prvo uklanjamo predecessor veze
    //
    for (BasicBlock *BB :
         BlocksToDelete) {

      if (!BB ||
          !BB->getParent()) {
        continue;
      }

      vector<BasicBlock *> Successors;

      for (BasicBlock *Succ :
           successors(BB)) {

        Successors.push_back(Succ);
      }

      for (BasicBlock *Succ :
           Successors) {

        if (BlocksToDelete.find(Succ) ==
            BlocksToDelete.end()) {

          Succ->removePredecessor(
              BB,
              true);
        }
      }
    }

    //
    // Zatim skidamo reference
    //
    for (BasicBlock *BB :
         BlocksToDelete) {

      if (BB &&
          BB->getParent()) {

        BB->dropAllReferences();
      }
    }

    //
    // Na kraju brisemo blokove
    //
    for (BasicBlock *BB :
         BlocksToDelete) {

      if (BB &&
          BB->getParent()) {

        BB->eraseFromParent();
      }
    }
  }

  void cleanupFunctionPhis(
      Function *F) {

    const DataLayout &DL =
        F->getParent()->getDataLayout();

    //
    // Uklanjanje PHI incoming vrednosti
    // koje vise nemaju predecessor.
    //
    for (BasicBlock &BB :
         *F) {

      unordered_set<BasicBlock *> RealPreds(
          pred_begin(&BB),
          pred_end(&BB));

      for (Instruction &I :
           BB) {

        PHINode *PN =
            dyn_cast<PHINode>(&I);

        if (!PN) {
          continue;
        }

        for (int i =
                 static_cast<int>(
                     PN->getNumIncomingValues()) - 1;
             i >= 0;
             i--) {

          BasicBlock *Incoming =
              PN->getIncomingBlock(i);

          if (RealPreds.find(Incoming) ==
              RealPreds.end()) {

            PN->removeIncomingValue(
                i,
                false);
          }
        }
      }
    }

    //
    // Pojednostavljivanje PHI cvorova
    //
    bool Changed = true;

    while (Changed) {

      Changed = false;

      for (BasicBlock &BB :
           *F) {

        for (auto It = BB.begin();
             It != BB.end();) {

          Instruction &I =
              *It++;

          PHINode *PN =
              dyn_cast<PHINode>(&I);

          if (!PN) {
            continue;
          }

          if (PN->getNumIncomingValues() ==
              0) {

            PN->replaceAllUsesWith(
                UndefValue::get(
                    PN->getType()));

            PN->eraseFromParent();

            Changed = true;

            continue;
          }

          SimplifyQuery SQ(
              DL,
              PN);

          Value *V =
              SimplifyInstruction(
                  PN,
                  SQ);

          if (V &&
              V != PN) {

            PN->replaceAllUsesWith(V);
            PN->eraseFromParent();

            Changed = true;
          }
        }
      }
    }
  }

  BasicBlock *copyLoop(
      Loop *L) {

    BasicBlock *Exit =
        L->getExitBlock();

    BasicBlock *Preheader =
        L->getLoopPreheader();

    BasicBlock *Header =
        L->getHeader();

    if (!Header) {
      return nullptr;
    }

    vector<BasicBlock *>
        LoopBasicBlocksCopy;

    ValueToValueMapTy VMap;

    IRBuilder<> Builder(
        Header->getContext());

    //
    // Kreiranje kopija basic blokova
    //
    for (BasicBlock *BB :
         LoopBasicBlocks) {

      BasicBlock *NewBB =
          BasicBlock::Create(
              Header->getContext(),
              BB->getName() +
                  ".fission",
              Header->getParent(),
              Exit);

      LoopBasicBlocksCopy.push_back(
          NewBB);

      VMap[BB] =
          NewBB;
    }

    //
    // Kloniranje instrukcija
    //
    for (size_t i = 0;
         i < LoopBasicBlocks.size();
         i++) {

      BasicBlock *OldBB =
          LoopBasicBlocks[i];

      BasicBlock *NewBB =
          LoopBasicBlocksCopy[i];

      Builder.SetInsertPoint(
          NewBB);

      for (Instruction &I :
           *OldBB) {

        Instruction *NewInst =
            I.clone();

        Builder.Insert(
            NewInst);

        VMap[&I] =
            NewInst;
      }
    }

    //
    // Remap operand-a i successor-a
    //
    for (BasicBlock *BB :
         LoopBasicBlocksCopy) {

      for (Instruction &I :
           *BB) {

        RemapInstruction(
            &I,
            VMap,
            RF_NoModuleLevelChanges |
                RF_IgnoreMissingLocals);
      }
    }

    //
    // Ciscenje PHI cvorova
    //
    for (BasicBlock *NewBB :
         LoopBasicBlocksCopy) {

      for (Instruction &I :
           *NewBB) {

        PHINode *PN =
            dyn_cast<PHINode>(&I);

        if (!PN) {
          continue;
        }

        for (int i =
                 static_cast<int>(
                     PN->getNumIncomingValues()) - 1;
             i >= 0;
             i--) {

          BasicBlock *IncB =
              PN->getIncomingBlock(i);

          bool Valid = false;

          for (BasicBlock *NB :
               LoopBasicBlocksCopy) {

            if (IncB == NB) {
              Valid = true;
              break;
            }
          }

          if (Preheader &&
              IncB == Preheader) {

            Valid = true;
          }

          if (!Valid) {

            PN->removeIncomingValue(
                i,
                false);
          }
        }
      }
    }

    if (LoopBasicBlocksCopy.empty()) {
      return nullptr;
    }

    return LoopBasicBlocksCopy.front();
  }

  void loopFission(
      Loop *L) {

    BasicBlock *LoopCopy =
        copyLoop(L);

    if (!LoopCopy ||
        LoopBasicBlocks.empty()) {
      return;
    }

    Instruction *Term =
        LoopBasicBlocks.front()
            ->getTerminator();

    if (!Term) {
      return;
    }

    if (Term->getNumSuccessors() >
        1) {

      Term->setSuccessor(
          1,
          LoopCopy);
    }
  }

  bool runOnLoop(
      Loop *L,
      LPPassManager &LPM) override {

    errs()
        << "Procesiram petlju: "
        << L->getHeader()->getName()
        << "\n";

    //
    // OVO je ispravna linija.
    //
    LoopBasicBlocks =
        L->getBlocksVector();

    if (LoopBasicBlocks.empty()) {
      return false;
    }

    BasicBlock *FirstIf =
        findIfBasicBlock(
            LoopBasicBlocks,
            true);

    BasicBlock *LastIf =
        findIfBasicBlock(
            LoopBasicBlocks,
            false);

    if (!FirstIf ||
        !LastIf ||
        FirstIf == LastIf) {

      errs()
          << "Nema najmanje dva if-a "
          << "u petlji - fission se ne radi.\n";

      return false;
    }

    DependenceInfo &DI =
        getAnalysis<
            DependenceAnalysisWrapperPass>()
            .getDI();

    if (hasDependencies(
            L,
            DI)) {

      errs()
          << "Petlja se NE MOZE razdvojiti "
          << "zbog postojanja zavisnosti "
          << "podataka!\n";

      return false;
    }

    errs()
        << "Nema zabranjujucih zavisnosti. "
        << "Pokrecem loop fission.\n";

    loopFission(L);

    BasicBlock *BranchBlock =
        findIfBasicBlock(
            LoopBasicBlocks,
            true);

    if (BranchBlock) {

      BranchInst *FirstBranch =
          dyn_cast<BranchInst>(
              BranchBlock
                  ->getTerminator());

      if (FirstBranch &&
          FirstBranch->isConditional()) {

        BasicBlock *TrueBB =
            FirstBranch
                ->getSuccessor(0);

        BasicBlock *NextIfOrJoinBB =
            FirstBranch
                ->getSuccessor(1);

        BranchInst *TrueBranch =
            dyn_cast<BranchInst>(
                TrueBB
                    ->getTerminator());

        unordered_set<
            BasicBlock *>
            BlocksToDelete;

        BasicBlock *Latch =
            L->getLoopLatch();

        if (Latch) {

          deleteAllBlocksFrom(
              NextIfOrJoinBB,
              Latch,
              BlocksToDelete);

          if (FirstBranch
                  ->getNumSuccessors() >
              1) {

            FirstBranch
                ->setSuccessor(
                    1,
                    Latch);
          }

          if (TrueBranch &&
              TrueBranch
                      ->getNumSuccessors() >
                  0) {

            TrueBranch
                ->setSuccessor(
                    0,
                    Latch);
          }

          //
          // Ne dozvoljavamo slucajno
          // brisanje latch-a.
          //
          BlocksToDelete.erase(
              Latch);

          unlinkAndDeleteBlocks(
              BlocksToDelete);
        }
      }
    }

    Function *F =
        L->getHeader()
            ->getParent();

    removeUnreachableBlocks(
        *F);

    cleanupFunctionPhis(
        F);

    removeUnreachableBlocks(
        *F);

    errs()
        << "Loop fission zavrsen.\n";

    return true;
  }
};

} // namespace

char OurLoopFissionPass::ID = 0;

static RegisterPass<OurLoopFissionPass> X(
    "Our-Loop-Fission-pass",
    "Our Loop Fission Pass",
    false,
    false);
