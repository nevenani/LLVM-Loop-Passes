#include <vector>
#include <unordered_map>
#include <unordered_set>
#include "llvm/Pass.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Support/Casting.h"
#include "llvm/IR/Constants.h"
#include "llvm/Support/raw_ostream.h"

using namespace std;
using namespace llvm;

namespace {
struct OurLoopFissionPass : public LoopPass {
  static char ID;
  OurLoopFissionPass() : LoopPass(ID) {}

  vector<BasicBlock *> LoopBasicBlocks;

  BasicBlock *findIfBasicBlock(const vector<BasicBlock*> &BBs, bool findFirst) {
    BasicBlock *LastBranchBlock = nullptr;
    for (size_t i = 1; i < BBs.size(); i++) {
      for (Instruction &I : *BBs[i]) {
        if (isa<ICmpInst>(&I)) {
          if (findFirst) return BBs[i];
          LastBranchBlock = BBs[i];
        }
      }
    }
    return LastBranchBlock;
  }

  void deleteAllBlocksFrom(BasicBlock *Current, BasicBlock *BlockToStop,
                           unordered_set<BasicBlock*> &BlocksToDelete) {
    if (!Current || Current == BlockToStop) return;
    BlocksToDelete.insert(Current);

    Instruction *TI = Current->getTerminator();
    if (!TI) return;

    for (size_t i = 0; i < TI->getNumSuccessors(); i++) {
      BasicBlock *Successor = TI->getSuccessor(i);
      if (BlocksToDelete.find(Successor) == BlocksToDelete.end() && Successor != BlockToStop) {
        deleteAllBlocksFrom(Successor, BlockToStop, BlocksToDelete);
      }
    }
  }

  void safeDeleteBlocks(const unordered_set<BasicBlock*> &BlocksToDelete) {
    for (BasicBlock *BB : BlocksToDelete) {
      if (!BB) continue;
      for (Instruction &I : *BB) {
        I.replaceAllUsesWith(UndefValue::get(I.getType()));
      }
    }

    for (BasicBlock *BB : BlocksToDelete) {
      if (!BB) continue;
      for (BasicBlock *Succ : successors(BB)) {
        if (BlocksToDelete.find(Succ) == BlocksToDelete.end()) {
          Succ->removePredecessor(BB, true);
        }
      }
    }

    for (BasicBlock *BB : BlocksToDelete) {
      if (!BB) continue;
      BB->dropAllReferences();
    }

    for (BasicBlock *BB : BlocksToDelete) {
      if (BB && BB->getParent()) {
        BB->eraseFromParent();
      }
    }
  }

  BasicBlock *copyLoop(Loop *L) {
    BasicBlock *Exit = L->getExitBlock();
    if (!Exit) return nullptr;

    vector<BasicBlock*> LoopBasicBlocksCopy;
    ValueToValueMapTy VMap;
    IRBuilder<> Builder(Exit->getContext());

    for (BasicBlock *BB : LoopBasicBlocks) {
      BasicBlock *NewBB = BasicBlock::Create(Exit->getContext(), BB->getName() + ".fission", Exit->getParent(), Exit);
      LoopBasicBlocksCopy.push_back(NewBB);
      VMap[BB] = NewBB;
    }

    for (size_t i = 0; i < LoopBasicBlocks.size(); i++) {
      BasicBlock *OldBB = LoopBasicBlocks[i];
      BasicBlock *NewBB = LoopBasicBlocksCopy[i];
      Builder.SetInsertPoint(NewBB);

      for (Instruction &I : *OldBB) {
        Instruction *NewInst = I.clone();
        Builder.Insert(NewInst);
        VMap[&I] = NewInst;
      }
    }

    for (BasicBlock *BB : LoopBasicBlocksCopy) {
      for (Instruction &I : *BB) {
        RemapInstruction(&I, VMap, RF_NoModuleLevelChanges | RF_IgnoreMissingLocals);
      }
    }

    unordered_set<BasicBlock*> BlocksToDelete;
    BasicBlock *BlockToStart = findIfBasicBlock(LoopBasicBlocksCopy, true);
    BasicBlock *BlockToStop = findIfBasicBlock(LoopBasicBlocksCopy, false);

    if (BlockToStart && BlockToStop) {
      deleteAllBlocksFrom(BlockToStart, BlockToStop, BlocksToDelete);

      Instruction *HeaderTerm = LoopBasicBlocksCopy.front()->getTerminator();
      if (HeaderTerm && HeaderTerm->getNumSuccessors() > 0) {
        HeaderTerm->setSuccessor(0, BlockToStop);
      }

      safeDeleteBlocks(BlocksToDelete);
    }

    return LoopBasicBlocksCopy.front();
  }

  void loopFission(Loop *L) {
    BasicBlock *LoopCopy = copyLoop(L);
    if (LoopCopy && !LoopBasicBlocks.empty()) {
      Instruction *Term = LoopBasicBlocks.front()->getTerminator();
      if (Term && Term->getNumSuccessors() > 1) {
        Term->setSuccessor(1, LoopCopy);
      }
    }
  }

  bool runOnLoop(Loop *L, LPPassManager &LPM) override {
    errs() << "Procesiram petlju: " << L->getHeader()->getName() << "\n";
    LoopBasicBlocks = L->getBlocksVector();

    BasicBlock *FirstIf = findIfBasicBlock(LoopBasicBlocks, true);
    BasicBlock *LastIf = findIfBasicBlock(LoopBasicBlocks, false);
    if (!FirstIf || !LastIf || FirstIf == LastIf) {
      return false;
    }

    loopFission(L);

    BasicBlock *BranchBlock = findIfBasicBlock(LoopBasicBlocks, true);
    if (BranchBlock) {
      BranchInst *FirstBranch = dyn_cast<BranchInst>(BranchBlock->getTerminator());

      if (FirstBranch && FirstBranch->isConditional()) {
        BasicBlock *TrueBB = FirstBranch->getSuccessor(0);
        BasicBlock *NextIfOrJoinBB = FirstBranch->getSuccessor(1);

        BranchInst *TrueBranch = dyn_cast<BranchInst>(TrueBB->getTerminator());
        unordered_set<BasicBlock*> BlocksToDelete;

        deleteAllBlocksFrom(NextIfOrJoinBB, L->getLoopLatch(), BlocksToDelete);
        
        if (FirstBranch->getNumSuccessors() > 1) {
          FirstBranch->setSuccessor(1, L->getLoopLatch());
        }
        if (TrueBranch && TrueBranch->getNumSuccessors() > 0) {
          TrueBranch->setSuccessor(0, L->getLoopLatch());
        }

        safeDeleteBlocks(BlocksToDelete);
      }
    }

    return true;
  }
};
}

char OurLoopFissionPass::ID = 0;
static RegisterPass<OurLoopFissionPass> X("Our-Loop-Fission-pass", "Our Loop Fission Pass");