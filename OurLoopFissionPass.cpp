#include <vector>
#include <unordered_map>
#include <unordered_set>

#include "llvm/Pass.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/LoopInfo.h"

// NOVO - ANALIZA
#include "llvm/Analysis/DependenceAnalysis.h"

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

    // ============================================================
    // NOVO - ANALIZA
    // ============================================================

    void getAnalysisUsage(AnalysisUsage &AU) const override {
        AU.addRequired<DependenceAnalysisWrapperPass>();
    }

    void collectBlocksUntil(BasicBlock *Current, BasicBlock *BlockToStop, Loop *L,
                            unordered_set<BasicBlock *> &Blocks) {
        if (!Current || Current == BlockToStop || !L->contains(Current)) {
            return;
        }

        if (Blocks.find(Current) != Blocks.end()) {
            return;
        }

        Blocks.insert(Current);

        Instruction *Term = Current->getTerminator();

        if (!Term) {
            return;
        }

        for (unsigned i = 0; i < Term->getNumSuccessors(); i++) {
            collectBlocksUntil(Term->getSuccessor(i), BlockToStop, L, Blocks);
        }
    }

    bool instructionInBlocks(Instruction *I, const unordered_set<BasicBlock *> &Blocks) {
        return I && Blocks.find(I->getParent()) != Blocks.end();
    }

    bool hasDependencies(Loop *L, BasicBlock *FirstIf, BasicBlock *LastIf, DependenceInfo &DI) {
        BasicBlock *Latch = L->getLoopLatch();

        if (!Latch) {
            errs() << "[FISSION] Petlja nema latch blok.\n";
            return true;
        }

        unordered_set<BasicBlock *> FirstPartBlocks;
        unordered_set<BasicBlock *> SecondPartBlocks;

        collectBlocksUntil(FirstIf, LastIf, L, FirstPartBlocks);
        collectBlocksUntil(LastIf, Latch, L, SecondPartBlocks);

        errs() << "[ANALIZA] Blokova u prvom delu: " << FirstPartBlocks.size() << "\n";
        errs() << "[ANALIZA] Blokova u drugom delu: " << SecondPartBlocks.size() << "\n";

        vector<Instruction *> FirstMemoryInsts;
        vector<Instruction *> SecondMemoryInsts;
        for (BasicBlock *BB : FirstPartBlocks) {
            for (Instruction &I : *BB) {
                if (isa<LoadInst>(&I) || isa<StoreInst>(&I)) {
                    FirstMemoryInsts.push_back(&I);
                }
                for (User *U : I.users()) {
                    Instruction *UserInst = dyn_cast<Instruction>(U);

                    if (!UserInst) {
                        continue;
                    }
                    if (!instructionInBlocks(UserInst, SecondPartBlocks)) {
                        continue;
                    }
                    if (PHINode *PN = dyn_cast<PHINode>(UserInst)) {
                        if (PN->getParent() == LastIf) {
                            continue;
                        }
                    }
                    errs() << "[FISSION ZABRANJEN] SSA zavisnost izmedju delova petlje.\n";
                    errs() << "  Instrukcija iz prvog dela:\n";
                    errs() << "    " << I << "\n";
                    errs() << "  Koristi se u drugom delu:\n";
                    errs() << "    " << *UserInst << "\n";

                    return true;
                }
            }
        }
        for (BasicBlock *BB : SecondPartBlocks) {
            for (Instruction &I : *BB) {
                if (isa<LoadInst>(&I) || isa<StoreInst>(&I)) {
                    SecondMemoryInsts.push_back(&I);
                }
            }
        }
        for (Instruction *I1 : FirstMemoryInsts) {
            for (Instruction *I2 : SecondMemoryInsts) {
                if (DI.depends(I1, I2, true)) {
                    errs() << "[FISSION ZABRANJEN] Memorijska zavisnost izmedju delova petlje.\n";
                    errs() << "  Prvi deo:\n";
                    errs() << "    " << *I1 << "\n";
                    errs() << "  Drugi deo:\n";
                    errs() << "    " << *I2 << "\n";

                    return true;
                }
                if (DI.depends(I2, I1, true)) {
                    errs() << "[FISSION ZABRANJEN] Memorijska zavisnost izmedju delova petlje.\n";
                    errs() << "  Drugi deo:\n";
                    errs() << "    " << *I2 << "\n";
                    errs() << "  Prvi deo:\n";
                    errs() << "    " << *I1 << "\n";

                    return true;
                }
            }
        }
        BasicBlock *Header = L->getHeader();
        for (Instruction &I : *Header) {
            PHINode *PN = dyn_cast<PHINode>(&I);
            if (!PN) {
                break;
            }
            bool UsedInFirstPart = false;
            bool UsedInSecondPart = false;
            for (User *U : PN->users()) {
                Instruction *UserInst = dyn_cast<Instruction>(U);

                if (!UserInst) {
                    continue;
                }
                if (instructionInBlocks(UserInst, FirstPartBlocks)) {
                    UsedInFirstPart = true;
                }
                if (instructionInBlocks(UserInst, SecondPartBlocks)) {
                    UsedInSecondPart = true;
                }
            }
            if (UsedInFirstPart && UsedInSecondPart) {
                errs() << "[FISSION ZABRANJEN] Ista loop promenljiva koristi se u oba dela petlje:\n";
                errs() << "    " << *PN << "\n";

                return true;
            }
        }
        errs() << "[ANALIZA] Nisu pronadjene zavisnosti koje sprecavaju loop fission.\n";
        return false;
    }
    BasicBlock *findIfBasicBlock(const vector<BasicBlock *> &BBs, bool findFirst) {
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
    void deleteAllBlocksFrom(BasicBlock *Current, BasicBlock *BlockToStop,
                             unordered_set<BasicBlock *> &BlocksToDelete) {
        if (!Current || Current == BlockToStop) {
            return;
        }
        BlocksToDelete.insert(Current);

        Instruction *TI = Current->getTerminator();
        if (!TI) {
            return;
        }
        for (size_t i = 0; i < TI->getNumSuccessors(); i++) {
            BasicBlock *Successor = TI->getSuccessor(i);

            if (BlocksToDelete.find(Successor) == BlocksToDelete.end() && Successor != BlockToStop) {
                deleteAllBlocksFrom(Successor, BlockToStop, BlocksToDelete);
            }
        }
    }
    void safeDeleteBlocks(const unordered_set<BasicBlock *> &BlocksToDelete) {
        for (BasicBlock *BB : BlocksToDelete) {
            if (!BB) {
                continue;
            }
            for (Instruction &I : *BB) {
                I.replaceAllUsesWith(UndefValue::get(I.getType()));
            }
        }
        for (BasicBlock *BB : BlocksToDelete) {
            if (!BB) {
                continue;
            }
            for (BasicBlock *Succ : successors(BB)) {
                if (BlocksToDelete.find(Succ) == BlocksToDelete.end()) {
                    Succ->removePredecessor(BB, true);
                }
            }
        }
        for (BasicBlock *BB : BlocksToDelete) {
            if (!BB) {
                continue;
            }
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
        if (!Exit) {
            return nullptr;
        }
        vector<BasicBlock *> LoopBasicBlocksCopy;
        ValueToValueMapTy VMap;
        IRBuilder<> Builder(Exit->getContext());

        for (BasicBlock *BB : LoopBasicBlocks) {
            BasicBlock *NewBB =
                BasicBlock::Create(Exit->getContext(), BB->getName() + ".fission", Exit->getParent(), Exit);

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
        unordered_set<BasicBlock *> BlocksToDelete;

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
        DependenceInfo &DI = getAnalysis<DependenceAnalysisWrapperPass>().getDI();
        if (hasDependencies(L, FirstIf, LastIf, DI)) {
            errs() << "[FISSION] Petlja se NE razdvaja jer postoje zavisnosti izmedju delova.\n";
            return false;
        }
        errs() << "[FISSION] Petlja moze da se razdvoji.\n";
        loopFission(L);
        BasicBlock *BranchBlock = findIfBasicBlock(LoopBasicBlocks, true);
        if (BranchBlock) {
            BranchInst *FirstBranch = dyn_cast<BranchInst>(BranchBlock->getTerminator());
            if (FirstBranch && FirstBranch->isConditional()) {
                BasicBlock *TrueBB = FirstBranch->getSuccessor(0);
                BasicBlock *NextIfOrJoinBB = FirstBranch->getSuccessor(1);
                BranchInst *TrueBranch = dyn_cast<BranchInst>(TrueBB->getTerminator());

                unordered_set<BasicBlock *> BlocksToDelete;

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
