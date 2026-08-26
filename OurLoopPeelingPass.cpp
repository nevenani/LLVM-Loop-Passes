#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Pass.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Transforms/Utils/Cloning.h"

#include <unordered_map>
#include <vector>

using namespace llvm;

namespace {

struct OurLoopPeelingPass : public LoopPass {
    std::unordered_map<Value *, Value *> VariablesMap;
    std::vector<BasicBlock *> LoopBasicBlocks;
    Value *LoopCounter, *LoopBound;

    static char ID;
    OurLoopPeelingPass() : LoopPass(ID) {}

    void mapVariables(Loop *L) {
        for (BasicBlock &BB : *L->getLoopPreheader()->getParent()) {
            for (Instruction &I : BB) {
                if (isa<LoadInst>(&I)) {
                VariablesMap[&I] = I.getOperand(0);
                }
            }
        }
    }

    void findLoopCounterAndBound(Loop *L) {
        for(Instruction &I : *L->getHeader()){
            if(isa<ICmpInst>(&I)){
                LoopCounter = VariablesMap[I.getOperand(0)];
                LoopBound = VariablesMap[I.getOperand(1)];
                break;
            }
        }
    }

    BasicBlock *findCompareBlock() {
        for (size_t i = 1; i < LoopBasicBlocks.size(); i++) {
            for (Instruction &I : *LoopBasicBlocks[i]) {
                if (isa<ICmpInst>(&I)) {
                    return LoopBasicBlocks[i];
                }
            }
        }

        return nullptr;
    }

    unsigned getPeelingCount() {
        BasicBlock *CompareBlock = findCompareBlock();
        if (CompareBlock == nullptr) {
            return 0;
        }

        for (Instruction &I : *CompareBlock) {
            if (auto *Cmp = dyn_cast<ICmpInst>(&I)) {
                Value *Op0 = Cmp->getOperand(0);
                Value *Op1 = Cmp->getOperand(1);

                Value *Var1 = VariablesMap.count(Op0) ? VariablesMap[Op0] : Op0;
                Value *Var2 = VariablesMap.count(Op1) ? VariablesMap[Op1] : Op1;

                if (Var1 == LoopCounter) {
                    if (auto *CI = dyn_cast<ConstantInt>(Op1)) {
                        return (unsigned)CI->getZExtValue();
                    }
                }

                if (Var2 == LoopCounter) {
                    if (auto *CI = dyn_cast<ConstantInt>(Op0)) {
                        return (unsigned)CI->getZExtValue();
                    }
                }
            }
        }
        return 0;
    }

    BasicBlock *copyBasicBlock(BasicBlock *OriginalBlock) {
        Instruction *Clone;
        std::unordered_map<Value *, Value *> Mapping;
        IRBuilder<> Builder(OriginalBlock);

        BasicBlock *NewBlock = BasicBlock::Create(OriginalBlock->getContext(), "",
        OriginalBlock->getParent(), LoopBasicBlocks.front());

        Builder.SetInsertPoint(NewBlock);

        for (Instruction &I : *OriginalBlock) {
            Clone = I.clone();
            Mapping[&I] = Clone;
            Builder.Insert(Clone);

            for (size_t i = 0; i < Clone->getNumOperands(); i++) {
                if (Mapping[Clone->getOperand(i)]) {
                Clone->setOperand(i, Mapping[Clone->getOperand(i)]);
                }
            }
        }

        return NewBlock;
    }

    BasicBlock *copyBasicBlockWithConstant(BasicBlock *OriginalBlock, Value *LoopCounterVar, int ConstantVal, BasicBlock *InsertBeforeBB) {
        Instruction *Clone;
        std::unordered_map<Value *, Value *> Mapping;
        LLVMContext &Ctx = OriginalBlock->getContext();
        IRBuilder<> Builder(OriginalBlock);

        BasicBlock *NewBlock = BasicBlock::Create(Ctx, "", OriginalBlock->getParent(), InsertBeforeBB);
        Builder.SetInsertPoint(NewBlock);

        ConstantInt *CVal = ConstantInt::get(Type::getInt32Ty(Ctx), ConstantVal);

        for (Instruction &I : *OriginalBlock) {

            if (auto *LI = dyn_cast<LoadInst>(&I)) {
                    Value *LoadedPtr = LI->getOperand(0);
                    
                    if (LoadedPtr == LoopCounterVar || VariablesMap[LI] == LoopCounterVar) {
                        Mapping[&I] = CVal;
                        continue;
                    }
                
            }

            if (isa<ICmpInst>(&I)) {
                Mapping[&I] = ConstantInt::getTrue(Ctx);
                continue;
            }

            Clone = I.clone();
            Mapping[&I] = Clone;
            Builder.Insert(Clone);

            for (size_t i = 0; i < Clone->getNumOperands(); i++) {
                Value *Op = Clone->getOperand(i);
                if (Mapping[Op]) {
                Clone->setOperand(i, Mapping[Op]);
                }
            }
        }

        return NewBlock;
    }



    void peeling(Loop *L) {
        BasicBlock *CompareBlock = findCompareBlock();

        unsigned PeelingCount = getPeelingCount();

        if(PeelingCount == 0 || CompareBlock == nullptr)
            return;

        BasicBlock *Preheader = L->getLoopPreheader();
        BasicBlock *Header = L->getHeader();
        if (!Preheader || !Header) return;

        BasicBlock *ThenBlock = nullptr;
        if (auto *BI = dyn_cast<BranchInst>(CompareBlock->getTerminator())) {
            if (BI->isConditional()) {
                ThenBlock = BI->getSuccessor(0); 
            }
        }

        if (!ThenBlock) return;

        BasicBlock *LastPredecessor = Preheader;
        BasicBlock *FirstPeeled = nullptr;

        std::vector<BasicBlock *> PeeledBlocks;

        for (unsigned i = 0; i < PeelingCount; ++i) {
           
            BasicBlock *PeeledThen = copyBasicBlockWithConstant(ThenBlock, LoopCounter, i, Header);

            Instruction *OldTerm = PeeledThen->getTerminator();
            if (OldTerm) {
                OldTerm->eraseFromParent();
            }

            if (i == 0) {
                FirstPeeled = PeeledThen; 
            } else {
                
                Instruction *PrevTerm = LastPredecessor->getTerminator();
                if (PrevTerm) PrevTerm->eraseFromParent();
                BranchInst::Create(PeeledThen, LastPredecessor);
            }

            PeeledBlocks.push_back(PeeledThen);
            LastPredecessor = PeeledThen;
        }

        
        Instruction *PreheaderTerm = Preheader->getTerminator();
        if (PreheaderTerm) PreheaderTerm->eraseFromParent();
        BranchInst::Create(FirstPeeled, Preheader);

        
        if (!PeeledBlocks.empty()) {
            BranchInst::Create(Header, PeeledBlocks.back());
        }

    }
  

    bool runOnLoop(Loop *L, LPPassManager &LPM) override {
        mapVariables(L);
        LoopBasicBlocks = L->getBlocks();
        findLoopCounterAndBound(L);


        peeling(L);

        
        return true;
    }
};
}

char OurLoopPeelingPass::ID = 0;
static RegisterPass<OurLoopPeelingPass> X("Our-Loop-Peeling-pass", "Loop Peeling Pass");