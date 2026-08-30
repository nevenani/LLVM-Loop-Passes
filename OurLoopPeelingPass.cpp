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
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

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

                if (Var1 == LoopCounter || Var2 == LoopCounter) {
                    ConstantInt *CI = dyn_cast<ConstantInt>(Var1 == LoopCounter ? Op1 : Op0);
                    if (CI) {
                        
                        if (Cmp->getPredicate() == ICmpInst::ICMP_EQ) {
                            return 1; 
                        }
                        
                        if (Cmp->getPredicate() == ICmpInst::ICMP_SLT || Cmp->getPredicate() == ICmpInst::ICMP_SLE) {
                            return (unsigned)CI->getZExtValue() + 1;
                        }
                    }
                }
            }
        }
        return 0;
    }


    BasicBlock *copyBasicBlockWithConstant(BasicBlock *OriginalBlock, int ConstantVal, BasicBlock *InsertBeforeBB) {
        Instruction *Clone;
        std::unordered_map<Value *, Value *> Mapping;
        LLVMContext &Ctx = OriginalBlock->getContext();

        BasicBlock *NewBlock = BasicBlock::Create(Ctx, "", OriginalBlock->getParent(), InsertBeforeBB);
        IRBuilder<> Builder(NewBlock);
        Builder.SetInsertPoint(NewBlock);

        ConstantInt *CVal = ConstantInt::get(Type::getInt32Ty(Ctx), ConstantVal);

        for (Instruction &I : *OriginalBlock) {

            if (auto *LI = dyn_cast<LoadInst>(&I)) {
                    Value *LoadedPtr = LI->getOperand(0);
                    
                    if (LoadedPtr == LoopCounter || VariablesMap[LI] == LoopCounter) {
                        Mapping[&I] = CVal;
                        continue;
                    }
                
            }

            if (isa<ICmpInst>(&I) || isa<BranchInst>(&I)) {
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

        if (PeelingCount == 0 || CompareBlock == nullptr || !LoopCounter)
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

        std::vector<BasicBlock *> PeeledBlocks;

        
        for (unsigned i = 0; i < PeelingCount; ++i) {
            BasicBlock *PeeledThen = copyBasicBlockWithConstant(ThenBlock, i, Header);
            PeeledBlocks.push_back(PeeledThen);
        }


        Instruction *PreheaderTerm = Preheader->getTerminator();
        if (PreheaderTerm) PreheaderTerm->eraseFromParent();
        BranchInst::Create(PeeledBlocks[0], Preheader);

 
        for (size_t i = 0; i < PeeledBlocks.size(); ++i) {
            IRBuilder<> B(PeeledBlocks[i]);
            if (i + 1 < PeeledBlocks.size()) {
                B.CreateBr(PeeledBlocks[i + 1]);
            } else {
                B.CreateStore(ConstantInt::get(Type::getInt32Ty(Header->getContext()), PeelingCount), LoopCounter);
                B.CreateBr(Header);
            }
        }

    }
  

    bool runOnLoop(Loop *L, LPPassManager &LPM) override {
        mapVariables(L);
        LoopBasicBlocks = L->getBlocks();
        findLoopCounterAndBound(L);

        unsigned PeelingCount = getPeelingCount();
        if (PeelingCount == 0 || !LoopBound)
            return false;

        int64_t LoopIterations = -1;

        
        if (ConstantInt *BoundCI = dyn_cast<ConstantInt>(LoopBound)) {
            LoopIterations = BoundCI->getZExtValue();
        } 
        
        else {
            Value *Ptr = LoopBound;
            Function *F = L->getHeader()->getParent();
            
            for (BasicBlock &BB : *F) {
                for (Instruction &I : BB) {
                    if (StoreInst *SI = dyn_cast<StoreInst>(&I)) {
                        if (SI->getPointerOperand() == Ptr) {
                            if (ConstantInt *CI = dyn_cast<ConstantInt>(SI->getValueOperand())) {
                                LoopIterations = CI->getZExtValue();
                                break;
                            }
                        }
                    }
                }
                if (LoopIterations != -1) break;
            }
        }

        
        if (LoopIterations != -1 && (unsigned)LoopIterations < PeelingCount) {
            return false;
        }

        peeling(L);

        
        return true;
    }
};
}

char OurLoopPeelingPass::ID = 0;
static RegisterPass<OurLoopPeelingPass> X("Our-Loop-Peeling-pass", "Loop Peeling Pass");
