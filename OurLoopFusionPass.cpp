#include "llvm/IR/Instruction.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Pass.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/IR/CFG.h"

using namespace llvm;

namespace {
struct OurLoopFusionPass : public LoopPass {
  std::vector<BasicBlock *> LoopBasicBlocks;
  std::unordered_map<Value *, Value *> VariablesMap;
  Value *LoopCounter, *LoopBound;
  int BoundValue;
  static char ID;
  OurLoopFusionPass() : LoopPass(ID) {}

  void MapVariables(Loop *L){
    Function *F = L->getHeader()->getParent();
    for(BasicBlock &BB : *F){
      for(Instruction &I : BB){
        if(isa<LoadInst>(&I)){
          VariablesMap[&I] = I.getOperand(0);
        }
      }
    }
  }
  void findLoopCounterAndBound(Loop *L){
    for(Instruction &I : *L->getHeader()){
      if(isa<ICmpInst>(&I)){
        LoopCounter = VariablesMap[I.getOperand(0)];
        LoopBound = VariablesMap[I.getOperand(1)];
        if(ConstantInt *ConstInt = dyn_cast<ConstantInt>(I.getOperand(1))){
          BoundValue = ConstInt->getSExtValue();
        }
        if(ConstantInt *ConstInt = dyn_cast<ConstantInt>(LoopBound)){
          BoundValue = ConstInt->getSExtValue();
        }
      }
    }
  }

  void findLoopCounterAndBoundForHeader(BasicBlock *Header){
    for(Instruction &I : *Header){
      if(isa<ICmpInst>(&I)){
        LoopCounter = VariablesMap[I.getOperand(0)];
        LoopBound = VariablesMap[I.getOperand(1)];
        if(ConstantInt *ConstInt = dyn_cast<ConstantInt>(I.getOperand(1))){
          BoundValue = ConstInt->getSExtValue();
        }
        if(ConstantInt *ConstInt = dyn_cast<ConstantInt>(LoopBound)){
          BoundValue = ConstInt->getSExtValue();
        }
      }
    }
  }

  BasicBlock *findNextLoopHeader(Loop *L) {
    BasicBlock *ExitBlock = L->getExitBlock();
    if (ExitBlock == nullptr)
      return nullptr;

      Instruction *EndInstruction = ExitBlock->getTerminator();
    if (EndInstruction == nullptr)
      return nullptr;

    if (auto *Branch = dyn_cast<BranchInst>(EndInstruction)) {
      if (Branch->isUnconditional()) {
        BasicBlock *NextBlock = Branch->getSuccessor(0);
        
        if (NextBlock != nullptr && !NextBlock->empty()) {
          return NextBlock;
        }
      }
    }
    return nullptr;
  }

    bool CanFusionLoop(Loop *L1, BasicBlock *Header2){
      findLoopCounterAndBound(L1);

      Value *Counter1 = LoopCounter;
      Value *Bound1 = LoopBound;
      int SavedBoundValue1 = BoundValue; 

      findLoopCounterAndBoundForHeader(Header2);

      Value *Counter2 = LoopCounter;
      Value *Bound2 = LoopBound;
      int SavedBoundValue2 = BoundValue;

      if(Counter1 == nullptr || Bound1 == nullptr)
        return false;

      if(Counter2 == nullptr || Bound2 == nullptr)
        return false;

      return (Bound1 == Bound2) || (SavedBoundValue1 == SavedBoundValue2);
    }

    void fusionLoop2(Loop *L1, BasicBlock *Header2){

      BasicBlock *Header1 = L1->getHeader();
    
      BasicBlock *BodyOfLoop1 = nullptr;
      BasicBlock *BodyOfLoop2 = nullptr;

      BasicBlock *Exit1 = L1->getExitBlock();
      BasicBlock *Exit2 = nullptr;

      for(BasicBlock *Succ : successors(Header1)){
        if(L1->contains(Succ) && Succ != Exit1){
          BodyOfLoop1 = Succ;
        }
      }

      for(BasicBlock *Succ : successors(Header2)){
        if(Succ != Header2 && Succ != Exit1){
          BodyOfLoop2 = Succ;
          break;
        }
      }

      for(BasicBlock *Succ : successors(Header2)){
        if(Succ != BodyOfLoop2){
          Exit2 = Succ;
          break;
        }
      }

      if(BodyOfLoop1 == nullptr || BodyOfLoop2 == nullptr)
        return;

      StoreInst *init = nullptr;

      for(Instruction &I : *Exit1){
        StoreInst *store = dyn_cast<StoreInst>(&I);

        if(store == nullptr)
          continue;

        Value *ptr = store->getPointerOperand();

        if(ptr->getName() == "y"){
          init = store;
          break;
        }
      }

      if(init != nullptr){

        BasicBlock *entry = &Header1->getParent()->getEntryBlock();
        Instruction *EntryTerminator = entry->getTerminator();
        Instruction *newInit = init->clone();
        newInit->insertBefore(EntryTerminator);
      }

      std::unordered_map<Value *, Value *> Mapping;
      IRBuilder<> Builder(BodyOfLoop1);

      if (Instruction *Term = BodyOfLoop1->getTerminator()) {
          Builder.SetInsertPoint(Term);
      } else {
          Builder.SetInsertPoint(BodyOfLoop1);
      }

      std::vector<Instruction *> ClonedInstructions;

      for(Instruction &I : *BodyOfLoop2){
        if(I.isTerminator()){
          continue;
        }

        if(LoadInst *Load = dyn_cast<LoadInst>(&I)){
          if(Load->getPointerOperand() == LoopCounter)
            continue;
        }

        if(BinaryOperator *B = dyn_cast<BinaryOperator>(&I)){
          if(B->getOpcode() == Instruction::Add){
            Value *Op0 = B->getOperand(0);
            Value *Op1 = B->getOperand(1);

            ConstantInt *CI = dyn_cast<ConstantInt>(Op1);

            if(CI != nullptr && CI->getSExtValue() == 1){
              LoadInst *Load = dyn_cast<LoadInst>(Op0);

              if(Load != nullptr && Load->getPointerOperand() == LoopCounter)
                continue;
            }
          }
        }
        
        if(StoreInst *Store = dyn_cast<StoreInst>(&I)){
          if(Store->getPointerOperand() == LoopCounter)
            continue;
        }

        Instruction *Copy = I.clone();
        Mapping[&I] = Copy;
        Builder.Insert(Copy);
        ClonedInstructions.push_back(Copy);
      }

      for(Instruction *Copy : ClonedInstructions){
        for(size_t i = 0; i < Copy->getNumOperands(); i++){
          Value *Op = Copy->getOperand(i);
          if(Mapping.count(Op)){
            Copy->setOperand(i, Mapping[Op]);
          }
        }
      }

      
      BranchInst *ExitBranch = dyn_cast<BranchInst>(Header1->getTerminator());

      if(ExitBranch == nullptr)
        return;

      if(Exit2 != nullptr){
        for(unsigned i = 0; i < ExitBranch->getNumSuccessors(); ++i){
          if(ExitBranch->getSuccessor(i) == Exit1){
            ExitBranch->setSuccessor(i, Exit2);
          }
        }
      }
      Function *F = Header1->getParent();

      EliminateUnreachableBlocks(*F);
    }

    void fusionLoop(Loop *L1, BasicBlock *Header2){
      BasicBlock *Header1 = L1->getHeader();
    
      BasicBlock *BodyOfLoop1 = nullptr;
      BasicBlock *BodyOfLoop2 = nullptr;

      BasicBlock *Exit1 = L1->getExitBlock();
      BasicBlock *Exit2 = nullptr;

      for(BasicBlock *Succ : successors(Header1)){
        if(L1->contains(Succ) && Succ != Exit1){
          BodyOfLoop1 = Succ;
          break;
        }
      }

      for(BasicBlock *Succ : successors(Header2)){
        if(Succ != Header2 && Succ != Exit1){
          BodyOfLoop2 = Succ;
          break;
        }
      }

      for(BasicBlock *Succ : successors(Header2)){
        if(Succ != BodyOfLoop2){
          Exit2 = Succ;
          break;
        }
      }

      if(BodyOfLoop1 == nullptr || BodyOfLoop2 == nullptr)
        return;

      StoreInst *init = nullptr;
      for(Instruction &I : *Exit1){
        StoreInst *store = dyn_cast<StoreInst>(&I);
        if(store == nullptr)
          continue;

        Value *ptr = store->getPointerOperand();
        if(ptr->getName() == "y" || ptr->hasName()){ 
          init = store;
          break;
        }
      }

      if(init != nullptr){
        BasicBlock *entry = &Header1->getParent()->getEntryBlock();
        Instruction *EntryTerminator = entry->getTerminator();
        Instruction *newInit = init->clone();
        newInit->insertBefore(EntryTerminator);
      }

      
      std::unordered_map<Value *, Value *> Mapping;
      IRBuilder<> Builder(BodyOfLoop1);

      if (Instruction *Term = BodyOfLoop1->getTerminator()) {
          Builder.SetInsertPoint(Term);
      } else {
          Builder.SetInsertPoint(BodyOfLoop1);
      }

      std::vector<Instruction *> ClonedInstructions;

      for(Instruction &I : *BodyOfLoop2){
        if(I.isTerminator()){
          continue;
        }

        
        if(LoadInst *Load = dyn_cast<LoadInst>(&I)){
          if(Load->getPointerOperand() == LoopCounter)
            continue;
        }

        if(BinaryOperator *B = dyn_cast<BinaryOperator>(&I)){
          if(B->getOpcode() == Instruction::Add){
            Value *Op0 = B->getOperand(0);
            Value *Op1 = B->getOperand(1);
            ConstantInt *CI = dyn_cast<ConstantInt>(Op1);

            if(CI != nullptr && CI->getSExtValue() == 1){
              LoadInst *Load = dyn_cast<LoadInst>(Op0);
              if(Load != nullptr && Load->getPointerOperand() == LoopCounter)
                continue;
            }
          }
        }
        
       if(StoreInst *Store = dyn_cast<StoreInst>(&I)){
          if(Store->getPointerOperand() == LoopCounter)
            continue;
        }

        Instruction *Copy = I.clone();
        Mapping[&I] = Copy;
        Builder.Insert(Copy);
        ClonedInstructions.push_back(Copy);
      }

      
      for(Instruction *Copy : ClonedInstructions){
        for(size_t i = 0; i < Copy->getNumOperands(); i++){
          Value *Op = Copy->getOperand(i);
          if(Mapping.count(Op)){
            Copy->setOperand(i, Mapping[Op]);
          }
        }
      }
    
      BranchInst *ExitBranch = dyn_cast<BranchInst>(Header1->getTerminator());
      if(ExitBranch == nullptr){
        // Ako terminator zaglavlja nije direktan Branch, tražimo uslovni skok u bloku uslova
        // (u zavisnosti od strukture, obično je u header-u ili uslovnom bloku)
      }

      for(BasicBlock *Pred : predecessors(Exit1)){
        if(BranchInst *BI = dyn_cast<BranchInst>(Pred->getTerminator())){
          for(unsigned i = 0; i < BI->getNumSuccessors(); ++i){
            if(BI->getSuccessor(i) == Exit1 && Exit2 != nullptr){
              BI->setSuccessor(i, Exit2);
            }
          }
        }
      }
      Function *F = Header1->getParent();
      EliminateUnreachableBlocks(*F);
    }

    bool runOnLoop(Loop *L, LPPassManager &LPM) override {
      
      if (!L || !L->getHeader() || !L->getLoopPreheader())
        return false;

     
      if (L->getExitBlock() == nullptr)
        return false;
      
      
      LoopBasicBlocks = L->getBlocksVector();

      MapVariables(L);

      BasicBlock *NextLoopHeader = findNextLoopHeader(L);
      if(NextLoopHeader == nullptr)
        return false;

      if(!CanFusionLoop(L, NextLoopHeader))
        return false;

      fusionLoop(L, NextLoopHeader);
      
      return true;
    }

    
};
}

char OurLoopFusionPass::ID = 0;
static RegisterPass<OurLoopFusionPass> X("Our-Loop-Fusion-pass", "Loop fusion pass");