add_llvm_library(LLVMOurLoopPass MODULE BUILDTREE_ONLY
  OurLoopFusionPass.cpp
  OurLoopPeelingPass.cpp
  OurLoopFissionPass.cpp

  DEPENDS
  intrinsics_gen
  PLUGIN_TOOL
  opt
  )