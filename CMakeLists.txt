cmake_minimum_required(VERSION 3.13)
project(LLVMLoopPasses)

find_package(LLVM REQUIRED CONFIG)

list(APPEND CMAKE_MODULE_PATH ${LLVM_DIR})
include(AddLLVM)

add_definitions(${LLVM_DEFINITIONS})
include_directories(${LLVM_INCLUDE_DIRS})
link_directories(${LLVM_LIBRARY_DIRS})

# Ovdje navodimo ostale fajlove u repozitorijumu kako ih LLVM ne bi prijavljivao kao "nepoznate"
set(LLVM_OPTIONAL_SOURCES
  OurLoopFusionPass.cpp
  OurLoopPeelingPass.cpp
  testForFission.c
  testForFussion.c
  testForPeeling.c
)

add_llvm_library(LLVMOurLoopFissionPass MODULE
  OurLoopFissionPass.cpp
)
