cmake_minimum_required(VERSION 3.13)
project(LLVMLoopPasses)

find_package(LLVM REQUIRED CONFIG)

list(APPEND CMAKE_MODULE_PATH ${LLVM_DIR})
include(AddLLVM)

add_definitions(${LLVM_DEFINITIONS})
include_directories(${LLVM_INCLUDE_DIRS})
link_directories(${LLVM_LIBRARY_DIRS})

add_llvm_library(LLVMOurLoopFissionPass MODULE
  OurLoopFissionPass.cpp
)
