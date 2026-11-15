#pragma once

#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/CommandLine.h"

struct FLTOpaquePass : llvm::PassInfoMixin<FLTOpaquePass>
{
    llvm::PreservedAnalyses run(llvm::Module& m, llvm::ModuleAnalysisManager&);
};

bool RunFLTOpaque(llvm::Module& m);

extern llvm::cl::opt<bool> FLTOpaqueEnable;