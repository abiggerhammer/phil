{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.Phase0
  ( phase0LLVMTarget
  , phase0LLVMArtifact
  , phase0LLVMVerificationContext
  ) where

import qualified Data.Map.Strict as Map
import Phil.Assurance.Types (digestText)
import Phil.LLVM.IR
import Phil.LLVM.Lower (lowerSystemsConservative)
import Phil.LLVM.Verify (LLVMVerificationContext (..))
import Phil.Systems.Phase0
  ( phase0SystemsArtifact
  , phase0SystemsVerificationContext
  )

phase0LLVMTarget :: LLVMTargetProfile
phase0LLVMTarget = LLVMTargetProfile
  { llvmTargetLanguageVersion = "LLVM IR 18 opaque-pointer subset"
  , llvmTargetToolVersion = "llvm-as 18.x expected"
  , llvmTargetTripleName = "x86_64-unknown-linux-gnu"
  , llvmTargetDataLayout =
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
  , llvmTargetRuntimeABIDigest = digestText "phil-runtime/phase0/reference-v1"
  , llvmTargetRuntimeABIProfile = "phil-runtime/phase0/reference-v1"
  }

phase0LLVMArtifact :: LLVMArtifact
phase0LLVMArtifact = lowerSystemsConservative phase0LLVMTarget phase0SystemsArtifact

phase0LLVMVerificationContext :: LLVMVerificationContext
phase0LLVMVerificationContext = LLVMVerificationContext
  { llvmSystemsContext = phase0SystemsVerificationContext
  , llvmExpectedLanguageVersion = llvmTargetLanguageVersion phase0LLVMTarget
  , llvmExpectedToolVersion = llvmTargetToolVersion phase0LLVMTarget
  , llvmExpectedTargetTriple = llvmTargetTripleName phase0LLVMTarget
  , llvmExpectedDataLayout = llvmTargetDataLayout phase0LLVMTarget
  , llvmExpectedRuntimeABIDigest = llvmTargetRuntimeABIDigest phase0LLVMTarget
  , llvmExpectedRuntimeABIProfile = llvmTargetRuntimeABIProfile phase0LLVMTarget
  , llvmAuthorizedStrengthenings = Map.empty
  }
