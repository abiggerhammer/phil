{-# LANGUAGE OverloadedStrings #-}

module Phil.Compiler.RuntimeChoiceTargets
  ( runtimeChoiceAArch64AppleDarwinABIDescriptor
  , phase1RuntimeChoiceAArch64AppleDarwinTarget
  ) where

import qualified Data.Text as Text
import Data.Text (Text)
import Phil.Assurance.Types (digestText)
import Phil.Compiler.RuntimeChoiceLLVM (runtimeChoiceProviderABIDescriptor)
import Phil.LLVM.IR (LLVMTargetProfile (..))

-- | Phase-1 runtime-choice provider ABI specialized to the Apple Silicon
-- Darwin target family. The ABI identity is target-specific even though the
-- semantic handle/call convention is otherwise the same as the Linux profile.
runtimeChoiceAArch64AppleDarwinABIDescriptor :: Text
runtimeChoiceAArch64AppleDarwinABIDescriptor = Text.replace
  "target=x86_64-unknown-linux-gnu"
  "target=aarch64-apple-darwin"
  runtimeChoiceProviderABIDescriptor

-- | LLVM 18 target profile for native Apple Silicon Darwin execution.
--
-- The data layout was probed from Homebrew LLVM 18.1.8 on a native arm64
-- macOS runner by compiling with --target=aarch64-apple-darwin. We retain the
-- generic Darwin target identity here rather than LLVM's deployment-version
-- canonicalization, so the certified profile names the ABI family rather than
-- one runner image's minimum macOS spelling.
phase1RuntimeChoiceAArch64AppleDarwinTarget :: LLVMTargetProfile
phase1RuntimeChoiceAArch64AppleDarwinTarget = LLVMTargetProfile
  { llvmTargetLanguageVersion = "LLVM IR 18 opaque-pointer subset"
  , llvmTargetToolVersion = "llvm-as 18.x expected"
  , llvmTargetTripleName = "aarch64-apple-darwin"
  , llvmTargetDataLayout = "e-m:o-i64:64-i128:128-n32:64-S128"
  , llvmTargetRuntimeABIDigest = digestText runtimeChoiceAArch64AppleDarwinABIDescriptor
  , llvmTargetRuntimeABIProfile = "phil-runtime/phase1/runtime-choice-provider-v1"
  }
