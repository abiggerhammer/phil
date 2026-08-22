{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.RecognizedRecord
  ( RecognizedRecordLLVMError (..)
  , recognizedRecordABIDescriptor
  , phase0RecognizedRecordLLVMTarget
  , phase0RecognizedRecordLLVMArtifact
  , phase0RecognizedRecordLLVMVerificationContext
  , verifyPhase0RecognizedRecordLLVM
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types (digestText)
import Phil.LLVM.IR
import Phil.LLVM.Lower (lowerSystemsRecognizedRecord)
import Phil.LLVM.Phase0 (phase0LLVMTarget)
import Phil.LLVM.Verify
import Phil.Systems.RecognizedRecord

data RecognizedRecordLLVMError
  = RecognizedRecordSystemsCandidateError RecognizedRecordError
  | RecognizedRecordLLVMVerificationError LLVMVerificationError
  deriving (Eq, Show)

recognizedRecordABIDescriptor :: Text
recognizedRecordABIDescriptor = Text.unlines
  [ "phil-runtime/phase0/recognized-record-v1"
  , "target=x86_64-unknown-linux-gnu"
  , "recognition-result={i8,ptr}"
  , "recognition-status=0-failure,1-success,other-fail-closed"
  , "recognition-failure-record=null"
  , "record-handle=opaque-runtime-owned"
  , "generated-record-dereference=forbidden"
  , "scalar-accessor=phil_record_<grammar>_get_<field>(ptr)->iN"
  , "runtime-symbol-identity=physical-primitive-and-signature"
  , "exact-receive-u64=phil_runtime_receive_exact_u64(i64)->i1"
  , "pointer-strengthening=none-by-default"
  ]

phase0RecognizedRecordLLVMTarget :: LLVMTargetProfile
phase0RecognizedRecordLLVMTarget = phase0LLVMTarget
  { llvmTargetRuntimeABIDigest = digestText recognizedRecordABIDescriptor
  , llvmTargetRuntimeABIProfile = "phil-runtime/phase0/recognized-record-v1"
  }

phase0RecognizedRecordLLVMArtifact
  :: Either RecognizedRecordError LLVMArtifact
phase0RecognizedRecordLLVMArtifact = do
  bundle <- phase0RecognizedRecordBundle
  pure (lowerSystemsRecognizedRecord
    phase0RecognizedRecordLLVMTarget
    (recognizedRecordArtifact bundle))

phase0RecognizedRecordLLVMVerificationContext
  :: RecognizedRecordBundle
  -> LLVMVerificationContext
phase0RecognizedRecordLLVMVerificationContext bundle = LLVMVerificationContext
  { llvmSystemsContext = recognizedRecordContext bundle
  , llvmExpectedLanguageVersion = llvmTargetLanguageVersion phase0RecognizedRecordLLVMTarget
  , llvmExpectedToolVersion = llvmTargetToolVersion phase0RecognizedRecordLLVMTarget
  , llvmExpectedTargetTriple = llvmTargetTripleName phase0RecognizedRecordLLVMTarget
  , llvmExpectedDataLayout = llvmTargetDataLayout phase0RecognizedRecordLLVMTarget
  , llvmExpectedRuntimeABIDigest = llvmTargetRuntimeABIDigest phase0RecognizedRecordLLVMTarget
  , llvmExpectedRuntimeABIProfile = llvmTargetRuntimeABIProfile phase0RecognizedRecordLLVMTarget
  , llvmAuthorizedStrengthenings = mempty
  }

verifyPhase0RecognizedRecordLLVM
  :: Either RecognizedRecordLLVMError ()
verifyPhase0RecognizedRecordLLVM = do
  bundle <- mapLeft RecognizedRecordSystemsCandidateError phase0RecognizedRecordBundle
  let systemsArtifact = recognizedRecordArtifact bundle
      llvmArtifact = lowerSystemsRecognizedRecord phase0RecognizedRecordLLVMTarget systemsArtifact
      context = phase0RecognizedRecordLLVMVerificationContext bundle
  mapLeft RecognizedRecordLLVMVerificationError $
    verifyLLVMEmissionWith
      lowerSystemsRecognizedRecord
      context
      systemsArtifact
      llvmArtifact

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
