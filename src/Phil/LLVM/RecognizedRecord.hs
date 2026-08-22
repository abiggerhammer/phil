{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.RecognizedRecord
  ( RecognizedRecordLLVMError (..)
  , recognizedRecordRuntimeABIProfile
  , recognizedRecordRuntimeABIDescriptor
  , phase0RecognizedRecordLLVMTarget
  , phase0RecognizedRecordLLVMArtifact
  , phase0RecognizedRecordLLVMVerificationContext
  , verifyPhase0RecognizedRecordLLVM
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Assurance.Types (Digest, digestText)
import Phil.LLVM.IR
import Phil.LLVM.Lower (lowerSystemsConservative)
import Phil.LLVM.Phase0 (phase0LLVMTarget, phase0LLVMVerificationContext)
import Phil.LLVM.Verify
import Phil.Systems.RecognizedRecord

-- | Concrete target/runtime ABI chosen by #41 and normatively amended by #43.
-- The descriptor is content-addressed into the target profile so symbol and
-- signature policy changes necessarily create a new ABI identity.
recognizedRecordRuntimeABIProfile :: Text
recognizedRecordRuntimeABIProfile = "phil-runtime/phase0/recognized-record-v1"

recognizedRecordRuntimeABIDescriptor :: Text
recognizedRecordRuntimeABIDescriptor =
  "phil-runtime/phase0/recognized-record-v1\n"
  <> "recognition-result={i8,ptr}; status-success=exactly-1; failure-record=null\n"
  <> "record-handle=opaque-runtime-owned-ptr; no-gep; no-direct-load; no-generated-free\n"
  <> "field-accessor=phil_record_<Grammar>_get_<field>(ptr)->schema-scalar\n"
  <> "Begin.length=phil_record_Begin_get_length(ptr)->i64\n"
  <> "exact-receive=phil_runtime_receive_exact_u64(i64)->i1\n"
  <> "runtime-symbol-identity=physical-operation-plus-abi-signature\n"
  <> "runtime-symbol-excludes=RevisionId,EvidenceEntryId,AssuranceUseId,claim-set-cardinality,claim-set-order\n"
  <> "physical-site-identity=call-instruction-not-linker-symbol\n"
  <> "assurance-identity=verification-relation-not-linker-symbol\n"
  <> "pointer-strengthening=none-without-separate-authority\n"

recognizedRecordRuntimeABIDigest :: Digest
recognizedRecordRuntimeABIDigest = digestText recognizedRecordRuntimeABIDescriptor

phase0RecognizedRecordLLVMTarget :: LLVMTargetProfile
phase0RecognizedRecordLLVMTarget = phase0LLVMTarget
  { llvmTargetRuntimeABIDigest = recognizedRecordRuntimeABIDigest
  , llvmTargetRuntimeABIProfile = recognizedRecordRuntimeABIProfile
  }

data RecognizedRecordLLVMError
  = RecognizedRecordSystemsRejected RecognizedRecordError
  | RecognizedRecordLLVMRejected LLVMVerificationError
  deriving (Eq, Show)

phase0RecognizedRecordLLVMArtifact :: Either RecognizedRecordLLVMError LLVMArtifact
phase0RecognizedRecordLLVMArtifact = do
  bundle <- mapLeft RecognizedRecordSystemsRejected phase0RecognizedRecordBundle
  let systemsArtifact = recognizedRecordArtifact bundle
      artifact = lowerSystemsConservative phase0RecognizedRecordLLVMTarget systemsArtifact
      context = phase0RecognizedRecordLLVMVerificationContextFor bundle
  mapLeft RecognizedRecordLLVMRejected $
    verifyLLVMEmission context systemsArtifact artifact
  Right artifact

phase0RecognizedRecordLLVMVerificationContext
  :: Either RecognizedRecordLLVMError LLVMVerificationContext
phase0RecognizedRecordLLVMVerificationContext = do
  bundle <- mapLeft RecognizedRecordSystemsRejected phase0RecognizedRecordBundle
  Right (phase0RecognizedRecordLLVMVerificationContextFor bundle)

phase0RecognizedRecordLLVMVerificationContextFor
  :: RecognizedRecordBundle
  -> LLVMVerificationContext
phase0RecognizedRecordLLVMVerificationContextFor bundle = phase0LLVMVerificationContext
  { llvmSystemsContext = recognizedRecordContext bundle
  , llvmExpectedRuntimeABIDigest = recognizedRecordRuntimeABIDigest
  , llvmExpectedRuntimeABIProfile = recognizedRecordRuntimeABIProfile
  , llvmAuthorizedStrengthenings = Map.empty
  }

verifyPhase0RecognizedRecordLLVM :: Either RecognizedRecordLLVMError ()
verifyPhase0RecognizedRecordLLVM = do
  bundle <- mapLeft RecognizedRecordSystemsRejected phase0RecognizedRecordBundle
  artifact <- phase0RecognizedRecordLLVMArtifact
  mapLeft RecognizedRecordLLVMRejected $
    verifyLLVMEmission
      (phase0RecognizedRecordLLVMVerificationContextFor bundle)
      (recognizedRecordArtifact bundle)
      artifact

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
