{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.ControlCodec
  ( ControlCodecLLVMError (..)
  , controlCodecABIDescriptor
  , phase0ControlCodecLLVMTarget
  , phase0ControlCodecLLVMArtifact
  , phase0ControlCodecLLVMVerificationContext
  , lowerSystemsControlCodec
  , verifyControlCodecTranslation
  , verifyPhase0ControlCodecLLVM
  ) where

import Control.Monad (unless)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types (digestText, unDigest)
import Phil.LLVM.IR
import Phil.LLVM.StorageFailureDetail
import Phil.LLVM.Verify
import Phil.Systems.IR (SystemsArtifact)
import Phil.Systems.StorageFailure

data ControlCodecLLVMError
  = ControlCodecSystemsError StorageFailureError
  | ControlCodecPredecessorError StorageFailureDetailLLVMError
  | ControlCodecLLVMVerificationError LLVMVerificationError
  | ControlCodecFunctionBodyDrift
  | ControlCodecStrengtheningDrift
  | ControlCodecRenderedPrimitiveMissing Text
  | ControlCodecLegacyProfilePresent
  deriving (Eq, Show)

controlCodecABIDescriptor :: Text
controlCodecABIDescriptor = Text.unlines
  [ "phil-runtime/phase0/control-codec-v1"
  , "base-storage-failure-detail-abi-digest=" <>
      unDigest (digestText storageFailureDetailABIDescriptor)
  , "target=" <> llvmTargetTripleName phase0StorageFailureDetailLLVMTarget
  , "data-layout=" <> llvmTargetDataLayout phase0StorageFailureDetailLLVMTarget
  , "source-authority=storage-failure-detail-v1"
  , "frame.magic=50:48:49:4c"
  , "frame.codec-version=01"
  , "frame.header=magic[4]|version:u8|tag:u8|payload-length:u16be"
  , "frame.tag.Hello=01"
  , "frame.tag.Begin=02"
  , "frame.length-semantics=exact-payload-octet-count"
  , "frame.failure=bad-magic/version/tag/length/truncation-does-not-return-normally"
  , "hello.payload=count:u16be|versions[count]:u16be"
  , "hello.count=nonzero"
  , "hello.canonical=strictly-increasing-versions"
  , "hello.payload-length=2+2*count"
  , "begin.payload=length:u64be|kind-length:u8|kind:bytes|digest-alg:u8|digest:bytes[32]"
  , "begin.kind-length=1..255"
  , "begin.kind=opaque-exact-bytes"
  , "begin.digest-alg.sha256=01"
  , "begin.digest-length.sha256=32"
  , "begin.payload-length=42+kind-length"
  , "integer-byte-order=big-endian"
  , "host-struct-layout-on-wire=forbidden"
  , "codec-provider=single-shared-client-encoder/server-decoder-implementation"
  , "pending-commit=advance-exactly-one-framed-value"
  , "recognition-failure=frame-valid-grammar-invalid-payload"
  , "operating-system-io=outside-this-profile"
  , "source-to-systems-bridge=outside-this-profile"
  , "integrated-native-upload=outside-this-profile"
  ]

phase0ControlCodecLLVMTarget :: LLVMTargetProfile
phase0ControlCodecLLVMTarget = phase0StorageFailureDetailLLVMTarget
  { llvmTargetRuntimeABIDigest = digestText controlCodecABIDescriptor
  , llvmTargetRuntimeABIProfile = "phil-runtime/phase0/control-codec-v1"
  }

phase0ControlCodecLLVMArtifact
  :: Either StorageFailureError LLVMArtifact
phase0ControlCodecLLVMArtifact = do
  bundle <- phase0StorageFailureBundle
  pure (lowerSystemsControlCodec
    phase0ControlCodecLLVMTarget
    (storageFailureArtifact bundle))

phase0ControlCodecLLVMVerificationContext
  :: StorageFailureBundle
  -> LLVMVerificationContext
phase0ControlCodecLLVMVerificationContext bundle =
  (phase0StorageFailureDetailLLVMVerificationContext bundle)
    { llvmExpectedRuntimeABIDigest = llvmTargetRuntimeABIDigest phase0ControlCodecLLVMTarget
    , llvmExpectedRuntimeABIProfile = llvmTargetRuntimeABIProfile phase0ControlCodecLLVMTarget
    }

lowerSystemsControlCodec :: LLVMTargetProfile -> SystemsArtifact -> LLVMArtifact
lowerSystemsControlCodec = lowerSystemsStorageFailureDetail

verifyControlCodecTranslation
  :: StorageFailureBundle
  -> LLVMArtifact
  -> Either ControlCodecLLVMError ()
verifyControlCodecTranslation bundle llvmArtifact = do
  mapLeft ControlCodecSystemsError (verifyStorageFailureBundle bundle)

  let systemsArtifact = storageFailureArtifact bundle
      predecessorArtifact = lowerSystemsStorageFailureDetail
        phase0StorageFailureDetailLLVMTarget
        systemsArtifact
      predecessorModule = llvmArtifactModule predecessorArtifact
      moduleValue = llvmArtifactModule llvmArtifact

  mapLeft ControlCodecPredecessorError $
    verifyStorageFailureDetailTranslation bundle predecessorArtifact

  unless (llvmFunctions moduleValue == llvmFunctions predecessorModule) $
    Left ControlCodecFunctionBodyDrift
  unless (llvmStrengthenings moduleValue == llvmStrengthenings predecessorModule) $
    Left ControlCodecStrengtheningDrift

  mapLeft ControlCodecLLVMVerificationError $
    verifyLLVMEmissionWith
      lowerSystemsControlCodec
      (phase0ControlCodecLLVMVerificationContext bundle)
      systemsArtifact
      llvmArtifact

  verifyRendered (llvmArtifactText llvmArtifact)

verifyRendered :: Text -> Either ControlCodecLLVMError ()
verifyRendered rendered = do
  let required =
        [ "; runtime-abi-profile=phil-runtime/phase0/control-codec-v1"
        , "declare void @phil_runtime_send_hello(ptr, ptr)"
        , "declare void @phil_runtime_send_begin_sha256(ptr, i64, ptr, ptr)"
        , "declare void @phil_runtime_receive_frame_Hello(ptr, ptr, ptr)"
        , "declare void @phil_runtime_receive_frame_Begin(ptr, ptr, ptr)"
        , "declare i8 @phil_runtime_recognize_Hello(ptr, ptr, ptr, ptr)"
        , "declare i8 @phil_runtime_recognize_Begin(ptr, ptr, ptr, ptr)"
        , "declare i8 @phil_runtime_store_with_error(ptr, ptr, ptr)"
        ]
  mapM_ require required
  unless
    (not (Text.isInfixOf
      "; runtime-abi-profile=phil-runtime/phase0/storage-failure-detail-v1"
      rendered)) $
    Left ControlCodecLegacyProfilePresent
  where
    require needle = unless (Text.isInfixOf needle rendered) $
      Left (ControlCodecRenderedPrimitiveMissing needle)

verifyPhase0ControlCodecLLVM :: Either ControlCodecLLVMError ()
verifyPhase0ControlCodecLLVM = do
  bundle <- mapLeft ControlCodecSystemsError phase0StorageFailureBundle
  let artifact = lowerSystemsControlCodec
        phase0ControlCodecLLVMTarget
        (storageFailureArtifact bundle)
  verifyControlCodecTranslation bundle artifact

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
