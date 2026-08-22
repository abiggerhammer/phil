{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.AcceptedResponse
  ( AcceptedResponseLLVMError (..)
  , acceptedResponseABIDescriptor
  , phase0AcceptedResponseLLVMTarget
  , phase0AcceptedResponseLLVMArtifact
  , phase0AcceptedResponseLLVMVerificationContext
  , verifyAcceptedResponseTranslation
  , verifyPhase0AcceptedResponseLLVM
  ) where

import Control.Monad (forM_, unless)
import Data.Char (isAlphaNum)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types (digestText, unDigest, unEvidenceEntryId)
import Phil.LLVM.IR
import Phil.LLVM.Lower (lowerSystemsAcceptedResponse)
import Phil.LLVM.Storage
  ( storageABIDescriptor
  , phase0StorageLLVMTarget
  )
import Phil.LLVM.Verify
import Phil.Systems.AcceptedResponse
import Phil.Systems.IR
import Phil.Systems.Storage

data AcceptedResponseLLVMError
  = AcceptedResponseSystemsCandidateError AcceptedResponseError
  | AcceptedResponseLLVMVerificationError LLVMVerificationError
  | AcceptedResponseLLVMFunctionMissing Text
  | AcceptedResponseTransportParameterMismatch Text [LLVMParameter]
  | AcceptedResponseLLVMBlockMissing Text LLVMBlockId
  | AcceptedResponseLLVMOperationMismatch Text LLVMBlockId [LLVMOp]
  | AcceptedResponseLLVMTerminationMismatch Text LLVMBlockId LLVMTerminator
  | AcceptedResponseLLVMStoreMismatch Text LLVMBlockId LLVMTerminator
  | AcceptedResponseRenderedCallMismatch Text
  | AcceptedResponseGenericCallDetected Text
  | AcceptedResponseAmbientStateDetected Text
  | AcceptedResponseUploadIdRepresentationViolation Text
  | AcceptedResponseEvidenceSymbolDetected Text
  deriving (Eq, Show)

acceptedResponseABIDescriptor :: Text
acceptedResponseABIDescriptor = Text.unlines
  [ "phil-runtime/phase0/accepted-response-v1"
  , "base-storage-abi-digest=" <> unDigest (digestText storageABIDescriptor)
  , "target=" <> llvmTargetTripleName phase0StorageLLVMTarget
  , "data-layout=" <> llvmTargetDataLayout phase0StorageLLVMTarget
  , "accepted-selector=phil_runtime_select_accepted(ptr,ptr)->void"
  , "accepted-transport-operand=exact-component-transport-handle"
  , "accepted-upload-id-operand=exact-storage-result-handle"
  , "accepted-wire-length=17-octets"
  , "accepted-wire-tag=0x01"
  , "rejected-wire-tag-reserved=0x00"
  , "upload-id-wire-token=16-octets"
  , "upload-id-wire-token-authority=runtime-encoder-only"
  , "upload-id-semantic-handle=opaque-runtime-managed-nonowning"
  , "upload-id-layout-access=forbidden-generated-code"
  , "upload-id-release=forbidden-generated-code"
  , "accepted-outer-framing=not-defined-by-this-profile"
  , "accepted-write-failure=residual-runtime-assumption-no-source-failure-edge"
  , "ambient-accepted-state=forbidden"
  , "runtime-symbol-identity=physical-primitive-and-signature"
  , "pointer-strengthening=none-by-default"
  , "upload-id-freshness-or-uniqueness=not-certified-by-this-profile"
  ]

phase0AcceptedResponseLLVMTarget :: LLVMTargetProfile
phase0AcceptedResponseLLVMTarget = phase0StorageLLVMTarget
  { llvmTargetRuntimeABIDigest = digestText acceptedResponseABIDescriptor
  , llvmTargetRuntimeABIProfile = "phil-runtime/phase0/accepted-response-v1"
  }

phase0AcceptedResponseLLVMArtifact :: Either AcceptedResponseError LLVMArtifact
phase0AcceptedResponseLLVMArtifact = do
  bundle <- phase0AcceptedResponseBundle
  pure (lowerSystemsAcceptedResponse
    phase0AcceptedResponseLLVMTarget
    (acceptedResponseArtifact bundle))

phase0AcceptedResponseLLVMVerificationContext
  :: AcceptedResponseBundle
  -> LLVMVerificationContext
phase0AcceptedResponseLLVMVerificationContext bundle = LLVMVerificationContext
  { llvmSystemsContext = acceptedResponseContext bundle
  , llvmExpectedLanguageVersion = llvmTargetLanguageVersion phase0AcceptedResponseLLVMTarget
  , llvmExpectedToolVersion = llvmTargetToolVersion phase0AcceptedResponseLLVMTarget
  , llvmExpectedTargetTriple = llvmTargetTripleName phase0AcceptedResponseLLVMTarget
  , llvmExpectedDataLayout = llvmTargetDataLayout phase0AcceptedResponseLLVMTarget
  , llvmExpectedRuntimeABIDigest = llvmTargetRuntimeABIDigest phase0AcceptedResponseLLVMTarget
  , llvmExpectedRuntimeABIProfile = llvmTargetRuntimeABIProfile phase0AcceptedResponseLLVMTarget
  , llvmAuthorizedStrengthenings = mempty
  }

verifyAcceptedResponseTranslation
  :: AcceptedResponseBundle
  -> LLVMArtifact
  -> Either AcceptedResponseLLVMError ()
verifyAcceptedResponseTranslation bundle llvmArtifact = do
  mapLeft AcceptedResponseSystemsCandidateError $
    verifyAcceptedResponseBundle bundle
  let systemsArtifact = acceptedResponseArtifact bundle
      systemsProgram = systemsArtifactProgram systemsArtifact
      llvmModule = llvmArtifactModule llvmArtifact
      context = phase0AcceptedResponseLLVMVerificationContext bundle

  forM_ (Map.toAscList (systemsProgramFunctions systemsProgram)) $
    \(functionName, systemsFunction) -> do
      llvmFunction <- lookupLLVMFunction llvmModule functionName
      let expectedParameters =
            [ LLVMParameter (unValueId valueId) LLVMPointerParameter
            | (valueId, SystemsValue { systemsValueRole = TransportHandle }) <-
                Map.toAscList (systemsFunctionValues systemsFunction)
            ]
      unless (llvmFunctionParameters llvmFunction == expectedParameters) $
        Left (AcceptedResponseTransportParameterMismatch
          functionName
          (llvmFunctionParameters llvmFunction))

  verifyWitness bundle llvmArtifact

  mapLeft AcceptedResponseLLVMVerificationError $
    verifyLLVMEmissionWith
      lowerSystemsAcceptedResponse
      context
      systemsArtifact
      llvmArtifact

verifyWitness
  :: AcceptedResponseBundle
  -> LLVMArtifact
  -> Either AcceptedResponseLLVMError ()
verifyWitness bundle llvmArtifact = do
  let witness = acceptedResponseWitness bundle
      storeWitness = storageWitness (acceptedResponseStorageBundle bundle)
      functionName = acceptedResponseFunction witness
      systemsArtifact = acceptedResponseArtifact bundle
      systemsProgram = systemsArtifactProgram systemsArtifact
      llvmModule = llvmArtifactModule llvmArtifact
      acceptedBlockId = LLVMBlockId (unBlockId (acceptedResponseBlock witness))
      storeBlockId = LLVMBlockId (unBlockId (storageBlock storeWitness))
      expectedTransport = unValueId (acceptedResponseTransport witness)
      expectedUploadId = unValueId (acceptedResponseUploadId witness)

  llvmFunction <- lookupLLVMFunction llvmModule functionName
  acceptedBlock <- lookupLLVMBlock functionName llvmFunction acceptedBlockId
  unless (llvmBlockOps acceptedBlock == [LLVMAcceptedResponse expectedTransport expectedUploadId]) $
    Left (AcceptedResponseLLVMOperationMismatch
      functionName acceptedBlockId (llvmBlockOps acceptedBlock))
  unless (llvmBlockTerminator acceptedBlock == LLVMReturn (acceptedResponseOutcome witness)) $
    Left (AcceptedResponseLLVMTerminationMismatch
      functionName acceptedBlockId (llvmBlockTerminator acceptedBlock))

  storeBlock <- lookupLLVMBlock functionName llvmFunction storeBlockId
  case llvmBlockTerminator storeBlock of
    LLVMStore _ _ uploadId yes _
      | uploadId == expectedUploadId && yes == acceptedBlockId -> pure ()
    other -> Left (AcceptedResponseLLVMStoreMismatch functionName storeBlockId other)

  let rendered = llvmArtifactText llvmArtifact
      callNeedle = "@phil_runtime_select_accepted(ptr %"
        <> symbolish expectedTransport <> ", ptr %" <> symbolish expectedUploadId <> ")"
      uploadSymbol = "%" <> symbolish expectedUploadId
      uploadIdLines = filter (Text.isInfixOf uploadSymbol) (Text.lines rendered)
      forbiddenUploadIdTokens =
        [ "getelementptr"
        , "load "
        , "@phil_buffer_release"
        , "nonnull"
        , "noundef"
        , "dereferenceable"
        , "noalias"
        ]
      evidenceNamedSymbols =
        [ "@phil_runtime_" <> symbolish (unEvidenceEntryId (runtimeSiteEvidence runtimeSite))
        | sourceFunction <- Map.elems (systemsProgramFunctions systemsProgram)
        , runtimeSite <- runtimeSites sourceFunction
        ]
  unless (Text.isInfixOf callNeedle rendered) $
    Left (AcceptedResponseRenderedCallMismatch functionName)
  unless (not (Text.isInfixOf "@phil_call_select_accepted()" rendered)) $
    Left (AcceptedResponseGenericCallDetected functionName)
  unless
    ( not (Text.isInfixOf "@phil_current_upload_id" rendered)
    && not (Text.isInfixOf "@phil_current_transport" rendered)
    && not (Text.isInfixOf "@phil_current_accepted" rendered)
    ) $
    Left (AcceptedResponseAmbientStateDetected functionName)
  unless (all (\line -> all (not . (`Text.isInfixOf` line)) forbiddenUploadIdTokens) uploadIdLines) $
    Left (AcceptedResponseUploadIdRepresentationViolation functionName)
  unless (all (not . (`Text.isInfixOf` rendered)) evidenceNamedSymbols) $
    Left (AcceptedResponseEvidenceSymbolDetected functionName)

lookupLLVMFunction
  :: LLVMModule
  -> Text
  -> Either AcceptedResponseLLVMError LLVMFunction
lookupLLVMFunction moduleValue functionName =
  case Map.lookup functionName (llvmFunctions moduleValue) of
    Nothing -> Left (AcceptedResponseLLVMFunctionMissing functionName)
    Just value -> Right value

lookupLLVMBlock
  :: Text
  -> LLVMFunction
  -> LLVMBlockId
  -> Either AcceptedResponseLLVMError LLVMBlock
lookupLLVMBlock functionName function blockId =
  case Map.lookup blockId (llvmFunctionBlocks function) of
    Nothing -> Left (AcceptedResponseLLVMBlockMissing functionName blockId)
    Just value -> Right value

symbolish :: Text -> Text
symbolish = Text.map (\character -> if isAlphaNum character then character else '_')

verifyPhase0AcceptedResponseLLVM :: Either AcceptedResponseLLVMError ()
verifyPhase0AcceptedResponseLLVM = do
  bundle <- mapLeft AcceptedResponseSystemsCandidateError phase0AcceptedResponseBundle
  let llvmArtifact = lowerSystemsAcceptedResponse
        phase0AcceptedResponseLLVMTarget
        (acceptedResponseArtifact bundle)
  verifyAcceptedResponseTranslation bundle llvmArtifact

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
