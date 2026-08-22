{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.Storage
  ( StorageLLVMError (..)
  , storageABIDescriptor
  , phase0StorageLLVMTarget
  , phase0StorageLLVMArtifact
  , phase0StorageLLVMVerificationContext
  , verifyStorageTranslation
  , verifyPhase0StorageLLVM
  ) where

import Control.Monad (forM_, unless)
import Data.Char (isAlphaNum)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types (digestText, unDigest, unEvidenceEntryId)
import Phil.LLVM.DigestValidation
  ( digestValidationABIDescriptor
  , phase0DigestValidationLLVMTarget
  )
import Phil.LLVM.IR
import Phil.LLVM.Lower (lowerSystemsStorage)
import Phil.LLVM.Verify
import Phil.Systems.DigestValidation
import Phil.Systems.IR
import Phil.Systems.Storage

data StorageLLVMError
  = StorageSystemsCandidateError StorageError
  | StorageLLVMVerificationError LLVMVerificationError
  | StorageLLVMFunctionMissing Text
  | StorageTransportParameterMismatch Text [LLVMParameter]
  | StorageLLVMBlockMissing Text LLVMBlockId
  | StorageLLVMTerminatorMismatch Text LLVMBlockId LLVMTerminator
  | StorageRenderedCallMismatch Text
  | StorageRenderedStatusMismatch Text
  | StorageAmbientStateDetected Text
  | StoragePostTransferReleaseDetected Text LLVMBlockId Text
  | StorageEvidenceSymbolDetected Text
  deriving (Eq, Show)

storageABIDescriptor :: Text
storageABIDescriptor = Text.unlines
  [ "phil-runtime/phase0/storage-v1"
  , "base-digest-validation-abi-digest=" <> unDigest (digestText digestValidationABIDescriptor)
  , "target=" <> llvmTargetTripleName phase0DigestValidationLLVMTarget
  , "data-layout=" <> llvmTargetDataLayout phase0DigestValidationLLVMTarget
  , "store=phil_runtime_store(ptr)->{i8,ptr}"
  , "store-payload-operand=exact-receive-owner"
  , "store-ownership=consume-payload-on-all-outcomes"
  , "store-status=1-success,other-failure"
  , "store-failure-upload-id=null"
  , "upload-id-handle=opaque-runtime-managed-nonowning"
  , "upload-id-lifetime=valid-through-calling-component-return"
  , "upload-id-layout-access=forbidden"
  , "upload-id-release=forbidden"
  , "ambient-storage-payload=forbidden"
  , "runtime-symbol-identity=physical-primitive-and-signature"
  , "pointer-strengthening=none-by-default"
  ]

phase0StorageLLVMTarget :: LLVMTargetProfile
phase0StorageLLVMTarget = phase0DigestValidationLLVMTarget
  { llvmTargetRuntimeABIDigest = digestText storageABIDescriptor
  , llvmTargetRuntimeABIProfile = "phil-runtime/phase0/storage-v1"
  }

phase0StorageLLVMArtifact :: Either StorageError LLVMArtifact
phase0StorageLLVMArtifact = do
  bundle <- phase0StorageBundle
  pure (lowerSystemsStorage phase0StorageLLVMTarget (storageArtifact bundle))

phase0StorageLLVMVerificationContext :: StorageBundle -> LLVMVerificationContext
phase0StorageLLVMVerificationContext bundle = LLVMVerificationContext
  { llvmSystemsContext = storageContext bundle
  , llvmExpectedLanguageVersion = llvmTargetLanguageVersion phase0StorageLLVMTarget
  , llvmExpectedToolVersion = llvmTargetToolVersion phase0StorageLLVMTarget
  , llvmExpectedTargetTriple = llvmTargetTripleName phase0StorageLLVMTarget
  , llvmExpectedDataLayout = llvmTargetDataLayout phase0StorageLLVMTarget
  , llvmExpectedRuntimeABIDigest = llvmTargetRuntimeABIDigest phase0StorageLLVMTarget
  , llvmExpectedRuntimeABIProfile = llvmTargetRuntimeABIProfile phase0StorageLLVMTarget
  , llvmAuthorizedStrengthenings = mempty
  }

verifyStorageTranslation
  :: StorageBundle
  -> LLVMArtifact
  -> Either StorageLLVMError ()
verifyStorageTranslation bundle llvmArtifact = do
  mapLeft StorageSystemsCandidateError (verifyStorageBundle bundle)
  let systemsArtifact = storageArtifact bundle
      systemsProgram = systemsArtifactProgram systemsArtifact
      llvmModule = llvmArtifactModule llvmArtifact
      context = phase0StorageLLVMVerificationContext bundle

  forM_ (Map.toAscList (systemsProgramFunctions systemsProgram)) $
    \(functionName, systemsFunction) -> do
      llvmFunction <- lookupLLVMFunction llvmModule functionName
      let expectedParameters =
            [ LLVMParameter (unValueId valueId) LLVMPointerParameter
            | (valueId, SystemsValue { systemsValueRole = TransportHandle }) <-
                Map.toAscList (systemsFunctionValues systemsFunction)
            ]
      unless (llvmFunctionParameters llvmFunction == expectedParameters) $
        Left (StorageTransportParameterMismatch functionName (llvmFunctionParameters llvmFunction))

  verifyWitness bundle llvmArtifact

  mapLeft StorageLLVMVerificationError $
    verifyLLVMEmissionWith lowerSystemsStorage context systemsArtifact llvmArtifact

verifyWitness :: StorageBundle -> LLVMArtifact -> Either StorageLLVMError ()
verifyWitness bundle llvmArtifact = do
  let witness = storageWitness bundle
      functionName = storageFunction witness
      systemsArtifact = storageArtifact bundle
      systemsProgram = systemsArtifactProgram systemsArtifact
      llvmModule = llvmArtifactModule llvmArtifact
      blockId = LLVMBlockId (unBlockId (storageBlock witness))
      payloadName = payloadSSAName (storageOwner witness)
      uploadIdName = unValueId (storageResult witness)

  systemsFunction <- case Map.lookup functionName (systemsProgramFunctions systemsProgram) of
    Nothing -> Left (StorageSystemsCandidateError (StorageFunctionMissing functionName))
    Just value -> Right value
  sourceBlock <- case Map.lookup (storageBlock witness) (systemsFunctionBlocks systemsFunction) of
    Nothing -> Left (StorageSystemsCandidateError (StorageBlockMissing functionName (storageBlock witness)))
    Just value -> Right value
  (site, yes, no) <- case systemsBlockTerminator sourceBlock of
    TermStore
      { storeOwner = owner
      , storeResult = result
      , storeSite = siteValue
      , storeSuccess = yesValue
      , storeFailure = noValue
      }
      | owner == storageOwner witness
          && result == storageResult witness
          && runtimeSiteKind siteValue == StorageBoundary -> Right (siteValue, yesValue, noValue)
    other -> Left (StorageSystemsCandidateError
      (Phil.Systems.Storage.StorageTerminatorMismatch functionName (storageBlock witness) other))

  llvmFunction <- lookupLLVMFunction llvmModule functionName
  llvmBlock <- lookupLLVMBlock functionName llvmFunction blockId
  let expected = LLVMStore
        site
        payloadName
        uploadIdName
        (LLVMBlockId (unBlockId yes))
        (LLVMBlockId (unBlockId no))
  unless (llvmBlockTerminator llvmBlock == expected) $
    Left (StorageLLVMTerminatorMismatch functionName blockId (llvmBlockTerminator llvmBlock))

  mapM_ (rejectPayloadRelease functionName llvmFunction payloadName)
    [ blockId
    , LLVMBlockId (unBlockId (storageSuccess witness))
    , LLVMBlockId (unBlockId (storageFailure witness))
    ]

  let rendered = llvmArtifactText llvmArtifact
      blockSymbol = symbolish (unBlockId (storageBlock witness))
      callNeedle = "@phil_runtime_store(ptr %" <> symbolish payloadName <> ")"
      uploadNeedle = "%" <> symbolish uploadIdName
        <> " = extractvalue { i8, ptr } %phil_store_result_" <> blockSymbol <> ", 1"
      statusNeedle = "%phil_store_ok_" <> blockSymbol
        <> " = icmp eq i8 %phil_store_status_" <> blockSymbol <> ", 1"
      evidenceNamedSymbols =
        [ "@phil_runtime_" <> symbolish (unEvidenceEntryId (runtimeSiteEvidence runtimeSite))
        | sourceFunction <- Map.elems (systemsProgramFunctions systemsProgram)
        , runtimeSite <- runtimeSites sourceFunction
        ]
  unless (Text.isInfixOf callNeedle rendered && Text.isInfixOf uploadNeedle rendered) $
    Left (StorageRenderedCallMismatch functionName)
  unless (Text.isInfixOf statusNeedle rendered) $
    Left (StorageRenderedStatusMismatch functionName)
  unless
    ( not (Text.isInfixOf "@phil_runtime_store()" rendered)
    && not (Text.isInfixOf "@phil_current_payload" rendered)
    && not (Text.isInfixOf "@phil_current_upload_id" rendered)
    ) $
    Left (StorageAmbientStateDetected functionName)
  unless (all (not . (`Text.isInfixOf` rendered)) evidenceNamedSymbols) $
    Left (StorageEvidenceSymbolDetected functionName)

lookupLLVMFunction :: LLVMModule -> Text -> Either StorageLLVMError LLVMFunction
lookupLLVMFunction moduleValue functionName =
  case Map.lookup functionName (llvmFunctions moduleValue) of
    Nothing -> Left (StorageLLVMFunctionMissing functionName)
    Just value -> Right value

lookupLLVMBlock
  :: Text
  -> LLVMFunction
  -> LLVMBlockId
  -> Either StorageLLVMError LLVMBlock
lookupLLVMBlock functionName function blockId =
  case Map.lookup blockId (llvmFunctionBlocks function) of
    Nothing -> Left (StorageLLVMBlockMissing functionName blockId)
    Just value -> Right value

rejectPayloadRelease
  :: Text
  -> LLVMFunction
  -> Text
  -> LLVMBlockId
  -> Either StorageLLVMError ()
rejectPayloadRelease functionName function payloadName blockId = do
  blockValue <- lookupLLVMBlock functionName function blockId
  let bad =
        [ owner
        | LLVMBufferRelease owner <- llvmBlockOps blockValue
        , owner == payloadName
        ]
  case bad of
    owner : _ -> Left (StoragePostTransferReleaseDetected functionName blockId owner)
    [] -> Right ()

payloadSSAName :: ValueId -> Text
payloadSSAName valueId = unValueId valueId <> ".owner"

symbolish :: Text -> Text
symbolish = Text.map (\character -> if isAlphaNum character then character else '_')

verifyPhase0StorageLLVM :: Either StorageLLVMError ()
verifyPhase0StorageLLVM = do
  bundle <- mapLeft StorageSystemsCandidateError phase0StorageBundle
  let llvmArtifact = lowerSystemsStorage phase0StorageLLVMTarget (storageArtifact bundle)
  verifyStorageTranslation bundle llvmArtifact

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
