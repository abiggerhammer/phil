{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.StorageFailureDetail
  ( StorageFailureDetailLLVMError (..)
  , storageFailureDetailABIDescriptor
  , phase0StorageFailureDetailLLVMTarget
  , phase0StorageFailureDetailLLVMArtifact
  , phase0StorageFailureDetailLLVMVerificationContext
  , lowerSystemsStorageFailureDetail
  , verifyStorageFailureDetailTranslation
  , verifyPhase0StorageFailureDetailLLVM
  ) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types (digestText, unDigest)
import Phil.LLVM.IR
import Phil.LLVM.ServerFramedIngress
  ( ServerFramedIngressLLVMError
  , lowerSystemsServerFramedIngress
  , phase0ServerFramedIngressLLVMTarget
  , serverFramedIngressABIDescriptor
  , verifyServerFramedIngressLLVMWitnesses
  )
import Phil.LLVM.Verify
import Phil.Systems.IR
import Phil.Systems.StorageFailure

data StorageFailureDetailLLVMError
  = StorageFailureDetailSystemsError StorageFailureError
  | StorageFailureDetailServerIngressRegression ServerFramedIngressLLVMError
  | StorageFailureDetailLLVMVerificationError LLVMVerificationError
  | StorageFailureDetailFunctionMissing Text
  | StorageFailureDetailBlockMissing Text LLVMBlockId
  | StorageFailureDetailStoreMismatch LLVMTerminator
  | StorageFailureDetailFailureMismatch [LLVMOp] LLVMTerminator
  | StorageFailureDetailRenderedPrimitiveMissing Text
  | StorageFailureDetailLegacyPrimitivePresent Text
  | StorageFailureDetailAmbientStatePresent Text
  deriving (Eq, Show)

storageFailureDetailABIDescriptor :: Text
storageFailureDetailABIDescriptor = Text.unlines
  [ "phil-runtime/phase0/storage-failure-detail-v1"
  , "base-server-framed-ingress-abi-digest=" <> unDigest (digestText serverFramedIngressABIDescriptor)
  , "target=" <> llvmTargetTripleName phase0ServerFramedIngressLLVMTarget
  , "data-layout=" <> llvmTargetDataLayout phase0ServerFramedIngressLLVMTarget
  , "source-authority=storage-failure-detail-v1"
  , "store=phil_runtime_store_with_error(ptr,ptr,ptr)->i8"
  , "store-arg0=exact-server-payload-owner"
  , "store-arg1=upload-id-output-slot"
  , "store-arg2=storage-error-output-slot"
  , "store-status=1-success,other-failure"
  , "store-slot-initialization=compiler-writes-null-before-call"
  , "store-success=upload-id-valid,error-null"
  , "store-failure=upload-id-null,error-valid"
  , "store-ownership=payload-consumed-on-all-outcomes"
  , "storage-error=opaque-provider-managed-handle"
  , "failure-effect=phil_runtime_fail_storage(ptr,ptr)->void"
  , "failure-effect-arg0=exact-server-transport"
  , "failure-effect-arg1=exact-store-error-handle"
  , "failure-effect-semantics=local-terminal-internal-storage-failure-effect"
  , "payload-observation-after-store=forbidden"
  , "ambient-storage-error=forbidden"
  , "ambient-storage-payload=forbidden"
  , "wire-codec=outside-this-profile"
  ]

phase0StorageFailureDetailLLVMTarget :: LLVMTargetProfile
phase0StorageFailureDetailLLVMTarget = phase0ServerFramedIngressLLVMTarget
  { llvmTargetRuntimeABIDigest = digestText storageFailureDetailABIDescriptor
  , llvmTargetRuntimeABIProfile = "phil-runtime/phase0/storage-failure-detail-v1"
  }

phase0StorageFailureDetailLLVMArtifact
  :: Either StorageFailureError LLVMArtifact
phase0StorageFailureDetailLLVMArtifact = do
  bundle <- phase0StorageFailureBundle
  pure (lowerSystemsStorageFailureDetail
    phase0StorageFailureDetailLLVMTarget
    (storageFailureArtifact bundle))

phase0StorageFailureDetailLLVMVerificationContext
  :: StorageFailureBundle
  -> LLVMVerificationContext
phase0StorageFailureDetailLLVMVerificationContext bundle = LLVMVerificationContext
  { llvmSystemsContext = storageFailureContext bundle
  , llvmExpectedLanguageVersion = llvmTargetLanguageVersion phase0StorageFailureDetailLLVMTarget
  , llvmExpectedToolVersion = llvmTargetToolVersion phase0StorageFailureDetailLLVMTarget
  , llvmExpectedTargetTriple = llvmTargetTripleName phase0StorageFailureDetailLLVMTarget
  , llvmExpectedDataLayout = llvmTargetDataLayout phase0StorageFailureDetailLLVMTarget
  , llvmExpectedRuntimeABIDigest = llvmTargetRuntimeABIDigest phase0StorageFailureDetailLLVMTarget
  , llvmExpectedRuntimeABIProfile = llvmTargetRuntimeABIProfile phase0StorageFailureDetailLLVMTarget
  , llvmAuthorizedStrengthenings = mempty
  }

lowerSystemsStorageFailureDetail :: LLVMTargetProfile -> SystemsArtifact -> LLVMArtifact
lowerSystemsStorageFailureDetail target systemsArtifact = artifact
  where
    base = lowerSystemsServerFramedIngress target systemsArtifact
    witness = phase0StorageFailureWitness
    module0 = llvmArtifactModule base
    module1 = module0
      { llvmFunctions = Map.adjust rewriteServer
          (storageFailureFunction witness)
          (llvmFunctions module0)
      }
    rewriteServer function = function
      { llvmFunctionBlocks =
          Map.adjust rewriteStore
            (LLVMBlockId (unBlockId (storageFailureStoreBlock witness))) $
          Map.adjust rewriteFailure
            (LLVMBlockId (unBlockId (storageFailureFailureBlock witness)))
            (llvmFunctionBlocks function)
      }
    rewriteStore blockValue = blockValue
      { llvmBlockTerminator = case llvmBlockTerminator blockValue of
          LLVMStore site payload uploadId yes no ->
            LLVMStoreDetailed
              site
              payload
              uploadId
              (unValueId (storageFailureErrorValue witness))
              yes
              no
          other -> other
      }
    rewriteFailure blockValue = blockValue
      { llvmBlockOps = concatMap rewriteFailureOp (llvmBlockOps blockValue) }
    rewriteFailureOp operation = case operation of
      LLVMCall name
        | name == storageFailureMaterializeCall witness -> []
        | name == storageFailureEffectCall witness ->
            [ LLVMStorageFailureEffect
                (unValueId (storageFailureTransport witness))
                (unValueId (storageFailureErrorValue witness))
            ]
      other -> [other]
    contract0 = llvmArtifactContract base
    contract1 = contract0 { llvmContractTargetDigest = llvmModuleDigest module1 }
    artifact = base
      { llvmArtifactModule = module1
      , llvmArtifactText = renderLLVMModule module1
      , llvmArtifactContract = contract1
      }

verifyStorageFailureDetailTranslation
  :: StorageFailureBundle
  -> LLVMArtifact
  -> Either StorageFailureDetailLLVMError ()
verifyStorageFailureDetailTranslation bundle llvmArtifact = do
  mapLeft StorageFailureDetailSystemsError (verifyStorageFailureBundle bundle)
  mapLeft StorageFailureDetailServerIngressRegression $
    verifyServerFramedIngressLLVMWitnesses
      (storageFailurePredecessor bundle)
      llvmArtifact
  verifyStorageFailureDetailWitness bundle llvmArtifact
  mapLeft StorageFailureDetailLLVMVerificationError $
    verifyLLVMEmissionWith
      lowerSystemsStorageFailureDetail
      (phase0StorageFailureDetailLLVMVerificationContext bundle)
      (storageFailureArtifact bundle)
      llvmArtifact

verifyStorageFailureDetailWitness
  :: StorageFailureBundle
  -> LLVMArtifact
  -> Either StorageFailureDetailLLVMError ()
verifyStorageFailureDetailWitness bundle llvmArtifact = do
  let witness = storageFailureWitness bundle
      functionName = storageFailureFunction witness
      moduleValue = llvmArtifactModule llvmArtifact
      storeId = LLVMBlockId (unBlockId (storageFailureStoreBlock witness))
      failureId = LLVMBlockId (unBlockId (storageFailureFailureBlock witness))
  function <- maybe
    (Left (StorageFailureDetailFunctionMissing functionName))
    Right
    (Map.lookup functionName (llvmFunctions moduleValue))
  storeBlock <- lookupBlock functionName function storeId
  case llvmBlockTerminator storeBlock of
    LLVMStoreDetailed site payload uploadId storageError yes no
      | runtimeSiteKind site == StorageBoundary
          && payload == unValueId (storageFailureOwner witness) <> ".owner"
          && uploadId == unValueId (storageFailureSuccessResult witness)
          && storageError == unValueId (storageFailureErrorValue witness)
          && yes /= no -> pure ()
    other -> Left (StorageFailureDetailStoreMismatch other)
  failureBlock <- lookupBlock functionName function failureId
  let expectedOps =
        [ LLVMStorageFailureEffect
            (unValueId (storageFailureTransport witness))
            (unValueId (storageFailureErrorValue witness))
        ]
      expectedTerminator = LLVMReturn ("fatal:" <> storageFailureFatalClass witness)
  unless
    ( llvmBlockOps failureBlock == expectedOps
    && llvmBlockTerminator failureBlock == expectedTerminator
    ) $
    Left (StorageFailureDetailFailureMismatch
      (llvmBlockOps failureBlock)
      (llvmBlockTerminator failureBlock))
  verifyRendered (llvmArtifactText llvmArtifact)

verifyRendered :: Text -> Either StorageFailureDetailLLVMError ()
verifyRendered rendered = do
  let required =
        [ "declare i8 @phil_runtime_store_with_error(ptr, ptr, ptr)"
        , "declare void @phil_runtime_fail_storage(ptr, ptr)"
        , "@phil_runtime_store_with_error(ptr %server_payload_owner"
        , "@phil_runtime_fail_storage(ptr %server_transport, ptr %server_storage_error)"
        ]
      forbidden =
        [ "@phil_runtime_store(ptr %server_payload_owner)"
        , "@phil_call_materialize_storage_failure_error()"
        , "@phil_call_fail_internal_storage()"
        , "current_storage_error"
        , "current_storage_payload"
        ]
  mapM_ require required
  mapM_ forbid forbidden
  where
    require needle = unless (Text.isInfixOf needle rendered) $
      Left (StorageFailureDetailRenderedPrimitiveMissing needle)
    forbid needle = unless (not (Text.isInfixOf needle rendered)) $
      Left (StorageFailureDetailLegacyPrimitivePresent needle)

lookupBlock
  :: Text
  -> LLVMFunction
  -> LLVMBlockId
  -> Either StorageFailureDetailLLVMError LLVMBlock
lookupBlock functionName function blockId =
  maybe
    (Left (StorageFailureDetailBlockMissing functionName blockId))
    Right
    (Map.lookup blockId (llvmFunctionBlocks function))

verifyPhase0StorageFailureDetailLLVM
  :: Either StorageFailureDetailLLVMError ()
verifyPhase0StorageFailureDetailLLVM = do
  bundle <- mapLeft StorageFailureDetailSystemsError phase0StorageFailureBundle
  let artifact = lowerSystemsStorageFailureDetail
        phase0StorageFailureDetailLLVMTarget
        (storageFailureArtifact bundle)
  verifyStorageFailureDetailTranslation bundle artifact

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
