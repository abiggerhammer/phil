{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.RejectedResponse
  ( RejectedResponseLLVMError (..)
  , rejectedResponseABIDescriptor
  , phase0RejectedResponseLLVMTarget
  , phase0RejectedResponseLLVMArtifact
  , phase0RejectedResponseLLVMVerificationContext
  , lowerSystemsRejectedResponse
  , verifyRejectedResponseTranslation
  , verifyPhase0RejectedResponseLLVM
  ) where

import Control.Monad (forM_, unless)
import Data.Char (isAlphaNum)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types (digestText, unDigest, unEvidenceEntryId)
import Phil.LLVM.AcceptedResponse
  ( acceptedResponseABIDescriptor
  , phase0AcceptedResponseLLVMTarget
  )
import Phil.LLVM.IR
import Phil.LLVM.Lower (lowerSystemsAcceptedResponse)
import Phil.LLVM.Verify
import Phil.Systems.AcceptedResponse
import Phil.Systems.IR
import Phil.Systems.RejectedResponse

data RejectedResponseLLVMError
  = RejectedResponseSystemsCandidateError RejectedResponseError
  | RejectedResponseLLVMVerificationError LLVMVerificationError
  | RejectedResponseLLVMFunctionMissing Text
  | RejectedResponseTransportParameterMismatch Text [LLVMParameter]
  | RejectedResponseLLVMBlockMissing Text LLVMBlockId
  | RejectedResponseLLVMOperationMismatch Text LLVMBlockId [LLVMOp]
  | RejectedResponseLLVMTerminationMismatch Text LLVMBlockId LLVMTerminator
  | RejectedResponseLLVMDigestEdgeMismatch Text LLVMBlockId LLVMTerminator
  | RejectedResponseRenderedCallMismatch Text
  | RejectedResponseGenericCallDetected Text
  | RejectedResponseAmbientStateDetected Text
  | RejectedResponseAcceptedRegression Text LLVMBlockId [LLVMOp]
  | RejectedResponseEvidenceSymbolDetected Text
  deriving (Eq, Show)

rejectedResponseABIDescriptor :: Text
rejectedResponseABIDescriptor = Text.unlines
  [ "phil-runtime/phase0/rejected-response-v1"
  , "base-accepted-response-abi-digest=" <> unDigest (digestText acceptedResponseABIDescriptor)
  , "target=" <> llvmTargetTripleName phase0AcceptedResponseLLVMTarget
  , "data-layout=" <> llvmTargetDataLayout phase0AcceptedResponseLLVMTarget
  , "rejected-selector=phil_runtime_select_rejected(ptr,i8)->void"
  , "rejected-transport-operand=exact-component-transport-handle"
  , "rejected-wire-length=2-octets"
  , "rejected-wire-tag=0x00"
  , "rejected-reason-width=1-octet"
  , "rejected-reason-0x01=DigestMismatch"
  , "rejected-reason-other-codes=reserved-v1"
  , "digest-failure-protocol-observable-class=singleton-DigestMismatch"
  , "digest-diagnostic-detail=not-protocol-data"
  , "digest-mismatch-reason-lowering=control-flow-singleton-to-i8-0x01"
  , "rejected-outer-framing=not-defined-by-this-profile"
  , "rejected-write-failure=residual-runtime-assumption-no-source-failure-edge"
  , "ambient-rejected-state=forbidden"
  , "ambient-digest-error-state=forbidden"
  , "runtime-symbol-identity=physical-primitive-and-signature"
  , "pointer-strengthening=none-by-default"
  ]

phase0RejectedResponseLLVMTarget :: LLVMTargetProfile
phase0RejectedResponseLLVMTarget = phase0AcceptedResponseLLVMTarget
  { llvmTargetRuntimeABIDigest = digestText rejectedResponseABIDescriptor
  , llvmTargetRuntimeABIProfile = "phil-runtime/phase0/rejected-response-v1"
  }

phase0RejectedResponseLLVMArtifact :: Either RejectedResponseError LLVMArtifact
phase0RejectedResponseLLVMArtifact = do
  bundle <- phase0RejectedResponseBundle
  pure (lowerSystemsRejectedResponse
    phase0RejectedResponseLLVMTarget
    (rejectedResponseArtifact bundle))

lowerSystemsRejectedResponse :: LLVMTargetProfile -> SystemsArtifact -> LLVMArtifact
lowerSystemsRejectedResponse target systemsArtifact = artifact
  where
    base = lowerSystemsAcceptedResponse target systemsArtifact
    witness = phase0RejectedResponseWitness
    module0 = llvmArtifactModule base
    module1 = module0
      { llvmFunctions = Map.adjust rewriteFunction
          (rejectedResponseFunction witness)
          (llvmFunctions module0)
      }
    rewriteFunction function = function
      { llvmFunctionBlocks = Map.adjust rewriteBlock
          (LLVMBlockId (unBlockId (rejectedResponseBlock witness)))
          (llvmFunctionBlocks function)
      }
    rewriteBlock blockValue = blockValue
      { llvmBlockOps = map rewriteOp (llvmBlockOps blockValue) }
    rewriteOp operation = case operation of
      LLVMCall name | name == rejectedResponseOperation witness ->
        LLVMRejectedResponse
          (unValueId (rejectedResponseTransport witness))
          (rejectedResponseReasonCode witness)
      other -> other
    contract0 = llvmArtifactContract base
    contract1 = contract0 { llvmContractTargetDigest = llvmModuleDigest module1 }
    artifact = base
      { llvmArtifactModule = module1
      , llvmArtifactText = renderLLVMModule module1
      , llvmArtifactContract = contract1
      }

phase0RejectedResponseLLVMVerificationContext
  :: RejectedResponseBundle
  -> LLVMVerificationContext
phase0RejectedResponseLLVMVerificationContext bundle = LLVMVerificationContext
  { llvmSystemsContext = rejectedResponseContext bundle
  , llvmExpectedLanguageVersion = llvmTargetLanguageVersion phase0RejectedResponseLLVMTarget
  , llvmExpectedToolVersion = llvmTargetToolVersion phase0RejectedResponseLLVMTarget
  , llvmExpectedTargetTriple = llvmTargetTripleName phase0RejectedResponseLLVMTarget
  , llvmExpectedDataLayout = llvmTargetDataLayout phase0RejectedResponseLLVMTarget
  , llvmExpectedRuntimeABIDigest = llvmTargetRuntimeABIDigest phase0RejectedResponseLLVMTarget
  , llvmExpectedRuntimeABIProfile = llvmTargetRuntimeABIProfile phase0RejectedResponseLLVMTarget
  , llvmAuthorizedStrengthenings = mempty
  }

verifyRejectedResponseTranslation
  :: RejectedResponseBundle
  -> LLVMArtifact
  -> Either RejectedResponseLLVMError ()
verifyRejectedResponseTranslation bundle llvmArtifact = do
  mapLeft RejectedResponseSystemsCandidateError $
    verifyRejectedResponseBundle bundle
  let systemsArtifact = rejectedResponseArtifact bundle
      systemsProgram = systemsArtifactProgram systemsArtifact
      llvmModule = llvmArtifactModule llvmArtifact
      context = phase0RejectedResponseLLVMVerificationContext bundle

  forM_ (Map.toAscList (systemsProgramFunctions systemsProgram)) $
    \(functionName, systemsFunction) -> do
      llvmFunction <- lookupLLVMFunction llvmModule functionName
      let expectedParameters =
            [ LLVMParameter (unValueId valueId) LLVMPointerParameter
            | (valueId, SystemsValue { systemsValueRole = TransportHandle }) <-
                Map.toAscList (systemsFunctionValues systemsFunction)
            ]
      unless (llvmFunctionParameters llvmFunction == expectedParameters) $
        Left (RejectedResponseTransportParameterMismatch
          functionName
          (llvmFunctionParameters llvmFunction))

  verifyWitness bundle llvmArtifact

  mapLeft RejectedResponseLLVMVerificationError $
    verifyLLVMEmissionWith
      lowerSystemsRejectedResponse
      context
      systemsArtifact
      llvmArtifact

verifyWitness
  :: RejectedResponseBundle
  -> LLVMArtifact
  -> Either RejectedResponseLLVMError ()
verifyWitness bundle llvmArtifact = do
  let witness = rejectedResponseWitness bundle
      acceptedBundle = rejectedResponseAcceptedBundle bundle
      acceptedWitness = acceptedResponseWitness acceptedBundle
      functionName = rejectedResponseFunction witness
      llvmModule = llvmArtifactModule llvmArtifact
      rejectedBlockId = LLVMBlockId (unBlockId (rejectedResponseBlock witness))
      digestBlockId = LLVMBlockId (unBlockId (rejectedResponseDigestBlock witness))
      acceptedBlockId = LLVMBlockId (unBlockId (acceptedResponseBlock acceptedWitness))
      expectedTransport = unValueId (rejectedResponseTransport witness)
      expectedPayload = unValueId (rejectedResponsePayloadOwner witness) <> ".owner"
      expectedReasonCode = rejectedResponseReasonCode witness

  llvmFunction <- lookupLLVMFunction llvmModule functionName
  rejectedBlock <- lookupLLVMBlock functionName llvmFunction rejectedBlockId
  unless
    (llvmBlockOps rejectedBlock ==
      [ LLVMBufferRelease expectedPayload
      , LLVMRejectedResponse expectedTransport expectedReasonCode
      ]) $
    Left (RejectedResponseLLVMOperationMismatch
      functionName rejectedBlockId (llvmBlockOps rejectedBlock))
  unless (llvmBlockTerminator rejectedBlock == LLVMReturn (rejectedResponseOutcome witness)) $
    Left (RejectedResponseLLVMTerminationMismatch
      functionName rejectedBlockId (llvmBlockTerminator rejectedBlock))

  digestBlock <- lookupLLVMBlock functionName llvmFunction digestBlockId
  case llvmBlockTerminator digestBlock of
    LLVMDigestValidate _ _ _ _ failureBlock
      | failureBlock == rejectedBlockId -> pure ()
    other -> Left (RejectedResponseLLVMDigestEdgeMismatch
      functionName digestBlockId other)

  acceptedBlock <- lookupLLVMBlock functionName llvmFunction acceptedBlockId
  case llvmBlockOps acceptedBlock of
    [LLVMAcceptedResponse transport uploadId]
      | transport == unValueId (acceptedResponseTransport acceptedWitness)
          && uploadId == unValueId (acceptedResponseUploadId acceptedWitness) -> pure ()
    operations -> Left (RejectedResponseAcceptedRegression
      functionName acceptedBlockId operations)

  let rendered = llvmArtifactText llvmArtifact
      callNeedle = "@phil_runtime_select_rejected(ptr %"
        <> symbolish expectedTransport <> ", i8 " <> Text.pack (show expectedReasonCode) <> ")"
      evidenceNamedSymbols =
        [ "@phil_runtime_" <> symbolish (unEvidenceEntryId (runtimeSiteEvidence runtimeSite))
        | sourceFunction <- Map.elems
            (systemsProgramFunctions (systemsArtifactProgram (rejectedResponseArtifact bundle)))
        , runtimeSite <- runtimeSites sourceFunction
        ]
  unless (Text.isInfixOf callNeedle rendered) $
    Left (RejectedResponseRenderedCallMismatch functionName)
  unless (not (Text.isInfixOf "@phil_call_select_rejected()" rendered)) $
    Left (RejectedResponseGenericCallDetected functionName)
  unless
    ( not (Text.isInfixOf "@phil_current_rejected" rendered)
    && not (Text.isInfixOf "@phil_current_rejection_reason" rendered)
    && not (Text.isInfixOf "@phil_last_digest_error" rendered)
    && not (Text.isInfixOf "@phil_current_transport" rendered)
    ) $
    Left (RejectedResponseAmbientStateDetected functionName)
  unless (all (not . (`Text.isInfixOf` rendered)) evidenceNamedSymbols) $
    Left (RejectedResponseEvidenceSymbolDetected functionName)

lookupLLVMFunction
  :: LLVMModule
  -> Text
  -> Either RejectedResponseLLVMError LLVMFunction
lookupLLVMFunction moduleValue functionName =
  case Map.lookup functionName (llvmFunctions moduleValue) of
    Nothing -> Left (RejectedResponseLLVMFunctionMissing functionName)
    Just value -> Right value

lookupLLVMBlock
  :: Text
  -> LLVMFunction
  -> LLVMBlockId
  -> Either RejectedResponseLLVMError LLVMBlock
lookupLLVMBlock functionName function blockId =
  case Map.lookup blockId (llvmFunctionBlocks function) of
    Nothing -> Left (RejectedResponseLLVMBlockMissing functionName blockId)
    Just value -> Right value

symbolish :: Text -> Text
symbolish = Text.map (\character -> if isAlphaNum character then character else '_')

verifyPhase0RejectedResponseLLVM :: Either RejectedResponseLLVMError ()
verifyPhase0RejectedResponseLLVM = do
  bundle <- mapLeft RejectedResponseSystemsCandidateError phase0RejectedResponseBundle
  let llvmArtifact = lowerSystemsRejectedResponse
        phase0RejectedResponseLLVMTarget
        (rejectedResponseArtifact bundle)
  verifyRejectedResponseTranslation bundle llvmArtifact

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
