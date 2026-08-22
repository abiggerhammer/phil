{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.SessionOffer
  ( FinalResponseReceiveLLVMError (..)
  , finalResponseReceiveABIDescriptor
  , phase0FinalResponseReceiveLLVMTarget
  , phase0FinalResponseReceiveLLVMArtifact
  , phase0FinalResponseReceiveLLVMVerificationContext
  , lowerSystemsFinalResponseReceive
  , verifyFinalResponseReceiveWitness
  , verifyFinalResponseReceiveTranslation
  , verifyPhase0FinalResponseReceiveLLVM
  ) where

import Control.Monad (forM_, unless)
import Data.Char (isAlphaNum)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types (digestText, unDigest)
import Phil.LLVM.IR
import Phil.LLVM.RejectedResponse
  ( rejectedResponseABIDescriptor
  , lowerSystemsRejectedResponse
  , phase0RejectedResponseLLVMTarget
  )
import Phil.LLVM.Verify
import Phil.Systems.AcceptedResponse
import Phil.Systems.IR
import Phil.Systems.RejectedResponse
import Phil.Systems.SessionChoice

data FinalResponseReceiveLLVMError
  = FinalResponseReceiveSystemsError SessionChoiceError
  | FinalResponseReceiveLLVMVerificationError LLVMVerificationError
  | FinalResponseReceiveFunctionMissing Text
  | FinalResponseReceiveBlockMissing Text LLVMBlockId
  | FinalResponseReceiveTransportParameterMismatch Text [LLVMParameter]
  | FinalResponseReceiveOfferMismatch Text LLVMBlockId LLVMTerminator
  | FinalResponseReceiveAcceptedOpsMismatch Text LLVMBlockId [LLVMOp]
  | FinalResponseReceiveRejectedOpsMismatch Text LLVMBlockId [LLVMOp]
  | FinalResponseReceiveAcceptedOutcomeMismatch Text LLVMBlockId LLVMTerminator
  | FinalResponseReceiveRejectedOutcomeMismatch Text LLVMBlockId LLVMTerminator
  | FinalResponseReceiveServerAcceptedRegression Text LLVMBlockId [LLVMOp]
  | FinalResponseReceiveServerRejectedRegression Text LLVMBlockId [LLVMOp]
  | FinalResponseReceiveRenderedCallMissing Text
  | FinalResponseReceiveGenericCallDetected Text
  | FinalResponseReceiveAmbientStateDetected Text
  | FinalResponseReceiveDigestFailureLeaked Text
  deriving (Eq, Show)

finalResponseReceiveABIDescriptor :: Text
finalResponseReceiveABIDescriptor = Text.unlines
  [ "phil-runtime/phase0/final-response-receive-v1"
  , "base-rejected-response-abi-digest=" <> unDigest (digestText rejectedResponseABIDescriptor)
  , "target=" <> llvmTargetTripleName phase0RejectedResponseLLVMTarget
  , "data-layout=" <> llvmTargetDataLayout phase0RejectedResponseLLVMTarget
  , "receive-final-response=phil_runtime_receive_final_response(ptr,ptr)->i1"
  , "receive-transport-operand=exact-client-transport-handle"
  , "accepted-out-operand=caller-owned-pointer-slot-for-opaque-UploadId-handle"
  , "accepted-return=true"
  , "rejected-return=false"
  , "accepted-wire=exactly-0x01||UploadIdToken[16]"
  , "rejected-wire=exactly-0x00||0x01"
  , "accepted-token-materialization=runtime-private-opaque-UploadId-handle"
  , "rejected-DigestFailure-representation=erased-after-exact-program-no-use-witness"
  , "record-upload-id=phil_runtime_record_upload_id(ptr)->void"
  , "malformed-truncated-reserved-response=runtime-must-not-return-normally"
  , "malformed-response-generated-branch=none"
  , "outer-framing=not-defined-by-this-profile"
  , "ambient-final-response-state=forbidden"
  , "ambient-upload-id-state=forbidden"
  , "runtime-symbol-identity=physical-primitive-and-signature"
  , "pointer-strengthening=none-by-default"
  ]

phase0FinalResponseReceiveLLVMTarget :: LLVMTargetProfile
phase0FinalResponseReceiveLLVMTarget = phase0RejectedResponseLLVMTarget
  { llvmTargetRuntimeABIDigest = digestText finalResponseReceiveABIDescriptor
  , llvmTargetRuntimeABIProfile = "phil-runtime/phase0/final-response-receive-v1"
  }

phase0FinalResponseReceiveLLVMArtifact :: Either SessionChoiceError LLVMArtifact
phase0FinalResponseReceiveLLVMArtifact = do
  bundle <- phase0SessionChoiceBundle
  pure (lowerSystemsFinalResponseReceive
    phase0FinalResponseReceiveLLVMTarget
    (sessionChoiceArtifact bundle))

lowerSystemsFinalResponseReceive :: LLVMTargetProfile -> SystemsArtifact -> LLVMArtifact
lowerSystemsFinalResponseReceive target systemsArtifact = artifact
  where
    base = lowerSystemsRejectedResponse target systemsArtifact
    witness = phase0FinalResponseChoiceWitness
    module0 = llvmArtifactModule base
    module1 = module0
      { llvmFunctions = Map.adjust
          rewriteFunction
          (sessionChoiceFunction witness)
          (llvmFunctions module0)
      }
    rewriteFunction function = function
      { llvmFunctionBlocks = Map.adjust rewriteAcceptedBlock acceptedBlockId $
          Map.adjust rewriteOfferBlock offerBlockId (llvmFunctionBlocks function)
      }
    offerBlockId = LLVMBlockId (unBlockId (sessionChoiceOfferBlock witness))
    acceptedBlockId = LLVMBlockId (unBlockId (sessionChoiceAcceptedTarget witness))
    rejectedBlockId = LLVMBlockId (unBlockId (sessionChoiceRejectedTarget witness))
    rewriteOfferBlock blockValue = blockValue
      { llvmBlockTerminator = LLVMFinalResponseOffer
          (unValueId (sessionChoiceTransport witness))
          (unValueId (sessionChoiceAcceptedPayload witness))
          acceptedBlockId
          rejectedBlockId
      }
    rewriteAcceptedBlock blockValue = blockValue
      { llvmBlockOps = concatMap rewriteAcceptedOp (llvmBlockOps blockValue) }
    rewriteAcceptedOp operation = case operation of
      LLVMCall name | name == sessionChoiceRecordOperation witness ->
        [ LLVMFinalResponsePayloadBinding (unValueId (sessionChoiceAcceptedPayload witness))
        , LLVMRecordUploadId (unValueId (sessionChoiceAcceptedPayload witness))
        ]
      other -> [other]
    contract0 = llvmArtifactContract base
    contract1 = contract0 { llvmContractTargetDigest = llvmModuleDigest module1 }
    artifact = base
      { llvmArtifactModule = module1
      , llvmArtifactText = renderLLVMModule module1
      , llvmArtifactContract = contract1
      }

phase0FinalResponseReceiveLLVMVerificationContext
  :: SessionChoiceBundle
  -> LLVMVerificationContext
phase0FinalResponseReceiveLLVMVerificationContext bundle = LLVMVerificationContext
  { llvmSystemsContext = sessionChoiceContext bundle
  , llvmExpectedLanguageVersion = llvmTargetLanguageVersion phase0FinalResponseReceiveLLVMTarget
  , llvmExpectedToolVersion = llvmTargetToolVersion phase0FinalResponseReceiveLLVMTarget
  , llvmExpectedTargetTriple = llvmTargetTripleName phase0FinalResponseReceiveLLVMTarget
  , llvmExpectedDataLayout = llvmTargetDataLayout phase0FinalResponseReceiveLLVMTarget
  , llvmExpectedRuntimeABIDigest = llvmTargetRuntimeABIDigest phase0FinalResponseReceiveLLVMTarget
  , llvmExpectedRuntimeABIProfile = llvmTargetRuntimeABIProfile phase0FinalResponseReceiveLLVMTarget
  , llvmAuthorizedStrengthenings = mempty
  }

verifyFinalResponseReceiveTranslation
  :: SessionChoiceBundle
  -> LLVMArtifact
  -> Either FinalResponseReceiveLLVMError ()
verifyFinalResponseReceiveTranslation bundle llvmArtifact = do
  mapLeft FinalResponseReceiveSystemsError $ verifySessionChoiceBundle bundle
  let systemsArtifact = sessionChoiceArtifact bundle
      systemsProgram = systemsArtifactProgram systemsArtifact
      llvmModule = llvmArtifactModule llvmArtifact
      context = phase0FinalResponseReceiveLLVMVerificationContext bundle
  forM_ (Map.toAscList (systemsProgramFunctions systemsProgram)) $
    \(functionName, systemsFunction) -> do
      llvmFunction <- lookupLLVMFunction llvmModule functionName
      let expectedParameters =
            [ LLVMParameter (unValueId valueId) LLVMPointerParameter
            | (valueId, SystemsValue { systemsValueRole = TransportHandle }) <-
                Map.toAscList (systemsFunctionValues systemsFunction)
            ]
      unless (llvmFunctionParameters llvmFunction == expectedParameters) $
        Left (FinalResponseReceiveTransportParameterMismatch
          functionName (llvmFunctionParameters llvmFunction))
  verifyFinalResponseReceiveWitness bundle llvmArtifact
  mapLeft FinalResponseReceiveLLVMVerificationError $
    verifyLLVMEmissionWith
      lowerSystemsFinalResponseReceive
      context
      systemsArtifact
      llvmArtifact

verifyFinalResponseReceiveWitness
  :: SessionChoiceBundle
  -> LLVMArtifact
  -> Either FinalResponseReceiveLLVMError ()
verifyFinalResponseReceiveWitness bundle llvmArtifact = do
  let witness = sessionChoiceWitness bundle
      predecessor = sessionChoicePredecessor bundle
      rejectedWitness = rejectedResponseWitness predecessor
      acceptedWitness = acceptedResponseWitness (rejectedResponseAcceptedBundle predecessor)
      moduleValue = llvmArtifactModule llvmArtifact
      clientFunctionName = sessionChoiceFunction witness
      offerBlockId = LLVMBlockId (unBlockId (sessionChoiceOfferBlock witness))
      acceptedBlockId = LLVMBlockId (unBlockId (sessionChoiceAcceptedTarget witness))
      rejectedBlockId = LLVMBlockId (unBlockId (sessionChoiceRejectedTarget witness))
      uploadIdName = unValueId (sessionChoiceAcceptedPayload witness)
      transportName = unValueId (sessionChoiceTransport witness)
  clientFunction <- lookupLLVMFunction moduleValue clientFunctionName
  offerBlock <- lookupLLVMBlock clientFunctionName clientFunction offerBlockId
  unless
    (llvmBlockTerminator offerBlock == LLVMFinalResponseOffer
      transportName uploadIdName acceptedBlockId rejectedBlockId) $
    Left (FinalResponseReceiveOfferMismatch
      clientFunctionName offerBlockId (llvmBlockTerminator offerBlock))

  acceptedBlock <- lookupLLVMBlock clientFunctionName clientFunction acceptedBlockId
  unless
    (llvmBlockOps acceptedBlock ==
      [LLVMFinalResponsePayloadBinding uploadIdName, LLVMRecordUploadId uploadIdName]) $
    Left (FinalResponseReceiveAcceptedOpsMismatch
      clientFunctionName acceptedBlockId (llvmBlockOps acceptedBlock))
  unless (llvmBlockTerminator acceptedBlock == LLVMReturn "success") $
    Left (FinalResponseReceiveAcceptedOutcomeMismatch
      clientFunctionName acceptedBlockId (llvmBlockTerminator acceptedBlock))

  rejectedBlock <- lookupLLVMBlock clientFunctionName clientFunction rejectedBlockId
  unless (null (llvmBlockOps rejectedBlock)) $
    Left (FinalResponseReceiveRejectedOpsMismatch
      clientFunctionName rejectedBlockId (llvmBlockOps rejectedBlock))
  unless (llvmBlockTerminator rejectedBlock == LLVMReturn "failure") $
    Left (FinalResponseReceiveRejectedOutcomeMismatch
      clientFunctionName rejectedBlockId (llvmBlockTerminator rejectedBlock))

  serverFunction <- lookupLLVMFunction moduleValue (rejectedResponseFunction rejectedWitness)
  let serverAcceptedBlockId = LLVMBlockId (unBlockId (acceptedResponseBlock acceptedWitness))
      serverRejectedBlockId = LLVMBlockId (unBlockId (rejectedResponseBlock rejectedWitness))
  serverAcceptedBlock <- lookupLLVMBlock
    (rejectedResponseFunction rejectedWitness) serverFunction serverAcceptedBlockId
  unless
    (llvmBlockOps serverAcceptedBlock ==
      [ LLVMAcceptedResponse
          (unValueId (acceptedResponseTransport acceptedWitness))
          (unValueId (acceptedResponseUploadId acceptedWitness))
      ]) $
    Left (FinalResponseReceiveServerAcceptedRegression
      (rejectedResponseFunction rejectedWitness)
      serverAcceptedBlockId
      (llvmBlockOps serverAcceptedBlock))
  serverRejectedBlock <- lookupLLVMBlock
    (rejectedResponseFunction rejectedWitness) serverFunction serverRejectedBlockId
  case llvmBlockOps serverRejectedBlock of
    [LLVMBufferRelease _, LLVMRejectedResponse _ _] -> pure ()
    operations -> Left (FinalResponseReceiveServerRejectedRegression
      (rejectedResponseFunction rejectedWitness) serverRejectedBlockId operations)

  let rendered = llvmArtifactText llvmArtifact
      receiveNeedle = "@phil_runtime_receive_final_response(ptr %"
        <> symbolish transportName <> ", ptr %phil_final_response_upload_id_slot_"
        <> symbolish uploadIdName <> ")"
      loadNeedle = "%" <> symbolish uploadIdName
        <> " = load ptr, ptr %phil_final_response_upload_id_slot_" <> symbolish uploadIdName
      recordNeedle = "@phil_runtime_record_upload_id(ptr %" <> symbolish uploadIdName <> ")"
  unless (Text.isInfixOf receiveNeedle rendered
      && Text.isInfixOf loadNeedle rendered
      && Text.isInfixOf recordNeedle rendered) $
    Left (FinalResponseReceiveRenderedCallMissing clientFunctionName)
  unless
    ( not (Text.isInfixOf "@phil_call_receive_accepted_rejected_label" rendered)
    && not (Text.isInfixOf "@phil_call_record_upload_id" rendered)
    ) $
    Left (FinalResponseReceiveGenericCallDetected clientFunctionName)
  unless
    ( not (Text.isInfixOf "@phil_current_final_response" rendered)
    && not (Text.isInfixOf "@phil_current_upload_id" rendered)
    && not (Text.isInfixOf "@phil_last_response" rendered)
    ) $
    Left (FinalResponseReceiveAmbientStateDetected clientFunctionName)
  unless (not (Text.isInfixOf "client_digest_failure" rendered)) $
    Left (FinalResponseReceiveDigestFailureLeaked clientFunctionName)

lookupLLVMFunction
  :: LLVMModule
  -> Text
  -> Either FinalResponseReceiveLLVMError LLVMFunction
lookupLLVMFunction moduleValue functionName =
  case Map.lookup functionName (llvmFunctions moduleValue) of
    Nothing -> Left (FinalResponseReceiveFunctionMissing functionName)
    Just value -> Right value

lookupLLVMBlock
  :: Text
  -> LLVMFunction
  -> LLVMBlockId
  -> Either FinalResponseReceiveLLVMError LLVMBlock
lookupLLVMBlock functionName function blockId =
  case Map.lookup blockId (llvmFunctionBlocks function) of
    Nothing -> Left (FinalResponseReceiveBlockMissing functionName blockId)
    Just value -> Right value

symbolish :: Text -> Text
symbolish = Text.map (\character -> if isAlphaNum character then character else '_')

verifyPhase0FinalResponseReceiveLLVM :: Either FinalResponseReceiveLLVMError ()
verifyPhase0FinalResponseReceiveLLVM = do
  bundle <- mapLeft FinalResponseReceiveSystemsError phase0SessionChoiceBundle
  let llvmArtifact = lowerSystemsFinalResponseReceive
        phase0FinalResponseReceiveLLVMTarget
        (sessionChoiceArtifact bundle)
  verifyFinalResponseReceiveTranslation bundle llvmArtifact

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
