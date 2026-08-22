{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.PayloadCancelChoice
  ( PayloadCancelChoiceLLVMError (..)
  , payloadCancelChoiceABIDescriptor
  , payloadChoiceCode
  , cancelChoiceCode
  , phase0PayloadCancelChoiceLLVMTarget
  , phase0PayloadCancelChoiceLLVMArtifact
  , phase0PayloadCancelChoiceLLVMVerificationContext
  , lowerSystemsPayloadCancelChoice
  , verifyPayloadCancelChoiceLLVMWitness
  , verifyPayloadCancelChoiceTranslation
  , verifyPhase0PayloadCancelChoiceLLVM
  ) where

import Control.Monad (forM_, unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types (digestText, unDigest)
import Phil.LLVM.IR
import Phil.LLVM.SessionOffer
  ( finalResponseReceiveABIDescriptor
  , lowerSystemsFinalResponseReceive
  , phase0FinalResponseReceiveLLVMTarget
  , verifyFinalResponseReceiveWitness
  )
import Phil.LLVM.Verify
import Phil.Systems.IR
import Phil.Systems.PayloadCancelChoice

data PayloadCancelChoiceLLVMError
  = PayloadCancelChoiceSystemsError PayloadCancelChoiceError
  | PayloadCancelChoiceLLVMVerificationError LLVMVerificationError
  | PayloadCancelChoiceFinalResponseRegression Text
  | PayloadCancelChoiceFunctionMissing Text
  | PayloadCancelChoiceBlockMissing Text LLVMBlockId
  | PayloadCancelChoiceTransportParameterMismatch Text [LLVMParameter]
  | PayloadCancelChoiceClientSelectMismatch Text LLVMBlockId [LLVMOp]
  | PayloadCancelChoiceServerOfferMismatch Text LLVMBlockId LLVMTerminator
  | PayloadCancelChoiceRenderedCallMissing Text
  | PayloadCancelChoiceGenericCallDetected Text
  | PayloadCancelChoiceAmbientStateDetected Text
  | PayloadCancelChoicePoisonDetected Text
  deriving (Eq, Show)

payloadChoiceCode, cancelChoiceCode :: Int
payloadChoiceCode = 1
cancelChoiceCode = 0

payloadCancelChoiceABIDescriptor :: Text
payloadCancelChoiceABIDescriptor = Text.unlines
  [ "phil-runtime/phase0/payload-cancel-choice-v1"
  , "base-final-response-receive-abi-digest=" <> unDigest (digestText finalResponseReceiveABIDescriptor)
  , "target=" <> llvmTargetTripleName phase0FinalResponseReceiveLLVMTarget
  , "data-layout=" <> llvmTargetDataLayout phase0FinalResponseReceiveLLVMTarget
  , "select=phil_runtime_select_payload_cancel(ptr,i8)->void"
  , "select-transport-operand=exact-client-transport-handle"
  , "select-payload-code=0x01"
  , "select-cancel-code=0x00"
  , "select-other-code=forbidden-from-generated-code"
  , "select-write=exactly-one-octet"
  , "select-write-failure=residual-runtime-assumption;source-select-has-no-failure-edge"
  , "receive=phil_runtime_receive_payload_cancel(ptr)->i1"
  , "receive-transport-operand=exact-server-transport-handle"
  , "receive-0x01=true=payload"
  , "receive-0x00=false=cancel"
  , "receive-early-eof-or-reserved-octet=runtime-must-not-return-normally"
  , "malformed-choice-generated-branch=none"
  , "choice-payload=none"
  , "outer-framing=not-defined-by-this-profile"
  , "ambient-choice-state=forbidden"
  , "ambient-transport-state=forbidden"
  , "runtime-symbol-identity=physical-primitive-and-signature"
  , "pointer-strengthening=none-by-default"
  ]

phase0PayloadCancelChoiceLLVMTarget :: LLVMTargetProfile
phase0PayloadCancelChoiceLLVMTarget = phase0FinalResponseReceiveLLVMTarget
  { llvmTargetRuntimeABIDigest = digestText payloadCancelChoiceABIDescriptor
  , llvmTargetRuntimeABIProfile = "phil-runtime/phase0/payload-cancel-choice-v1"
  }

phase0PayloadCancelChoiceLLVMArtifact
  :: Either PayloadCancelChoiceError LLVMArtifact
phase0PayloadCancelChoiceLLVMArtifact = do
  bundle <- phase0PayloadCancelChoiceBundle
  pure (lowerSystemsPayloadCancelChoice
    phase0PayloadCancelChoiceLLVMTarget
    (payloadCancelChoiceArtifact bundle))

lowerSystemsPayloadCancelChoice :: LLVMTargetProfile -> SystemsArtifact -> LLVMArtifact
lowerSystemsPayloadCancelChoice target systemsArtifact = artifact
  where
    base = lowerSystemsFinalResponseReceive target systemsArtifact
    witness = phase0PayloadCancelChoiceWitness
    module0 = llvmArtifactModule base
    module1 = module0
      { llvmFunctions = Map.adjust rewriteServer
          (payloadCancelServerFunction witness) $
          Map.adjust rewriteClient
            (payloadCancelClientFunction witness)
            (llvmFunctions module0)
      }
    rewriteClient function = function
      { llvmFunctionBlocks = Map.adjust
          (rewriteSelect (payloadCancelPayloadLabel witness) payloadChoiceCode)
          payloadBlockId $
          Map.adjust
            (rewriteSelect (payloadCancelCancelLabel witness) cancelChoiceCode)
            cancelBlockId
            (llvmFunctionBlocks function)
      }
    rewriteSelect label code blockValue = blockValue
      { llvmBlockOps =
          LLVMPayloadCancelSelect
            (unValueId (payloadCancelClientTransport witness))
            code
          : filter (not . isUnloweredSelect label) (llvmBlockOps blockValue)
      }
    isUnloweredSelect label operation = case operation of
      LLVMPoison description -> description == "unlowered-session-select:" <> label
      _ -> False
    rewriteServer function = function
      { llvmFunctionBlocks = Map.adjust rewriteOffer offerBlockId (llvmFunctionBlocks function) }
    rewriteOffer blockValue = blockValue
      { llvmBlockTerminator = LLVMPayloadCancelOffer
          (unValueId (payloadCancelServerTransport witness))
          payloadTargetId
          cancelTargetId
      }
    payloadBlockId = LLVMBlockId (unBlockId (payloadCancelClientPayloadSelectBlock witness))
    cancelBlockId = LLVMBlockId (unBlockId (payloadCancelClientCancelSelectBlock witness))
    offerBlockId = LLVMBlockId (unBlockId (payloadCancelServerOfferBlock witness))
    payloadTargetId = LLVMBlockId (unBlockId (payloadCancelPayloadTarget witness))
    cancelTargetId = LLVMBlockId (unBlockId (payloadCancelCancelTarget witness))
    contract0 = llvmArtifactContract base
    contract1 = contract0 { llvmContractTargetDigest = llvmModuleDigest module1 }
    artifact = base
      { llvmArtifactModule = module1
      , llvmArtifactText = renderLLVMModule module1
      , llvmArtifactContract = contract1
      }

phase0PayloadCancelChoiceLLVMVerificationContext
  :: PayloadCancelChoiceBundle
  -> LLVMVerificationContext
phase0PayloadCancelChoiceLLVMVerificationContext bundle = LLVMVerificationContext
  { llvmSystemsContext = payloadCancelChoiceContext bundle
  , llvmExpectedLanguageVersion = llvmTargetLanguageVersion phase0PayloadCancelChoiceLLVMTarget
  , llvmExpectedToolVersion = llvmTargetToolVersion phase0PayloadCancelChoiceLLVMTarget
  , llvmExpectedTargetTriple = llvmTargetTripleName phase0PayloadCancelChoiceLLVMTarget
  , llvmExpectedDataLayout = llvmTargetDataLayout phase0PayloadCancelChoiceLLVMTarget
  , llvmExpectedRuntimeABIDigest = llvmTargetRuntimeABIDigest phase0PayloadCancelChoiceLLVMTarget
  , llvmExpectedRuntimeABIProfile = llvmTargetRuntimeABIProfile phase0PayloadCancelChoiceLLVMTarget
  , llvmAuthorizedStrengthenings = mempty
  }

verifyPayloadCancelChoiceTranslation
  :: PayloadCancelChoiceBundle
  -> LLVMArtifact
  -> Either PayloadCancelChoiceLLVMError ()
verifyPayloadCancelChoiceTranslation bundle llvmArtifact = do
  mapLeft PayloadCancelChoiceSystemsError $ verifyPayloadCancelChoiceBundle bundle
  let systemsArtifact = payloadCancelChoiceArtifact bundle
      systemsProgram = systemsArtifactProgram systemsArtifact
      llvmModule = llvmArtifactModule llvmArtifact
      context = phase0PayloadCancelChoiceLLVMVerificationContext bundle
  forM_ (Map.toAscList (systemsProgramFunctions systemsProgram)) $
    \(functionName, systemsFunction) -> do
      llvmFunction <- lookupLLVMFunction llvmModule functionName
      let expectedParameters =
            [ LLVMParameter (unValueId valueId) LLVMPointerParameter
            | (valueId, SystemsValue { systemsValueRole = TransportHandle }) <-
                Map.toAscList (systemsFunctionValues systemsFunction)
            ]
      unless (llvmFunctionParameters llvmFunction == expectedParameters) $
        Left (PayloadCancelChoiceTransportParameterMismatch
          functionName (llvmFunctionParameters llvmFunction))
  verifyPayloadCancelChoiceLLVMWitness bundle llvmArtifact
  mapLeft PayloadCancelChoiceLLVMVerificationError $
    verifyLLVMEmissionWith
      lowerSystemsPayloadCancelChoice
      context
      systemsArtifact
      llvmArtifact

verifyPayloadCancelChoiceLLVMWitness
  :: PayloadCancelChoiceBundle
  -> LLVMArtifact
  -> Either PayloadCancelChoiceLLVMError ()
verifyPayloadCancelChoiceLLVMWitness bundle llvmArtifact = do
  let witness = payloadCancelChoiceWitness bundle
      moduleValue = llvmArtifactModule llvmArtifact
      clientName = payloadCancelClientFunction witness
      serverName = payloadCancelServerFunction witness
      payloadBlockId = LLVMBlockId (unBlockId (payloadCancelClientPayloadSelectBlock witness))
      cancelBlockId = LLVMBlockId (unBlockId (payloadCancelClientCancelSelectBlock witness))
      offerBlockId = LLVMBlockId (unBlockId (payloadCancelServerOfferBlock witness))
      payloadTargetId = LLVMBlockId (unBlockId (payloadCancelPayloadTarget witness))
      cancelTargetId = LLVMBlockId (unBlockId (payloadCancelCancelTarget witness))
      clientTransport = unValueId (payloadCancelClientTransport witness)
      serverTransport = unValueId (payloadCancelServerTransport witness)
  clientFunction <- lookupLLVMFunction moduleValue clientName
  payloadBlock <- lookupLLVMBlock clientName clientFunction payloadBlockId
  cancelBlock <- lookupLLVMBlock clientName clientFunction cancelBlockId
  verifySelect clientName payloadBlockId clientTransport payloadChoiceCode (llvmBlockOps payloadBlock)
  verifySelect clientName cancelBlockId clientTransport cancelChoiceCode (llvmBlockOps cancelBlock)

  serverFunction <- lookupLLVMFunction moduleValue serverName
  offerBlock <- lookupLLVMBlock serverName serverFunction offerBlockId
  unless
    (llvmBlockTerminator offerBlock ==
      LLVMPayloadCancelOffer serverTransport payloadTargetId cancelTargetId) $
    Left (PayloadCancelChoiceServerOfferMismatch
      serverName offerBlockId (llvmBlockTerminator offerBlock))

  case verifyFinalResponseReceiveWitness
      (payloadCancelChoicePredecessor bundle)
      llvmArtifact of
    Right () -> pure ()
    Left err -> Left (PayloadCancelChoiceFinalResponseRegression (Text.pack (show err)))

  let rendered = llvmArtifactText llvmArtifact
      payloadNeedle = "@phil_runtime_select_payload_cancel(ptr %"
        <> symbolish clientTransport <> ", i8 1)"
      cancelNeedle = "@phil_runtime_select_payload_cancel(ptr %"
        <> symbolish clientTransport <> ", i8 0)"
      receiveNeedle = "@phil_runtime_receive_payload_cancel(ptr %"
        <> symbolish serverTransport <> ")"
  unless (Text.isInfixOf payloadNeedle rendered
      && Text.isInfixOf cancelNeedle rendered
      && Text.isInfixOf receiveNeedle rendered) $
    Left (PayloadCancelChoiceRenderedCallMissing "payload/cancel")
  unless
    ( not (Text.isInfixOf "@phil_call_select_payload" rendered)
    && not (Text.isInfixOf "@phil_call_select_cancel" rendered)
    && not (Text.isInfixOf "@phil_call_receive_payload_cancel_label" rendered)
    ) $
    Left (PayloadCancelChoiceGenericCallDetected "payload/cancel")
  unless
    ( not (Text.isInfixOf "@phil_current_payload_cancel_choice" rendered)
    && not (Text.isInfixOf "@phil_current_session_label" rendered)
    && not (Text.isInfixOf "@phil_current_transport" rendered)
    ) $
    Left (PayloadCancelChoiceAmbientStateDetected "payload/cancel")
  unless (not (Text.isInfixOf "unlowered-session-select" rendered)) $
    Left (PayloadCancelChoicePoisonDetected "payload/cancel")
  where
    verifySelect functionName blockId transport code operations =
      case operations of
        LLVMPayloadCancelSelect actualTransport actualCode : _
          | actualTransport == transport && actualCode == code -> pure ()
        _ -> Left (PayloadCancelChoiceClientSelectMismatch
          functionName blockId operations)

verifyPhase0PayloadCancelChoiceLLVM :: Either PayloadCancelChoiceLLVMError ()
verifyPhase0PayloadCancelChoiceLLVM = do
  bundle <- mapLeft PayloadCancelChoiceSystemsError phase0PayloadCancelChoiceBundle
  artifact <- mapLeft PayloadCancelChoiceSystemsError phase0PayloadCancelChoiceLLVMArtifact
  verifyPayloadCancelChoiceTranslation bundle artifact

lookupLLVMFunction
  :: LLVMModule
  -> Text
  -> Either PayloadCancelChoiceLLVMError LLVMFunction
lookupLLVMFunction moduleValue functionName =
  case Map.lookup functionName (llvmFunctions moduleValue) of
    Nothing -> Left (PayloadCancelChoiceFunctionMissing functionName)
    Just value -> Right value

lookupLLVMBlock
  :: Text
  -> LLVMFunction
  -> LLVMBlockId
  -> Either PayloadCancelChoiceLLVMError LLVMBlock
lookupLLVMBlock functionName function blockId =
  case Map.lookup blockId (llvmFunctionBlocks function) of
    Nothing -> Left (PayloadCancelChoiceBlockMissing functionName blockId)
    Just value -> Right value

symbolish :: Text -> Text
symbolish = Text.map (\character -> if isSymbol character then character else '_')
  where
    isSymbol character =
      (character >= 'a' && character <= 'z')
        || (character >= 'A' && character <= 'Z')
        || (character >= '0' && character <= '9')

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
