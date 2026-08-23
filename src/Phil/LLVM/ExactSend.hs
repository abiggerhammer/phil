{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.ExactSend
  ( ExactSendLLVMError (..)
  , exactSendABIDescriptor
  , phase0ExactSendLLVMTarget
  , phase0ExactSendLLVMArtifact
  , phase0ExactSendLLVMVerificationContext
  , lowerSystemsExactSend
  , verifyExactSendLLVMWitness
  , verifyExactSendTranslation
  , verifyPhase0ExactSendLLVM
  ) where

import Control.Monad (forM_, unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types (digestText, unDigest)
import Phil.LLVM.HelloPolicyValidation
  ( helloPolicyValidationABIDescriptor
  , lowerSystemsHelloPolicyValidation
  , phase0HelloPolicyValidationLLVMTarget
  , verifyHelloPolicyValidationLLVMWitness
  )
import Phil.LLVM.IR
import Phil.LLVM.Verify
import Phil.Systems.HelloPolicyValidation
import Phil.Systems.IR

data ExactSendLLVMError
  = ExactSendSystemsError HelloPolicyValidationError
  | ExactSendLLVMVerificationError LLVMVerificationError
  | ExactSendSystemsFunctionMissing Text
  | ExactSendSystemsBlockMissing Text BlockId
  | ExactSendSystemsPayloadMissing Text ValueId
  | ExactSendSystemsPayloadRoleMismatch Text ValueId SystemsValueRole
  | ExactSendSystemsCallMismatch Text BlockId [SystemsOp]
  | ExactSendLLVMFunctionMissing Text
  | ExactSendLLVMBlockMissing Text LLVMBlockId
  | ExactSendLLVMParameterMismatch Text [LLVMParameter]
  | ExactSendLLVMOperationMismatch Text LLVMBlockId [LLVMOp]
  | ExactSendLLVMHelloPolicyRegression Text
  | ExactSendLLVMRenderedCallMissing Text
  | ExactSendLLVMGenericCallDetected Text
  | ExactSendLLVMAmbientStateDetected Text
  | ExactSendLLVMPoisonDetected Text
  | ExactSendLLVMUnresolvedControlDetected Text LLVMBlockId
  deriving (Eq, Show)

clientFunctionName :: Text
clientFunctionName = "UploadClient"

clientSendBlock :: BlockId
clientSendBlock = BlockId "client.payload"

clientTransport :: ValueId
clientTransport = ValueId "client.transport"

clientPayload :: ValueId
clientPayload = ValueId "client.payload"

-- LLVM parameters, instructions, and basic blocks share one function-local
-- namespace. The source payload identity `client.payload` therefore cannot be
-- rendered literally as an argument because the source block `client.payload`
-- already renders as the label `client_payload`. Use the same explicit `.owner`
-- target-name convention as exact receive, while the verifier below binds it
-- back to the exact Systems `client.payload` identity.
clientPayloadTarget :: Text
clientPayloadTarget = unValueId clientPayload <> ".owner"

exactSendCallName :: Text
exactSendCallName = "send_exact"

exactSendABIDescriptor :: Text
exactSendABIDescriptor = Text.unlines
  [ "phil-runtime/phase0/transport-exact-send-v1"
  , "base-hello-policy-abi-digest=" <> unDigest (digestText helloPolicyValidationABIDescriptor)
  , "target=" <> llvmTargetTripleName phase0HelloPolicyValidationLLVMTarget
  , "data-layout=" <> llvmTargetDataLayout phase0HelloPolicyValidationLLVMTarget
  , "client-transport=existing-UploadClient-ptr-parameter"
  , "client-payload=appended-UploadClient-owned-buffer-ptr-parameter"
  , "payload-role=exact-existing-OwnedBuffer-client.payload"
  , "payload-target-ssa=client.payload.owner"
  , "payload-source-target-relation=client.payload->client.payload.owner"
  , "send=phil_runtime_send_exact(ptr,ptr)->void"
  , "send-arg0=exact-client-transport"
  , "send-arg1=exact-client-payload-owner-handle"
  , "send-semantics=return-only-after-entire-buffer-accepted-by-runtime-send-mechanism"
  , "send-failure=must-not-return-normally;source-has-no-failure-continuation"
  , "payload-ownership=consumed-on-normal-return"
  , "payload-copy=none-required-by-translation"
  , "payload-layout=opaque-runtime-owned-buffer-handle"
  , "ambient-transport=forbidden"
  , "ambient-payload=forbidden"
  , "outer-framing=not-defined-by-this-profile"
  , "socket-buffering-and-durability=outside-this-profile"
  , "runtime-symbol-identity=physical-primitive-and-signature"
  , "pointer-strengthening=none-by-default"
  ]

phase0ExactSendLLVMTarget :: LLVMTargetProfile
phase0ExactSendLLVMTarget = phase0HelloPolicyValidationLLVMTarget
  { llvmTargetRuntimeABIDigest = digestText exactSendABIDescriptor
  , llvmTargetRuntimeABIProfile = "phil-runtime/phase0/transport-exact-send-v1"
  }

phase0ExactSendLLVMArtifact :: Either HelloPolicyValidationError LLVMArtifact
phase0ExactSendLLVMArtifact = do
  bundle <- phase0HelloPolicyValidationBundle
  pure (lowerSystemsExactSend
    phase0ExactSendLLVMTarget
    (helloPolicyValidationArtifact bundle))

lowerSystemsExactSend :: LLVMTargetProfile -> SystemsArtifact -> LLVMArtifact
lowerSystemsExactSend target systemsArtifact = artifact
  where
    base = lowerSystemsHelloPolicyValidation target systemsArtifact
    module0 = llvmArtifactModule base
    module1 = module0
      { llvmFunctions = Map.adjust rewriteClient clientFunctionName (llvmFunctions module0) }

    rewriteClient function = function
      { llvmFunctionParameters = appendPayloadParameter (llvmFunctionParameters function)
      , llvmFunctionBlocks = Map.adjust rewriteSendBlock
          (LLVMBlockId (unBlockId clientSendBlock))
          (llvmFunctionBlocks function)
      }

    appendPayloadParameter parameters =
      let payloadParameter = LLVMParameter clientPayloadTarget LLVMPointerParameter
      in if payloadParameter `elem` parameters then parameters else parameters <> [payloadParameter]

    rewriteSendBlock blockValue = blockValue
      { llvmBlockOps = map rewriteOperation (llvmBlockOps blockValue) }

    rewriteOperation operation = case operation of
      LLVMRuntime site name
        | name == exactSendCallName
        , runtimeSiteKind site == ExactSendBoundary ->
            LLVMExactSend site (unValueId clientTransport) clientPayloadTarget
      _ -> operation

    contract0 = llvmArtifactContract base
    contract1 = contract0 { llvmContractTargetDigest = llvmModuleDigest module1 }
    artifact = base
      { llvmArtifactModule = module1
      , llvmArtifactText = renderLLVMModule module1
      , llvmArtifactContract = contract1
      }

phase0ExactSendLLVMVerificationContext
  :: HelloPolicyValidationBundle
  -> LLVMVerificationContext
phase0ExactSendLLVMVerificationContext bundle = LLVMVerificationContext
  { llvmSystemsContext = helloPolicyValidationContext bundle
  , llvmExpectedLanguageVersion = llvmTargetLanguageVersion phase0ExactSendLLVMTarget
  , llvmExpectedToolVersion = llvmTargetToolVersion phase0ExactSendLLVMTarget
  , llvmExpectedTargetTriple = llvmTargetTripleName phase0ExactSendLLVMTarget
  , llvmExpectedDataLayout = llvmTargetDataLayout phase0ExactSendLLVMTarget
  , llvmExpectedRuntimeABIDigest = llvmTargetRuntimeABIDigest phase0ExactSendLLVMTarget
  , llvmExpectedRuntimeABIProfile = llvmTargetRuntimeABIProfile phase0ExactSendLLVMTarget
  , llvmAuthorizedStrengthenings = mempty
  }

verifyExactSendTranslation
  :: HelloPolicyValidationBundle
  -> LLVMArtifact
  -> Either ExactSendLLVMError ()
verifyExactSendTranslation bundle llvmArtifact = do
  mapLeft ExactSendSystemsError (verifyHelloPolicyValidationBundle bundle)
  verifyExactSendLLVMWitness bundle llvmArtifact
  mapLeft ExactSendLLVMVerificationError $
    verifyLLVMEmissionWith
      lowerSystemsExactSend
      (phase0ExactSendLLVMVerificationContext bundle)
      (helloPolicyValidationArtifact bundle)
      llvmArtifact

verifyExactSendLLVMWitness
  :: HelloPolicyValidationBundle
  -> LLVMArtifact
  -> Either ExactSendLLVMError ()
verifyExactSendLLVMWitness bundle llvmArtifact = do
  let systemsArtifact = helloPolicyValidationArtifact bundle
      systemsProgram = systemsArtifactProgram systemsArtifact
      moduleValue = llvmArtifactModule llvmArtifact

  systemsClient <- lookupSystemsFunction systemsProgram clientFunctionName
  payloadValue <- case Map.lookup clientPayload (systemsFunctionValues systemsClient) of
    Nothing -> Left (ExactSendSystemsPayloadMissing clientFunctionName clientPayload)
    Just value -> Right value
  case systemsValueRole payloadValue of
    OwnedBuffer _ -> pure ()
    role -> Left (ExactSendSystemsPayloadRoleMismatch clientFunctionName clientPayload role)

  sourceBlock <- case Map.lookup clientSendBlock (systemsFunctionBlocks systemsClient) of
    Nothing -> Left (ExactSendSystemsBlockMissing clientFunctionName clientSendBlock)
    Just value -> Right value
  let exactCalls =
        [ (site, decision)
        | OpRuntimeCall name inputs outputs (Just site) decision <- systemsBlockOps sourceBlock
        , name == exactSendCallName
        , inputs == [clientTransport, clientPayload]
        , null outputs
        , runtimeSiteKind site == ExactSendBoundary
        ]
  site <- case exactCalls of
    [(value, _)] -> Right value
    _ -> Left (ExactSendSystemsCallMismatch clientFunctionName clientSendBlock (systemsBlockOps sourceBlock))

  llvmClient <- lookupLLVMFunction moduleValue clientFunctionName
  let baseParameters =
        [ LLVMParameter (unValueId valueId) LLVMPointerParameter
        | (valueId, SystemsValue { systemsValueRole = role }) <-
            Map.toAscList (systemsFunctionValues systemsClient)
        , role == TransportHandle || isRuntimeInput role
        ]
      expectedParameters = baseParameters <>
        [LLVMParameter clientPayloadTarget LLVMPointerParameter]
  unless (llvmFunctionParameters llvmClient == expectedParameters) $
    Left (ExactSendLLVMParameterMismatch clientFunctionName (llvmFunctionParameters llvmClient))

  let blockId = LLVMBlockId (unBlockId clientSendBlock)
  llvmBlock <- lookupLLVMBlock clientFunctionName llvmClient blockId
  let matching =
        [ operation
        | operation@(LLVMExactSend opSite transport payload) <- llvmBlockOps llvmBlock
        , opSite == site
        , transport == unValueId clientTransport
        , payload == clientPayloadTarget
        ]
      generic =
        [ operation
        | operation@(LLVMRuntime opSite name) <- llvmBlockOps llvmBlock
        , opSite == site || name == exactSendCallName
        ]
  unless (matching == [LLVMExactSend site (unValueId clientTransport) clientPayloadTarget]
      && null generic) $
    Left (ExactSendLLVMOperationMismatch clientFunctionName blockId (llvmBlockOps llvmBlock))

  case verifyHelloPolicyValidationLLVMWitness bundle llvmArtifact of
    Right () -> pure ()
    Left err -> Left (ExactSendLLVMHelloPolicyRegression (Text.pack (show err)))

  let rendered = llvmArtifactText llvmArtifact
  unless (Text.isInfixOf "declare void @phil_runtime_send_exact(ptr, ptr)" rendered) $
    Left (ExactSendLLVMRenderedCallMissing "declare void @phil_runtime_send_exact(ptr, ptr)")
  unless (Text.isInfixOf
      "call void @phil_runtime_send_exact(ptr %client_transport, ptr %client_payload_owner)"
      rendered) $
    Left (ExactSendLLVMRenderedCallMissing "exact send call")

  forM_
    [ "declare i1 @phil_runtime_send_exact()"
    , "@phil_call_send_exact"
    ] $ \needle ->
      unless (not (Text.isInfixOf needle rendered)) $
        Left (ExactSendLLVMGenericCallDetected needle)

  forM_
    [ "current_transport"
    , "current_payload"
    , "pending_send_payload"
    ] $ \needle ->
      unless (not (Text.isInfixOf needle rendered)) $
        Left (ExactSendLLVMAmbientStateDetected needle)

  forM_ (Map.toAscList (llvmFunctions moduleValue)) $ \(functionName, functionValue) ->
    forM_ (Map.toAscList (llvmFunctionBlocks functionValue)) $ \(candidateBlockId, blockValue) -> do
      forM_ (llvmBlockOps blockValue) $ \operation -> case operation of
        LLVMPoison description -> Left (ExactSendLLVMPoisonDetected description)
        _ -> pure ()
      case llvmBlockTerminator blockValue of
        LLVMUnreachable Nothing ->
          Left (ExactSendLLVMUnresolvedControlDetected functionName candidateBlockId)
        _ -> pure ()
  where
    isRuntimeInput role = case role of
      RuntimeInput _ -> True
      _ -> False

verifyPhase0ExactSendLLVM :: Either ExactSendLLVMError ()
verifyPhase0ExactSendLLVM = do
  bundle <- mapLeft ExactSendSystemsError phase0HelloPolicyValidationBundle
  let artifact = lowerSystemsExactSend
        phase0ExactSendLLVMTarget
        (helloPolicyValidationArtifact bundle)
  verifyExactSendTranslation bundle artifact

lookupSystemsFunction
  :: SystemsProgram
  -> Text
  -> Either ExactSendLLVMError SystemsFunction
lookupSystemsFunction program functionName =
  case Map.lookup functionName (systemsProgramFunctions program) of
    Nothing -> Left (ExactSendSystemsFunctionMissing functionName)
    Just value -> Right value

lookupLLVMFunction
  :: LLVMModule
  -> Text
  -> Either ExactSendLLVMError LLVMFunction
lookupLLVMFunction moduleValue functionName =
  case Map.lookup functionName (llvmFunctions moduleValue) of
    Nothing -> Left (ExactSendLLVMFunctionMissing functionName)
    Just value -> Right value

lookupLLVMBlock
  :: Text
  -> LLVMFunction
  -> LLVMBlockId
  -> Either ExactSendLLVMError LLVMBlock
lookupLLVMBlock functionName functionValue blockId =
  case Map.lookup blockId (llvmFunctionBlocks functionValue) of
    Nothing -> Left (ExactSendLLVMBlockMissing functionName blockId)
    Just value -> Right value

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
