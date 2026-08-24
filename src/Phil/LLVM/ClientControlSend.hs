{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.ClientControlSend
  ( ClientControlSendLLVMError (..)
  , clientControlSendABIDescriptor
  , phase0ClientControlSendLLVMTarget
  , phase0ClientControlSendLLVMArtifact
  , phase0ClientControlSendLLVMVerificationContext
  , lowerSystemsClientControlSend
  , verifyClientControlSendLLVMWitness
  , verifyClientControlSendTranslation
  , verifyPhase0ClientControlSendLLVM
  ) where

import Control.Monad (forM_, unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types (digestText, unDigest)
import Phil.Core.Scalar (ScalarType (..))
import Phil.LLVM.ExactSend
  ( exactSendABIDescriptor
  , lowerSystemsExactSend
  , phase0ExactSendLLVMTarget
  )
import Phil.LLVM.IR
import Phil.LLVM.Verify
import Phil.Systems.ClientOutbound
import Phil.Systems.IR
import Phil.Systems.VersionSessionChoice

data ClientControlSendLLVMError
  = ClientControlSendSystemsError ClientOutboundError
  | ClientControlSendLLVMVerificationError LLVMVerificationError
  | ClientControlSendSystemsFunctionMissing Text
  | ClientControlSendSystemsBlockMissing Text BlockId
  | ClientControlSendLLVMFunctionMissing Text
  | ClientControlSendLLVMBlockMissing Text LLVMBlockId
  | ClientControlSendLLVMParameterMismatch Text [LLVMParameter]
  | ClientControlSendLLVMEntryMismatch [LLVMOp]
  | ClientControlSendLLVMVersionMismatch [LLVMOp]
  | ClientControlSendLLVMRefinementMismatch LLVMTerminator
  | ClientControlSendLLVMVersionBindingMissing [LLVMOp]
  | ClientControlSendLLVMExactSendMismatch [LLVMOp]
  | ClientControlSendLLVMRenderedCallMissing Text
  | ClientControlSendLLVMGenericCallDetected Text
  | ClientControlSendLLVMAmbientStateDetected Text
  | ClientControlSendLLVMRecordResidueDetected Text
  | ClientControlSendLLVMPoisonDetected Text
  | ClientControlSendLLVMUnresolvedControlDetected Text LLVMBlockId
  deriving (Eq, Show)

clientFunctionName :: Text
clientFunctionName = "UploadClient"

clientPayload :: ValueId
clientPayload = ValueId "client.payload"

clientPayloadTarget :: Text
clientPayloadTarget = unValueId clientPayload <> ".owner"

clientExactSendBlock :: BlockId
clientExactSendBlock = BlockId "client.payload"

clientControlSendABIDescriptor :: Text
clientControlSendABIDescriptor = Text.unlines
  [ "phil-runtime/phase0/client-control-send-v1"
  , "base-exact-send-abi-digest=" <> unDigest (digestText exactSendABIDescriptor)
  , "target=" <> llvmTargetTripleName phase0ExactSendLLVMTarget
  , "data-layout=" <> llvmTargetDataLayout phase0ExactSendLLVMTarget
  , "supported-versions=phil_runtime_supported_versions()->ptr"
  , "supported-versions-representation=opaque-provider-ptr"
  , "supported-versions-provider-obligation=exact-source-supported_versions-result-and-nonempty"
  , "supported-versions-lifetime=valid-through-version-refinement"
  , "hello-record-lowering=construct-Hello-plus-send-fused-into-serializer-send"
  , "hello-send=phil_runtime_send_hello(ptr,ptr)->void"
  , "hello-send-arg0=exact-client-transport"
  , "hello-send-arg1=exact-supported-versions-handle"
  , "hello-send-semantics=serialize-and-send-one-complete-Hello-frame-or-do-not-return-normally"
  , "hello-record-target-handle=none"
  , "payload-source-target-relation=client.payload->client.payload.owner"
  , "payload-view-lowering=erase-borrowed-view-to-same-payload-owner-handle"
  , "payload-length=phil_runtime_payload_length(ptr)->i64"
  , "payload-length-arg0=exact-client-payload-owner"
  , "payload-kind=phil_runtime_payload_kind(ptr)->ptr"
  , "payload-kind-representation=opaque-provider-ptr"
  , "payload-kind-arg0=exact-client-payload-owner"
  , "sha256=phil_runtime_sha256(ptr)->ptr"
  , "sha256-arg0=exact-client-payload-owner"
  , "sha256-result-representation=opaque-provider-ptr"
  , "sha256-provider-obligation=result-is-SHA256-of-exact-payload-bytes"
  , "begin-record-lowering=construct-Begin-plus-send-fused-into-serializer-send"
  , "begin-send=phil_runtime_send_begin_sha256(ptr,i64,ptr,ptr)->void"
  , "begin-send-arg0=exact-client-transport"
  , "begin-send-arg1=exact-client-payload-length"
  , "begin-send-arg2=exact-client-payload-kind-handle"
  , "begin-send-arg3=exact-client-declared-SHA256-digest-handle"
  , "begin-send-static-digest-alg=sha256"
  , "begin-send-semantics=serialize-and-send-one-complete-Begin-frame-or-do-not-return-normally"
  , "begin-record-target-handle=none"
  , "client-refine=phil_runtime_refine_selected_version_with_set(ptr,ptr,i16)->i1"
  , "client-refine-arg0=exact-client-transport"
  , "client-refine-arg1=same-supported-versions-handle-sent-in-Hello"
  , "client-refine-arg2=decoded-selected-version"
  , "client-refine-provider-obligation=true-iff-selected-version-is-member-of-explicit-set"
  , "ambient-offered-version-set=forbidden"
  , "ambient-transport=forbidden"
  , "ambient-Hello=forbidden"
  , "ambient-Begin=forbidden"
  , "ambient-payload=forbidden"
  , "concrete-Hello-Begin-byte-layout=runtime-provider-gate-not-selected-by-this-profile"
  , "runtime-provider-codec-obligation=implement-the-frozen-Hello-and-Begin-grammars-and-framing-contract"
  , "socket-buffering-and-durability=outside-this-profile"
  , "runtime-symbol-identity=physical-primitive-and-signature"
  , "pointer-strengthening=none-by-default"
  ]

phase0ClientControlSendLLVMTarget :: LLVMTargetProfile
phase0ClientControlSendLLVMTarget = phase0ExactSendLLVMTarget
  { llvmTargetRuntimeABIDigest = digestText clientControlSendABIDescriptor
  , llvmTargetRuntimeABIProfile = "phil-runtime/phase0/client-control-send-v1"
  }

phase0ClientControlSendLLVMArtifact :: Either ClientOutboundError LLVMArtifact
phase0ClientControlSendLLVMArtifact = do
  bundle <- phase0ClientOutboundBundle
  pure (lowerSystemsClientControlSend
    phase0ClientControlSendLLVMTarget
    (clientOutboundArtifact bundle))

lowerSystemsClientControlSend :: LLVMTargetProfile -> SystemsArtifact -> LLVMArtifact
lowerSystemsClientControlSend target systemsArtifact = artifact
  where
    base = lowerSystemsExactSend target systemsArtifact
    outbound = phase0ClientOutboundWitness
    versionChoice = phase0VersionSessionChoiceWitness
    module0 = llvmArtifactModule base
    module1 = module0
      { llvmFunctions = Map.adjust rewriteClient clientFunctionName (llvmFunctions module0) }

    rewriteClient function = function
      { llvmFunctionBlocks = Map.adjust rewriteEntry entryBlockId $
          Map.adjust rewriteVersion versionBlockId $
          Map.adjust rewriteRefinement refinementBlockId
            (llvmFunctionBlocks function)
      }

    rewriteEntry blockValue = blockValue
      { llvmBlockOps =
          [ LLVMClientSupportedVersions supportedVersions
          , LLVMClientSendHello clientTransport supportedVersions
          ]
      }

    rewriteVersion blockValue = blockValue
      { llvmBlockOps =
          [ LLVMClientSHA256 declaredDigest clientPayloadTarget
          , LLVMClientPayloadLength payloadLength clientPayloadTarget
          , LLVMClientPayloadKind payloadKind clientPayloadTarget
          , LLVMClientSendBegin clientTransport payloadLength payloadKind declaredDigest
          ]
      }

    rewriteRefinement blockValue = blockValue
      { llvmBlockTerminator = case llvmBlockTerminator blockValue of
          LLVMVersionRefinement site transport selected yes no ->
            LLVMVersionRefinementWithSet
              site transport supportedVersions selected yes no
          other -> other
      }

    entryBlockId = LLVMBlockId (unBlockId (clientOutboundEntryBlock outbound))
    versionBlockId = LLVMBlockId (unBlockId (clientOutboundVersionBlock outbound))
    refinementBlockId = LLVMBlockId (unBlockId (versionChoiceClientVersionTarget versionChoice))
    clientTransport = unValueId (clientOutboundTransport outbound)
    supportedVersions = unValueId (clientOutboundSupportedVersions outbound)
    payloadLength = unValueId (clientOutboundPayloadLength outbound)
    payloadKind = unValueId (clientOutboundPayloadKind outbound)
    declaredDigest = unValueId (clientOutboundDeclaredDigest outbound)

    contract0 = llvmArtifactContract base
    contract1 = contract0
      { llvmContractTargetDigest = llvmModuleDigest module1
      , llvmContractTraceRelation = llvmContractTraceRelation contract0 <>
          [ "client supported_versions() -> explicit opaque version-set handle -> fused Hello serializer/send"
          , "the same version-set handle sent in Hello -> explicit selected-version refinement input"
          , "client payload borrow -> same physical payload-owner handle -> SHA-256, length, and kind extraction"
          , "semantic Begin construction with static sha256 -> fused Begin serializer/send with exact length, kind, and digest operands"
          ]
      , llvmContractResourceFailureRelation = llvmContractResourceFailureRelation contract0 <>
          [ "Hello and Begin source sends expose no recoverable failure continuation; serializer/send primitives must not return normally on failure"
          ]
      }
    artifact = base
      { llvmArtifactModule = module1
      , llvmArtifactText = renderLLVMModule module1
      , llvmArtifactContract = contract1
      }

phase0ClientControlSendLLVMVerificationContext
  :: ClientOutboundBundle
  -> LLVMVerificationContext
phase0ClientControlSendLLVMVerificationContext bundle = LLVMVerificationContext
  { llvmSystemsContext = clientOutboundContext bundle
  , llvmExpectedLanguageVersion = llvmTargetLanguageVersion phase0ClientControlSendLLVMTarget
  , llvmExpectedToolVersion = llvmTargetToolVersion phase0ClientControlSendLLVMTarget
  , llvmExpectedTargetTriple = llvmTargetTripleName phase0ClientControlSendLLVMTarget
  , llvmExpectedDataLayout = llvmTargetDataLayout phase0ClientControlSendLLVMTarget
  , llvmExpectedRuntimeABIDigest = llvmTargetRuntimeABIDigest phase0ClientControlSendLLVMTarget
  , llvmExpectedRuntimeABIProfile = llvmTargetRuntimeABIProfile phase0ClientControlSendLLVMTarget
  , llvmAuthorizedStrengthenings = mempty
  }

verifyClientControlSendTranslation
  :: ClientOutboundBundle
  -> LLVMArtifact
  -> Either ClientControlSendLLVMError ()
verifyClientControlSendTranslation bundle llvmArtifact = do
  mapLeft ClientControlSendSystemsError (verifyClientOutboundBundle bundle)
  verifyClientControlSendLLVMWitness bundle llvmArtifact
  mapLeft ClientControlSendLLVMVerificationError $
    verifyLLVMEmissionWith
      lowerSystemsClientControlSend
      (phase0ClientControlSendLLVMVerificationContext bundle)
      (clientOutboundArtifact bundle)
      llvmArtifact

verifyClientControlSendLLVMWitness
  :: ClientOutboundBundle
  -> LLVMArtifact
  -> Either ClientControlSendLLVMError ()
verifyClientControlSendLLVMWitness bundle llvmArtifact = do
  let outbound = clientOutboundWitness bundle
      versionChoice = phase0VersionSessionChoiceWitness
      systemsArtifact = clientOutboundArtifact bundle
      systemsProgram = systemsArtifactProgram systemsArtifact
      moduleValue = llvmArtifactModule llvmArtifact
      transport = unValueId (clientOutboundTransport outbound)
      supportedVersions = unValueId (clientOutboundSupportedVersions outbound)
      payloadLength = unValueId (clientOutboundPayloadLength outbound)
      payloadKind = unValueId (clientOutboundPayloadKind outbound)
      declaredDigest = unValueId (clientOutboundDeclaredDigest outbound)
      selectedVersion = unValueId (versionChoiceClientSelectedVersion versionChoice)
      entryId = LLVMBlockId (unBlockId (clientOutboundEntryBlock outbound))
      versionId = LLVMBlockId (unBlockId (clientOutboundVersionBlock outbound))
      refinementId = LLVMBlockId (unBlockId (versionChoiceClientVersionTarget versionChoice))
      exactSendId = LLVMBlockId (unBlockId clientExactSendBlock)

  systemsClient <- lookupSystemsFunction systemsProgram clientFunctionName
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
    Left (ClientControlSendLLVMParameterMismatch
      clientFunctionName (llvmFunctionParameters llvmClient))

  entryBlock <- lookupLLVMBlock clientFunctionName llvmClient entryId
  let expectedEntry =
        [ LLVMClientSupportedVersions supportedVersions
        , LLVMClientSendHello transport supportedVersions
        ]
  unless (llvmBlockOps entryBlock == expectedEntry) $
    Left (ClientControlSendLLVMEntryMismatch (llvmBlockOps entryBlock))

  versionBlock <- lookupLLVMBlock clientFunctionName llvmClient versionId
  let expectedVersion =
        [ LLVMClientSHA256 declaredDigest clientPayloadTarget
        , LLVMClientPayloadLength payloadLength clientPayloadTarget
        , LLVMClientPayloadKind payloadKind clientPayloadTarget
        , LLVMClientSendBegin transport payloadLength payloadKind declaredDigest
        ]
  unless (llvmBlockOps versionBlock == expectedVersion) $
    Left (ClientControlSendLLVMVersionMismatch (llvmBlockOps versionBlock))

  refinementBlock <- lookupLLVMBlock clientFunctionName llvmClient refinementId
  unless (LLVMVersionChoicePayloadBinding selectedVersion `elem` llvmBlockOps refinementBlock) $
    Left (ClientControlSendLLVMVersionBindingMissing (llvmBlockOps refinementBlock))
  case llvmBlockTerminator refinementBlock of
    LLVMVersionRefinementWithSet _ actualTransport actualVersions actualSelected yes no
      | actualTransport == transport
          && actualVersions == supportedVersions
          && actualSelected == selectedVersion
          && yes == LLVMBlockId (unBlockId (versionChoiceClientVersionSuccess versionChoice))
          && no == LLVMBlockId (unBlockId (versionChoiceClientVersionFailure versionChoice)) -> pure ()
    other -> Left (ClientControlSendLLVMRefinementMismatch other)

  sourceExactSend <- lookupSystemsBlock systemsClient clientExactSendBlock
  exactSite <- case
    [ site
    | OpRuntimeCall name inputs outputs (Just site) _ <- systemsBlockOps sourceExactSend
    , name == "send_exact"
    , inputs == [clientOutboundTransport outbound, clientPayload]
    , null outputs
    , runtimeSiteKind site == ExactSendBoundary
    ] of
      [site] -> Right site
      _ -> Left (ClientControlSendSystemsBlockMissing clientFunctionName clientExactSendBlock)

  exactBlock <- lookupLLVMBlock clientFunctionName llvmClient exactSendId
  let expectedExact = LLVMExactSend exactSite transport clientPayloadTarget
      exactOps = [op | op@LLVMExactSend {} <- llvmBlockOps exactBlock]
  unless (exactOps == [expectedExact]) $
    Left (ClientControlSendLLVMExactSendMismatch (llvmBlockOps exactBlock))

  let rendered = llvmArtifactText llvmArtifact
      required =
        [ "declare ptr @phil_runtime_supported_versions()"
        , "declare i64 @phil_runtime_payload_length(ptr)"
        , "declare ptr @phil_runtime_payload_kind(ptr)"
        , "declare ptr @phil_runtime_sha256(ptr)"
        , "declare void @phil_runtime_send_hello(ptr, ptr)"
        , "declare void @phil_runtime_send_begin_sha256(ptr, i64, ptr, ptr)"
        , "declare i1 @phil_runtime_refine_selected_version_with_set(ptr, ptr, i16)"
        , "%client_supported_versions = call ptr @phil_runtime_supported_versions()"
        , "call void @phil_runtime_send_hello(ptr %client_transport, ptr %client_supported_versions)"
        , "%client_declared_digest = call ptr @phil_runtime_sha256(ptr %client_payload_owner)"
        , "%client_payload_length = call i64 @phil_runtime_payload_length(ptr %client_payload_owner)"
        , "%client_payload_kind = call ptr @phil_runtime_payload_kind(ptr %client_payload_owner)"
        , "call void @phil_runtime_send_begin_sha256(ptr %client_transport, i64 %client_payload_length, ptr %client_payload_kind, ptr %client_declared_digest)"
        , "@phil_runtime_refine_selected_version_with_set(ptr %client_transport, ptr %client_supported_versions, i16 %client_selected_version)"
        , "call void @phil_runtime_send_exact(ptr %client_transport, ptr %client_payload_owner)"
        ]
  forM_ required $ \needle ->
    unless (Text.isInfixOf needle rendered) $
      Left (ClientControlSendLLVMRenderedCallMissing needle)

  forM_
    [ "@phil_call_supported_versions"
    , "@phil_call_construct_Hello"
    , "@phil_call_send_Hello"
    , "@phil_call_sha256_payload"
    , "@phil_call_project_payload_length"
    , "@phil_call_project_payload_kind"
    , "@phil_call_construct_Begin_sha256_"
    , "@phil_call_send_Begin"
    , "declare i1 @phil_runtime_refine_selected_version(ptr, i16)"
    ] $ \needle ->
      unless (not (Text.isInfixOf needle rendered)) $
        Left (ClientControlSendLLVMGenericCallDetected needle)

  forM_
    [ "current_transport"
    , "current_hello"
    , "current_begin"
    , "current_payload"
    , "current_offered_versions"
    , "last_supported_versions"
    ] $ \needle ->
      unless (not (Text.isInfixOf needle rendered)) $
        Left (ClientControlSendLLVMAmbientStateDetected needle)

  forM_
    [ "%client_hello ="
    , "%client_begin ="
    , "%client_payload_view ="
    ] $ \needle ->
      unless (not (Text.isInfixOf needle rendered)) $
        Left (ClientControlSendLLVMRecordResidueDetected needle)

  forM_ (Map.toAscList (llvmFunctions moduleValue)) $ \(functionName, functionValue) ->
    forM_ (Map.toAscList (llvmFunctionBlocks functionValue)) $ \(blockId, blockValue) -> do
      forM_ (llvmBlockOps blockValue) $ \operation -> case operation of
        LLVMPoison description -> Left (ClientControlSendLLVMPoisonDetected description)
        _ -> pure ()
      case llvmBlockTerminator blockValue of
        LLVMUnreachable Nothing ->
          Left (ClientControlSendLLVMUnresolvedControlDetected functionName blockId)
        _ -> pure ()
  where
    isRuntimeInput role = case role of
      RuntimeInput _ -> True
      _ -> False

verifyPhase0ClientControlSendLLVM :: Either ClientControlSendLLVMError ()
verifyPhase0ClientControlSendLLVM = do
  bundle <- mapLeft ClientControlSendSystemsError phase0ClientOutboundBundle
  let artifact = lowerSystemsClientControlSend
        phase0ClientControlSendLLVMTarget
        (clientOutboundArtifact bundle)
  verifyClientControlSendTranslation bundle artifact

lookupSystemsFunction
  :: SystemsProgram
  -> Text
  -> Either ClientControlSendLLVMError SystemsFunction
lookupSystemsFunction program functionName =
  case Map.lookup functionName (systemsProgramFunctions program) of
    Nothing -> Left (ClientControlSendSystemsFunctionMissing functionName)
    Just value -> Right value

lookupSystemsBlock
  :: SystemsFunction
  -> BlockId
  -> Either ClientControlSendLLVMError SystemsBlock
lookupSystemsBlock function blockId =
  case Map.lookup blockId (systemsFunctionBlocks function) of
    Nothing -> Left (ClientControlSendSystemsBlockMissing
      (systemsFunctionName function) blockId)
    Just value -> Right value

lookupLLVMFunction
  :: LLVMModule
  -> Text
  -> Either ClientControlSendLLVMError LLVMFunction
lookupLLVMFunction moduleValue functionName =
  case Map.lookup functionName (llvmFunctions moduleValue) of
    Nothing -> Left (ClientControlSendLLVMFunctionMissing functionName)
    Just value -> Right value

lookupLLVMBlock
  :: Text
  -> LLVMFunction
  -> LLVMBlockId
  -> Either ClientControlSendLLVMError LLVMBlock
lookupLLVMBlock functionName function blockId =
  case Map.lookup blockId (llvmFunctionBlocks function) of
    Nothing -> Left (ClientControlSendLLVMBlockMissing functionName blockId)
    Just value -> Right value

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
