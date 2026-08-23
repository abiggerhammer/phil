{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.BeginPolicyChoice
  ( BeginPolicyChoiceLLVMError (..)
  , beginPolicyChoiceABIDescriptor
  , phase0BeginPolicyChoiceLLVMTarget
  , phase0BeginPolicyChoiceLLVMArtifact
  , phase0BeginPolicyChoiceLLVMVerificationContext
  , lowerSystemsBeginPolicyChoice
  , verifyBeginPolicyReasonUseShape
  , verifyBeginPolicyChoiceLLVMWitness
  , verifyBeginPolicyChoiceTranslation
  , verifyPhase0BeginPolicyChoiceLLVM
  ) where

import Control.Monad (forM_, unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types (digestText, unDigest)
import Phil.LLVM.IR
import Phil.LLVM.Verify
import Phil.LLVM.VersionSessionChoice
  ( phase0VersionSessionChoiceLLVMTarget
  , lowerSystemsVersionSessionChoice
  , verifyVersionSessionChoiceLLVMWitness
  , versionSessionChoiceABIDescriptor
  )
import Phil.Systems.BeginPolicySessionChoice
import Phil.Systems.IR

data BeginPolicyChoiceLLVMError
  = BeginPolicyChoiceLLVMSystemsError BeginPolicySessionChoiceError
  | BeginPolicyChoiceLLVMVerificationError LLVMVerificationError
  | BeginPolicyChoiceLLVMFunctionMissing Text
  | BeginPolicyChoiceLLVMBlockMissing Text LLVMBlockId
  | BeginPolicyChoiceLLVMParameterMismatch Text [LLVMParameter]
  | BeginPolicyChoiceLLVMValidationMismatch Text LLVMBlockId LLVMTerminator
  | BeginPolicyChoiceLLVMServerRejectMismatch Text LLVMBlockId [LLVMOp]
  | BeginPolicyChoiceLLVMServerProceedMismatch Text LLVMBlockId [LLVMOp]
  | BeginPolicyChoiceLLVMClientOfferMismatch Text LLVMBlockId LLVMTerminator
  | BeginPolicyChoiceLLVMClientBindingMismatch Text LLVMBlockId [LLVMOp]
  | BeginPolicyChoiceLLVMReasonUseMismatch Text ValueId Int Int
  | BeginPolicyChoiceLLVMVersionRegression Text
  | BeginPolicyChoiceLLVMRenderedCallMissing Text
  | BeginPolicyChoiceLLVMGenericCallDetected Text
  | BeginPolicyChoiceLLVMAmbientStateDetected Text
  | BeginPolicyChoiceLLVMPoisonDetected Text
  | BeginPolicyChoiceLLVMUnresolvedControlDetected Text LLVMBlockId
  deriving (Eq, Show)

beginPolicyChoiceABIDescriptor :: Text
beginPolicyChoiceABIDescriptor = Text.unlines
  [ "phil-runtime/phase0/begin-policy-choice-v1"
  , "base-version-choice-abi-digest=" <> unDigest (digestText versionSessionChoiceABIDescriptor)
  , "target=" <> llvmTargetTripleName phase0VersionSessionChoiceLLVMTarget
  , "data-layout=" <> llvmTargetDataLayout phase0VersionSessionChoiceLLVMTarget
  , "policy-context=explicit-UploadServer-ptr-parameter"
  , "policy-context-ambient-lookup=forbidden"
  , "begin-record=exact-recognized-Begin-ptr"
  , "validate=phil_runtime_validate_begin_policy(ptr,ptr,ptr)->i1"
  , "validate-arg0=exact-policy-context"
  , "validate-arg1=exact-recognized-Begin"
  , "validate-out=pointer-to-i8-rejection-reason-slot"
  , "validate-true=accepted;reason-slot-not-observed"
  , "validate-false=rejected;reason-slot-initialized"
  , "validate-provider-obligation=return-true-iff-BeginPolicy-accepts;on-false-write-canonical-observable-reason"
  , "reason-physical-representation=i8-boundary-code"
  , "reason-observable-equivalence=exact-frozen-program-does-not-inspect-ValidationFailure[BeginPolicy]"
  , "reason-observation-gate=server-reason-exactly-one-forwarding-use;client-reason-zero-uses"
  , "reason-code-0x01=BeginPolicyRejected"
  , "reason-codes-other-than-0x01=reserved-v1"
  , "select-reject=phil_runtime_select_begin_policy_reject(ptr,i8)->void"
  , "select-proceed=phil_runtime_select_begin_policy_proceed(ptr)->void"
  , "receive=phil_runtime_receive_begin_policy_choice(ptr,ptr)->i1"
  , "receive-out=pointer-to-i8-rejection-reason-slot"
  , "receive-true=proceed;reason-slot-not-observed"
  , "receive-false=reject;reason-slot-initialized"
  , "wire-proceed=0x01"
  , "wire-reject=0x00 || reason-u8"
  , "wire-proceed-size=1-octet"
  , "wire-reject-size=2-octets"
  , "receive-tag-eof-reserved-or-truncated-reason=runtime-must-not-return-normally"
  , "receive-reject-reserved-reason=runtime-must-not-return-normally"
  , "select-write-failure=residual-runtime-assumption;source-select-has-no-failure-edge"
  , "validator-rich-diagnostics=runtime-local-not-protocol-data"
  , "outer-framing=not-defined-by-this-profile"
  , "ambient-choice-state=forbidden"
  , "ambient-policy-state=forbidden"
  , "ambient-rejection-state=forbidden"
  , "runtime-symbol-identity=physical-primitive-and-signature"
  , "pointer-strengthening=none-by-default"
  ]

phase0BeginPolicyChoiceLLVMTarget :: LLVMTargetProfile
phase0BeginPolicyChoiceLLVMTarget = phase0VersionSessionChoiceLLVMTarget
  { llvmTargetRuntimeABIDigest = digestText beginPolicyChoiceABIDescriptor
  , llvmTargetRuntimeABIProfile = "phil-runtime/phase0/begin-policy-choice-v1"
  }

phase0BeginPolicyChoiceLLVMArtifact
  :: Either BeginPolicySessionChoiceError LLVMArtifact
phase0BeginPolicyChoiceLLVMArtifact = do
  bundle <- phase0BeginPolicySessionChoiceBundle
  pure (lowerSystemsBeginPolicyChoice
    phase0BeginPolicyChoiceLLVMTarget
    (beginPolicySessionChoiceArtifact bundle))

lowerSystemsBeginPolicyChoice :: LLVMTargetProfile -> SystemsArtifact -> LLVMArtifact
lowerSystemsBeginPolicyChoice target systemsArtifact = artifact
  where
    base = lowerSystemsVersionSessionChoice target systemsArtifact
    witness = phase0BeginPolicySessionChoiceWitness
    module0 = llvmArtifactModule base
    module1 = module0
      { llvmFunctions = Map.adjust rewriteServer
          (beginPolicyServerFunction witness) $
          Map.adjust rewriteClient
            (beginPolicyClientFunction witness)
            (llvmFunctions module0)
      }

    rewriteServer function = function
      { llvmFunctionBlocks = Map.adjust rewriteCommit commitBlockId $
          Map.adjust rewriteReject rejectBlockId $
          Map.adjust rewriteProceed proceedBlockId (llvmFunctionBlocks function)
      }
    rewriteCommit blockValue =
      case beginPolicyRuntimeSite systemsArtifact witness of
        Nothing -> blockValue
        Just site -> blockValue
          { llvmBlockTerminator = LLVMBeginPolicyValidate
              site
              policyContext
              beginRecord
              serverReason
              proceedBlockId
              rejectBlockId
          }
    rewriteReject blockValue = blockValue
      { llvmBlockOps =
          [ LLVMBeginPolicyValidationReasonBinding serverReason
          , LLVMBeginPolicyRejectSelect serverTransport serverReason
          ] <> filter (not . isUnloweredSelect (beginPolicyRejectLabel witness))
            (llvmBlockOps blockValue)
      }
    rewriteProceed blockValue = blockValue
      { llvmBlockOps =
          LLVMBeginPolicyProceedSelect serverTransport
          : filter (not . isUnloweredSelect (beginPolicyProceedLabel witness))
              (llvmBlockOps blockValue)
      }

    rewriteClient function = function
      { llvmFunctionBlocks = Map.adjust rewriteClientOffer clientOfferBlockId $
          Map.adjust rewriteClientReject clientRejectBlockId
            (llvmFunctionBlocks function)
      }
    rewriteClientOffer blockValue = blockValue
      { llvmBlockTerminator = LLVMBeginPolicyChoiceOffer
          clientTransport
          clientReason
          clientProceedBlockId
          clientRejectBlockId
      }
    rewriteClientReject blockValue = blockValue
      { llvmBlockOps = LLVMBeginPolicyChoiceReasonBinding clientReason
          : llvmBlockOps blockValue
      }

    isUnloweredSelect label operation = case operation of
      LLVMPoison description -> description == "unlowered-session-select:" <> label
      _ -> False

    commitBlockId = LLVMBlockId (unBlockId (beginPolicyCommitBlock witness))
    rejectBlockId = LLVMBlockId (unBlockId (beginPolicyServerRejectBlock witness))
    proceedBlockId = LLVMBlockId (unBlockId (beginPolicyServerProceedBlock witness))
    clientOfferBlockId = LLVMBlockId (unBlockId (beginPolicyClientOfferBlock witness))
    clientRejectBlockId = LLVMBlockId (unBlockId (beginPolicyClientRejectTarget witness))
    clientProceedBlockId = LLVMBlockId (unBlockId (beginPolicyClientProceedTarget witness))
    policyContext = unValueId (beginPolicyPolicyContext witness)
    beginRecord = unValueId (beginPolicyBeginRecord witness)
    serverReason = unValueId (beginPolicyServerRejectReason witness)
    serverTransport = unValueId (beginPolicyServerTransport witness)
    clientReason = unValueId (beginPolicyClientRejectReason witness)
    clientTransport = unValueId (beginPolicyClientTransport witness)

    contract0 = llvmArtifactContract base
    contract1 = contract0 { llvmContractTargetDigest = llvmModuleDigest module1 }
    artifact = base
      { llvmArtifactModule = module1
      , llvmArtifactText = renderLLVMModule module1
      , llvmArtifactContract = contract1
      }

phase0BeginPolicyChoiceLLVMVerificationContext
  :: BeginPolicySessionChoiceBundle
  -> LLVMVerificationContext
phase0BeginPolicyChoiceLLVMVerificationContext bundle = LLVMVerificationContext
  { llvmSystemsContext = beginPolicySessionChoiceContext bundle
  , llvmExpectedLanguageVersion = llvmTargetLanguageVersion phase0BeginPolicyChoiceLLVMTarget
  , llvmExpectedToolVersion = llvmTargetToolVersion phase0BeginPolicyChoiceLLVMTarget
  , llvmExpectedTargetTriple = llvmTargetTripleName phase0BeginPolicyChoiceLLVMTarget
  , llvmExpectedDataLayout = llvmTargetDataLayout phase0BeginPolicyChoiceLLVMTarget
  , llvmExpectedRuntimeABIDigest = llvmTargetRuntimeABIDigest phase0BeginPolicyChoiceLLVMTarget
  , llvmExpectedRuntimeABIProfile = llvmTargetRuntimeABIProfile phase0BeginPolicyChoiceLLVMTarget
  , llvmAuthorizedStrengthenings = mempty
  }

verifyBeginPolicyReasonUseShape
  :: BeginPolicySessionChoiceBundle
  -> Either BeginPolicyChoiceLLVMError ()
verifyBeginPolicyReasonUseShape bundle = do
  let witness = beginPolicySessionChoiceWitness bundle
      program = systemsArtifactProgram (beginPolicySessionChoiceArtifact bundle)
      serverName = beginPolicyServerFunction witness
      clientName = beginPolicyClientFunction witness
      serverReason = beginPolicyServerRejectReason witness
      clientReason = beginPolicyClientRejectReason witness
  server <- lookupSystemsFunction program serverName
  client <- lookupSystemsFunction program clientName
  let serverUses = valueUseCount serverReason server
      clientUses = valueUseCount clientReason client
  unless (serverUses == 1) $
    Left (BeginPolicyChoiceLLVMReasonUseMismatch
      serverName serverReason 1 serverUses)
  unless (clientUses == 0) $
    Left (BeginPolicyChoiceLLVMReasonUseMismatch
      clientName clientReason 0 clientUses)

verifyBeginPolicyChoiceTranslation
  :: BeginPolicySessionChoiceBundle
  -> LLVMArtifact
  -> Either BeginPolicyChoiceLLVMError ()
verifyBeginPolicyChoiceTranslation bundle llvmArtifact = do
  mapLeft BeginPolicyChoiceLLVMSystemsError $
    verifyBeginPolicySessionChoiceBundle bundle
  verifyBeginPolicyReasonUseShape bundle
  let systemsArtifact = beginPolicySessionChoiceArtifact bundle
      systemsProgram = systemsArtifactProgram systemsArtifact
      moduleValue = llvmArtifactModule llvmArtifact
      context = phase0BeginPolicyChoiceLLVMVerificationContext bundle
  forM_ (Map.toAscList (systemsProgramFunctions systemsProgram)) $
    \(functionName, systemsFunction) -> do
      llvmFunction <- lookupLLVMFunction moduleValue functionName
      let expectedParameters =
            [ LLVMParameter (unValueId valueId) LLVMPointerParameter
            | (valueId, SystemsValue { systemsValueRole = role }) <-
                Map.toAscList (systemsFunctionValues systemsFunction)
            , role == TransportHandle || isRuntimeInput role
            ]
      unless (llvmFunctionParameters llvmFunction == expectedParameters) $
        Left (BeginPolicyChoiceLLVMParameterMismatch
          functionName (llvmFunctionParameters llvmFunction))
  verifyBeginPolicyChoiceLLVMWitness bundle llvmArtifact
  mapLeft BeginPolicyChoiceLLVMVerificationError $
    verifyLLVMEmissionWith
      lowerSystemsBeginPolicyChoice
      context
      systemsArtifact
      llvmArtifact
  where
    isRuntimeInput role = case role of
      RuntimeInput _ -> True
      _ -> False

verifyBeginPolicyChoiceLLVMWitness
  :: BeginPolicySessionChoiceBundle
  -> LLVMArtifact
  -> Either BeginPolicyChoiceLLVMError ()
verifyBeginPolicyChoiceLLVMWitness bundle llvmArtifact = do
  let witness = beginPolicySessionChoiceWitness bundle
      systemsArtifact = beginPolicySessionChoiceArtifact bundle
      moduleValue = llvmArtifactModule llvmArtifact
      serverName = beginPolicyServerFunction witness
      clientName = beginPolicyClientFunction witness
      commitId = LLVMBlockId (unBlockId (beginPolicyCommitBlock witness))
      rejectId = LLVMBlockId (unBlockId (beginPolicyServerRejectBlock witness))
      proceedId = LLVMBlockId (unBlockId (beginPolicyServerProceedBlock witness))
      clientOfferId = LLVMBlockId (unBlockId (beginPolicyClientOfferBlock witness))
      clientRejectId = LLVMBlockId (unBlockId (beginPolicyClientRejectTarget witness))
      clientProceedId = LLVMBlockId (unBlockId (beginPolicyClientProceedTarget witness))
      serverTransport = unValueId (beginPolicyServerTransport witness)
      clientTransport = unValueId (beginPolicyClientTransport witness)
      policyContext = unValueId (beginPolicyPolicyContext witness)
      beginRecord = unValueId (beginPolicyBeginRecord witness)
      serverReason = unValueId (beginPolicyServerRejectReason witness)
      clientReason = unValueId (beginPolicyClientRejectReason witness)

  site <- case beginPolicyRuntimeSite systemsArtifact witness of
    Nothing -> Left (BeginPolicyChoiceLLVMValidationMismatch
      serverName commitId (LLVMUnreachable Nothing))
    Just value -> Right value

  server <- lookupLLVMFunction moduleValue serverName
  commitBlock <- lookupLLVMBlock serverName server commitId
  unless (llvmBlockTerminator commitBlock == LLVMBeginPolicyValidate
      site policyContext beginRecord serverReason proceedId rejectId) $
    Left (BeginPolicyChoiceLLVMValidationMismatch
      serverName commitId (llvmBlockTerminator commitBlock))

  rejectBlock <- lookupLLVMBlock serverName server rejectId
  unless
    ( LLVMBeginPolicyValidationReasonBinding serverReason `elem` llvmBlockOps rejectBlock
    && LLVMBeginPolicyRejectSelect serverTransport serverReason `elem` llvmBlockOps rejectBlock
    ) $
    Left (BeginPolicyChoiceLLVMServerRejectMismatch
      serverName rejectId (llvmBlockOps rejectBlock))

  proceedBlock <- lookupLLVMBlock serverName server proceedId
  unless (LLVMBeginPolicyProceedSelect serverTransport `elem` llvmBlockOps proceedBlock) $
    Left (BeginPolicyChoiceLLVMServerProceedMismatch
      serverName proceedId (llvmBlockOps proceedBlock))

  client <- lookupLLVMFunction moduleValue clientName
  clientOffer <- lookupLLVMBlock clientName client clientOfferId
  unless (llvmBlockTerminator clientOffer == LLVMBeginPolicyChoiceOffer
      clientTransport clientReason clientProceedId clientRejectId) $
    Left (BeginPolicyChoiceLLVMClientOfferMismatch
      clientName clientOfferId (llvmBlockTerminator clientOffer))
  clientReject <- lookupLLVMBlock clientName client clientRejectId
  unless (LLVMBeginPolicyChoiceReasonBinding clientReason `elem` llvmBlockOps clientReject) $
    Left (BeginPolicyChoiceLLVMClientBindingMismatch
      clientName clientRejectId (llvmBlockOps clientReject))

  case verifyVersionSessionChoiceLLVMWitness
      (beginPolicySessionChoicePredecessor bundle) llvmArtifact of
    Right () -> pure ()
    Left err -> Left (BeginPolicyChoiceLLVMVersionRegression (Text.pack (show err)))

  let rendered = llvmArtifactText llvmArtifact
      requiredCalls =
        [ "declare i1 @phil_runtime_validate_begin_policy(ptr, ptr, ptr)"
        , "declare void @phil_runtime_select_begin_policy_reject(ptr, i8)"
        , "declare void @phil_runtime_select_begin_policy_proceed(ptr)"
        , "declare i1 @phil_runtime_receive_begin_policy_choice(ptr, ptr)"
        ]
  forM_ requiredCalls $ \needle ->
    unless (Text.isInfixOf needle rendered) $
      Left (BeginPolicyChoiceLLVMRenderedCallMissing needle)
  forM_
    [ "@phil_call_select_reject"
    , "@phil_call_select_proceed"
    , "@phil_runtime_validate_BeginPolicy()"
    , "receive proceed/reject label"
    ] $ \needle ->
      unless (not (Text.isInfixOf needle rendered)) $
        Left (BeginPolicyChoiceLLVMGenericCallDetected needle)
  forM_
    [ "current_policy"
    , "current_begin"
    , "current_begin_policy_reason"
    , "last_begin_policy_reason"
    ] $ \needle ->
      unless (not (Text.isInfixOf needle rendered)) $
        Left (BeginPolicyChoiceLLVMAmbientStateDetected needle)
  forM_
    [ "unlowered-session-select:reject"
    , "unlowered-session-select:proceed"
    ] $ \needle ->
      unless (not (Text.isInfixOf needle rendered)) $
        Left (BeginPolicyChoiceLLVMPoisonDetected needle)

  forM_ (Map.toAscList (llvmFunctions moduleValue)) $ \(functionName, functionValue) ->
    forM_ (Map.toAscList (llvmFunctionBlocks functionValue)) $ \(blockId, blockValue) ->
      case llvmBlockTerminator blockValue of
        LLVMUnreachable Nothing ->
          Left (BeginPolicyChoiceLLVMUnresolvedControlDetected functionName blockId)
        _ -> pure ()

verifyPhase0BeginPolicyChoiceLLVM :: Either BeginPolicyChoiceLLVMError ()
verifyPhase0BeginPolicyChoiceLLVM = do
  bundle <- mapLeft BeginPolicyChoiceLLVMSystemsError phase0BeginPolicySessionChoiceBundle
  let artifact = lowerSystemsBeginPolicyChoice
        phase0BeginPolicyChoiceLLVMTarget
        (beginPolicySessionChoiceArtifact bundle)
  verifyBeginPolicyChoiceTranslation bundle artifact

valueUseCount :: ValueId -> SystemsFunction -> Int
valueUseCount valueId functionValue = sum
  [ sum (map (operationUseCount valueId) (systemsBlockOps blockValue))
      + terminatorUseCount valueId (systemsBlockTerminator blockValue)
  | blockValue <- Map.elems (systemsFunctionBlocks functionValue)
  ]

operationUseCount :: ValueId -> SystemsOp -> Int
operationUseCount valueId operation = length (filter (== valueId) inputs)
  where
    inputs = case operation of
      OpReceiveFrame { receiveTransport = transport } -> [transport]
      OpBorrowView { borrowOwner = owner } -> [owner]
      OpCommitIngress { commitPending = pending, commitTransport = transport } ->
        [pending, transport]
      OpDestroyPending { destroyPending = pending, destroyFrameOwner = owner } ->
        [pending, owner]
      OpReleaseOwner { releaseOwner = owner } -> [owner]
      OpCleanupPartial { cleanupOwner = owner } -> [owner]
      OpRuntimeCall { runtimeCallInputs = runtimeInputs } -> runtimeInputs
      OpSessionSelect { sessionSelectTransport = transport, sessionSelectPayload = payload } ->
        transport : maybe [] pure payload
      OpCopy { copySource = source } -> [source]
      OpEraseFact {} -> []
      OpDiagnostic {} -> []
      OpScalarLiteral {} -> []
      OpTraceEvent {} -> []

terminatorUseCount :: ValueId -> SystemsTerminator -> Int
terminatorUseCount valueId terminator = length (filter (== valueId) inputs)
  where
    inputs = case terminator of
      TermJump {} -> []
      TermBranch condition _ _ -> [condition]
      TermRecognize { recognizePending = pending, recognizeRawView = rawView } ->
        [pending, rawView]
      TermRuntimeCheck { checkInputs = checkValues } -> checkValues
      TermReceiveExact { exactTransport = transport, exactLength = lengthValue } ->
        [transport, lengthValue]
      TermSendExact { sendExactTransport = transport, sendExactOwner = owner } ->
        [transport, owner]
      TermStore { storeOwner = owner } -> [owner]
      TermSessionOffer { sessionOfferTransport = transport } -> [transport]
      TermRuntimeChoice { runtimeChoiceInputs = choiceInputs } -> choiceInputs
      TermReturnScalar result -> [result]
      TermEnd {} -> []
      TermFatal {} -> []

beginPolicyRuntimeSite
  :: SystemsArtifact
  -> BeginPolicySessionChoiceWitness
  -> Maybe RuntimeSiteRef
beginPolicyRuntimeSite artifact witness = do
  functionValue <- Map.lookup
    (beginPolicyServerFunction witness)
    (systemsProgramFunctions (systemsArtifactProgram artifact))
  blockValue <- Map.lookup
    (beginPolicyCommitBlock witness)
    (systemsFunctionBlocks functionValue)
  case systemsBlockTerminator blockValue of
    TermRuntimeChoice name inputs (Just site) _
      | name == beginPolicyRuntimeChoiceName witness
          && inputs == [beginPolicyPolicyContext witness, beginPolicyBeginRecord witness]
          && runtimeSiteKind site == ValidationBoundary "BeginPolicy" -> Just site
    _ -> Nothing

lookupSystemsFunction
  :: SystemsProgram
  -> Text
  -> Either BeginPolicyChoiceLLVMError SystemsFunction
lookupSystemsFunction program functionName =
  case Map.lookup functionName (systemsProgramFunctions program) of
    Nothing -> Left (BeginPolicyChoiceLLVMFunctionMissing functionName)
    Just functionValue -> Right functionValue

lookupLLVMFunction
  :: LLVMModule
  -> Text
  -> Either BeginPolicyChoiceLLVMError LLVMFunction
lookupLLVMFunction moduleValue functionName =
  case Map.lookup functionName (llvmFunctions moduleValue) of
    Nothing -> Left (BeginPolicyChoiceLLVMFunctionMissing functionName)
    Just functionValue -> Right functionValue

lookupLLVMBlock
  :: Text
  -> LLVMFunction
  -> LLVMBlockId
  -> Either BeginPolicyChoiceLLVMError LLVMBlock
lookupLLVMBlock functionName functionValue blockId =
  case Map.lookup blockId (llvmFunctionBlocks functionValue) of
    Nothing -> Left (BeginPolicyChoiceLLVMBlockMissing functionName blockId)
    Just blockValue -> Right blockValue

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
