{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.BeginPolicySessionChoice
  ( BeginPolicySessionChoiceWitness (..)
  , BeginPolicySessionChoiceBundle (..)
  , BeginPolicySessionChoiceError (..)
  , phase0BeginPolicySessionChoiceWitness
  , phase0BeginPolicySessionChoiceBundle
  , verifyBeginPolicySessionChoiceBundle
  , verifyBeginPolicySessionChoiceWitness
  ) where

import Control.Monad (unless, when)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Assurance.Types
import Phil.Systems.Dataflow
import Phil.Systems.IR
import Phil.Systems.RecognizedRecord
import Phil.Systems.Verify
import Phil.Systems.VersionChoiceOperands

data BeginPolicySessionChoiceWitness = BeginPolicySessionChoiceWitness
  { beginPolicyServerFunction :: Text
  , beginPolicyServerTransport :: ValueId
  , beginPolicyCommitBlock :: BlockId
  , beginPolicyBeginRecord :: ValueId
  , beginPolicyPolicyContext :: ValueId
  , beginPolicyServerRejectReason :: ValueId
  , beginPolicyRuntimeChoiceName :: Text
  , beginPolicyAcceptedArm :: Text
  , beginPolicyRejectedArm :: Text
  , beginPolicyServerRejectBlock :: BlockId
  , beginPolicyServerProceedBlock :: BlockId
  , beginPolicyRejectLabel :: Text
  , beginPolicyProceedLabel :: Text
  , beginPolicyClientFunction :: Text
  , beginPolicyClientTransport :: ValueId
  , beginPolicyClientOfferBlock :: BlockId
  , beginPolicyClientRejectTarget :: BlockId
  , beginPolicyClientProceedTarget :: BlockId
  , beginPolicyClientRejectReason :: ValueId
  , beginPolicyClientLegacyDiscriminator :: ValueId
  , beginPolicyClientLegacyReceiveCall :: Text
  , beginPolicyLoweringDecision :: DecisionId
  }
  deriving (Eq, Show)

data BeginPolicySessionChoiceBundle = BeginPolicySessionChoiceBundle
  { beginPolicySessionChoiceArtifact :: SystemsArtifact
  , beginPolicySessionChoiceContext :: SystemsVerificationContext
  , beginPolicySessionChoicePredecessor :: VersionChoiceOperandsBundle
  , beginPolicySessionChoiceWitness :: BeginPolicySessionChoiceWitness
  }
  deriving (Eq, Show)

data BeginPolicySessionChoiceError
  = BeginPolicyPredecessorError VersionChoiceOperandsError
  | BeginPolicySystemsError SystemsVerificationError
  | BeginPolicyDataflowError ScalarDataflowError
  | BeginPolicyVersionRegression VersionChoiceOperandsError
  | BeginPolicyRecognizedRecordRegression RecognizedRecordError
  | BeginPolicyFunctionMissing Text
  | BeginPolicyBlockMissing Text BlockId
  | BeginPolicyValueMissing Text ValueId
  | BeginPolicyValueRoleMismatch Text ValueId SystemsValueRole
  | BeginPolicyUnexpectedValuePresent Text ValueId
  | BeginPolicyLegacyDiscriminatorPresent Text ValueId
  | BeginPolicyLegacyReceivePresent Text BlockId Text
  | BeginPolicyInputHasProducer Text ValueId
  | BeginPolicyRuntimeChoiceMismatch Text BlockId SystemsTerminator
  | BeginPolicyRuntimeSiteChanged RuntimeSiteRef RuntimeSiteRef
  | BeginPolicyServerSelectMismatch Text BlockId [SystemsOp]
  | BeginPolicyClientOfferMismatch Text BlockId SystemsTerminator
  | BeginPolicyDecisionAlreadyPresent DecisionId
  | BeginPolicyDecisionMissing DecisionId
  | BeginPolicyDecisionMismatch DecisionId
  deriving (Eq, Show)

phase0BeginPolicySessionChoiceWitness :: BeginPolicySessionChoiceWitness
phase0BeginPolicySessionChoiceWitness = BeginPolicySessionChoiceWitness
  { beginPolicyServerFunction = "UploadServer"
  , beginPolicyServerTransport = ValueId "server.transport"
  , beginPolicyCommitBlock = BlockId "server.begin.commit"
  , beginPolicyBeginRecord = ValueId "server.begin"
  , beginPolicyPolicyContext = ValueId "server.policy_context"
  , beginPolicyServerRejectReason = ValueId "server.begin_reject_reason"
  , beginPolicyRuntimeChoiceName = "validate BeginPolicy"
  , beginPolicyAcceptedArm = "accepted"
  , beginPolicyRejectedArm = "rejected"
  , beginPolicyServerRejectBlock = BlockId "server.reject"
  , beginPolicyServerProceedBlock = BlockId "server.proceed"
  , beginPolicyRejectLabel = "reject"
  , beginPolicyProceedLabel = "proceed"
  , beginPolicyClientFunction = "UploadClient"
  , beginPolicyClientTransport = ValueId "client.transport"
  , beginPolicyClientOfferBlock = BlockId "client.version"
  , beginPolicyClientRejectTarget = BlockId "client.reject"
  , beginPolicyClientProceedTarget = BlockId "client.proceed"
  , beginPolicyClientRejectReason = ValueId "client.begin_reject_reason"
  , beginPolicyClientLegacyDiscriminator = ValueId "client.begin_branch"
  , beginPolicyClientLegacyReceiveCall = "receive proceed/reject label"
  , beginPolicyLoweringDecision = DecisionId "lower.session.begin_policy_choice"
  }

phase0BeginPolicySessionChoiceBundle
  :: Either BeginPolicySessionChoiceError BeginPolicySessionChoiceBundle
phase0BeginPolicySessionChoiceBundle = do
  predecessor <- mapLeft BeginPolicyPredecessorError phase0VersionChoiceOperandsBundle
  let baseArtifact = versionChoiceOperandsArtifact predecessor
      baseContext = versionChoiceOperandsContext predecessor
      witness = phase0BeginPolicySessionChoiceWitness
      predecessorDecisions = loweringLedgerDecisions (systemsArtifactLoweringLedger baseArtifact)
  when (Map.member (beginPolicyLoweringDecision witness) predecessorDecisions) $
    Left (BeginPolicyDecisionAlreadyPresent (beginPolicyLoweringDecision witness))
  predecessorSite <- extractPredecessorRuntimeSite baseArtifact witness
  program <- materializeBeginPolicySessionChoice witness (systemsArtifactProgram baseArtifact)
  let baseContract = systemsArtifactStageContract baseArtifact
      targetDigest = systemsProgramDigest program
      contract = baseContract
        { stageTargetArtifactDigest = targetDigest
        , stageTraceRelation = stageTraceRelation baseContract <>
            [ "BeginPolicy validation preserves the exact runtime site while exposing accepted/rejected(reason) as a local semantic choice"
            , "reject(reason)/proceed is a peer-visible session choice with branch-local reason identity"
            , "the established recognized Begin value and a new explicit policyContext become validator operands without selecting new physical representation"
            ]
        }
      sourceDigest = stageSourceArtifactDigest contract
      rebound = Map.map (rebindDecisionTarget targetDigest) predecessorDecisions
      decision = deriveBeginPolicyDecision sourceDigest targetDigest predecessorSite witness
      decisions = Map.insert (beginPolicyLoweringDecision witness) decision rebound
      loweringRoot = deriveLoweringLedgerRoot decisions
      artifact = SystemsArtifact program contract (LoweringLedger decisions loweringRoot)
      assuranceLedger = systemsAssuranceLedger baseContext
      baseManifest = systemsAssuranceManifest baseContext
      provisionalManifest = baseManifest
        { manifestImplementationDigest = systemsArtifactDigest artifact
        , manifestLoweringLedgerRoot = loweringRoot
        }
      manifest = provisionalManifest
        { manifestId = deriveManifestId assuranceLedger provisionalManifest }
      baseVerification = systemsAssuranceVerificationContext baseContext
      verification = baseVerification
        { verificationImplementationDigest = systemsArtifactDigest artifact
        , verificationLoweringLedgerRoot = loweringRoot
        }
      context = baseContext
        { systemsAssuranceManifest = manifest
        , systemsAssuranceVerificationContext = verification
        }
      bundle = BeginPolicySessionChoiceBundle artifact context predecessor witness
  verifyBeginPolicySessionChoiceBundle bundle
  pure bundle

verifyBeginPolicySessionChoiceBundle
  :: BeginPolicySessionChoiceBundle
  -> Either BeginPolicySessionChoiceError ()
verifyBeginPolicySessionChoiceBundle bundle = do
  mapLeft BeginPolicyPredecessorError $
    verifyVersionChoiceOperandsBundle (beginPolicySessionChoicePredecessor bundle)
  mapLeft BeginPolicySystemsError $
    verifySystemsArtifact
      (beginPolicySessionChoiceContext bundle)
      (beginPolicySessionChoiceArtifact bundle)
  mapLeft BeginPolicyDataflowError $
    verifyScalarDataflow (beginPolicySessionChoiceArtifact bundle)
  mapLeft BeginPolicyVersionRegression $
    verifyVersionChoiceOperandsWitness
      (beginPolicySessionChoiceArtifact bundle)
      phase0VersionChoiceOperandsWitness
  mapLeft BeginPolicyRecognizedRecordRegression $
    verifyRecognizedRecordWitnesses
      (beginPolicySessionChoiceArtifact bundle)
      [phase0BeginRecordWitness]
  let witness = beginPolicySessionChoiceWitness bundle
  predecessorSite <- extractPredecessorRuntimeSite
    (versionChoiceOperandsArtifact (beginPolicySessionChoicePredecessor bundle))
    witness
  successorSite <- extractSuccessorRuntimeSite
    (beginPolicySessionChoiceArtifact bundle)
    witness
  unless (predecessorSite == successorSite) $
    Left (BeginPolicyRuntimeSiteChanged predecessorSite successorSite)
  verifyBeginPolicySessionChoiceWitness
    (beginPolicySessionChoiceArtifact bundle)
    witness

verifyBeginPolicySessionChoiceWitness
  :: SystemsArtifact
  -> BeginPolicySessionChoiceWitness
  -> Either BeginPolicySessionChoiceError ()
verifyBeginPolicySessionChoiceWitness artifact witness = do
  let program = systemsArtifactProgram artifact
  server <- lookupFunction (beginPolicyServerFunction witness) program
  client <- lookupFunction (beginPolicyClientFunction witness) program

  verifyRole (beginPolicyServerFunction witness) server
    (beginPolicyServerTransport witness) TransportHandle
  verifyRole (beginPolicyServerFunction witness) server
    (beginPolicyBeginRecord witness) (RuntimeRecord "Begin")
  verifyRole (beginPolicyServerFunction witness) server
    (beginPolicyPolicyContext witness) (RuntimeInput "PolicyContext")
  verifyRole (beginPolicyServerFunction witness) server
    (beginPolicyServerRejectReason witness) (RuntimeOpaque "ValidationReason[BeginPolicy]")
  verifyRole (beginPolicyClientFunction witness) client
    (beginPolicyClientTransport witness) TransportHandle
  verifyRole (beginPolicyClientFunction witness) client
    (beginPolicyClientRejectReason witness) (RuntimeOpaque "ValidationReason[BeginPolicy]")

  when (valueHasProducer server (beginPolicyPolicyContext witness)) $
    Left (BeginPolicyInputHasProducer
      (beginPolicyServerFunction witness)
      (beginPolicyPolicyContext witness))

  case Map.lookup (beginPolicyClientLegacyDiscriminator witness) (systemsFunctionValues client) of
    Nothing -> pure ()
    Just _ -> Left (BeginPolicyLegacyDiscriminatorPresent
      (beginPolicyClientFunction witness)
      (beginPolicyClientLegacyDiscriminator witness))

  commitBlock <- lookupBlock
    (beginPolicyServerFunction witness)
    server
    (beginPolicyCommitBlock witness)
  case systemsBlockTerminator commitBlock of
    TermRuntimeChoice name inputs (Just site) arms
      | name == beginPolicyRuntimeChoiceName witness
          && inputs == [beginPolicyPolicyContext witness, beginPolicyBeginRecord witness]
          && runtimeSiteKind site == ValidationBoundary "BeginPolicy"
          && arms == expectedRuntimeArms witness -> pure ()
    other -> Left (BeginPolicyRuntimeChoiceMismatch
      (beginPolicyServerFunction witness)
      (beginPolicyCommitBlock witness)
      other)

  verifyServerSelect
    witness server
    (beginPolicyServerRejectBlock witness)
    (beginPolicyRejectLabel witness)
    (Just (beginPolicyServerRejectReason witness))
  verifyServerSelect
    witness server
    (beginPolicyServerProceedBlock witness)
    (beginPolicyProceedLabel witness)
    Nothing

  offerBlock <- lookupBlock
    (beginPolicyClientFunction witness)
    client
    (beginPolicyClientOfferBlock witness)
  unless (not (any (isLegacyReceive witness) (systemsBlockOps offerBlock))) $
    Left (BeginPolicyLegacyReceivePresent
      (beginPolicyClientFunction witness)
      (beginPolicyClientOfferBlock witness)
      (beginPolicyClientLegacyReceiveCall witness))
  case systemsBlockTerminator offerBlock of
    TermSessionOffer transport arms
      | transport == beginPolicyClientTransport witness
          && arms == expectedOfferArms witness -> pure ()
    other -> Left (BeginPolicyClientOfferMismatch
      (beginPolicyClientFunction witness)
      (beginPolicyClientOfferBlock witness)
      other)

  let decisions = loweringLedgerDecisions (systemsArtifactLoweringLedger artifact)
      sourceDigest = stageSourceArtifactDigest (systemsArtifactStageContract artifact)
      targetDigest = systemsProgramDigest program
  site <- extractSuccessorRuntimeSite artifact witness
  let expectedDecision = deriveBeginPolicyDecision sourceDigest targetDigest site witness
  case Map.lookup (beginPolicyLoweringDecision witness) decisions of
    Nothing -> Left (BeginPolicyDecisionMissing (beginPolicyLoweringDecision witness))
    Just actual -> unless (actual == expectedDecision) $
      Left (BeginPolicyDecisionMismatch (beginPolicyLoweringDecision witness))

verifyServerSelect
  :: BeginPolicySessionChoiceWitness
  -> SystemsFunction
  -> BlockId
  -> Text
  -> Maybe ValueId
  -> Either BeginPolicySessionChoiceError ()
verifyServerSelect witness server blockId label payload = do
  blockValue <- lookupBlock (beginPolicyServerFunction witness) server blockId
  let exact operation = case operation of
        OpSessionSelect transport actualLabel actualPayload decisionId ->
          transport == beginPolicyServerTransport witness
            && actualLabel == label
            && actualPayload == payload
            && decisionId == beginPolicyLoweringDecision witness
        _ -> False
      legacy operation = case operation of
        OpRuntimeCall { runtimeCallName = name } -> name == "select " <> label
        _ -> False
  unless (any exact (systemsBlockOps blockValue) && not (any legacy (systemsBlockOps blockValue))) $
    Left (BeginPolicyServerSelectMismatch
      (beginPolicyServerFunction witness)
      blockId
      (systemsBlockOps blockValue))

materializeBeginPolicySessionChoice
  :: BeginPolicySessionChoiceWitness
  -> SystemsProgram
  -> Either BeginPolicySessionChoiceError SystemsProgram
materializeBeginPolicySessionChoice witness program = do
  server <- lookupFunction (beginPolicyServerFunction witness) program
  client <- lookupFunction (beginPolicyClientFunction witness) program
  commitBlock <- lookupBlock
    (beginPolicyServerFunction witness) server (beginPolicyCommitBlock witness)
  rejectBlock <- lookupBlock
    (beginPolicyServerFunction witness) server (beginPolicyServerRejectBlock witness)
  proceedBlock <- lookupBlock
    (beginPolicyServerFunction witness) server (beginPolicyServerProceedBlock witness)
  clientOffer <- lookupBlock
    (beginPolicyClientFunction witness) client (beginPolicyClientOfferBlock witness)

  verifyRole (beginPolicyServerFunction witness) server
    (beginPolicyBeginRecord witness) (RuntimeRecord "Begin")
  mapM_ (requireAbsent (beginPolicyServerFunction witness) server)
    [ beginPolicyPolicyContext witness
    , beginPolicyServerRejectReason witness
    ]
  requireAbsent
    (beginPolicyClientFunction witness)
    client
    (beginPolicyClientRejectReason witness)

  site <- case systemsBlockTerminator commitBlock of
    TermRuntimeCheck [] runtimeSite yes no
      | runtimeSiteKind runtimeSite == ValidationBoundary "BeginPolicy"
          && yes == beginPolicyServerProceedBlock witness
          && no == beginPolicyServerRejectBlock witness -> Right runtimeSite
    other -> Left (BeginPolicyRuntimeChoiceMismatch
      (beginPolicyServerFunction witness)
      (beginPolicyCommitBlock witness)
      other)

  case systemsBlockTerminator clientOffer of
    TermBranch discriminator yes no
      | discriminator == beginPolicyClientLegacyDiscriminator witness
          && yes == beginPolicyClientProceedTarget witness
          && no == beginPolicyClientRejectTarget witness -> pure ()
    other -> Left (BeginPolicyClientOfferMismatch
      (beginPolicyClientFunction witness)
      (beginPolicyClientOfferBlock witness)
      other)

  rejectBlock' <- replaceLegacySelect witness rejectBlock
    (beginPolicyRejectLabel witness)
    (Just (beginPolicyServerRejectReason witness))
  proceedBlock' <- replaceLegacySelect witness proceedBlock
    (beginPolicyProceedLabel witness)
    Nothing
  clientOps <- stripLegacyReceive witness (systemsBlockOps clientOffer)

  let commitBlock' = commitBlock
        { systemsBlockTerminator = TermRuntimeChoice
            (beginPolicyRuntimeChoiceName witness)
            [beginPolicyPolicyContext witness, beginPolicyBeginRecord witness]
            (Just site)
            (expectedRuntimeArms witness)
        }
      serverValues = Map.insert
        (beginPolicyServerRejectReason witness)
        (SystemsValue
          (beginPolicyServerRejectReason witness)
          (RuntimeOpaque "ValidationReason[BeginPolicy]")
          Nothing) $
        Map.insert
          (beginPolicyPolicyContext witness)
          (SystemsValue
            (beginPolicyPolicyContext witness)
            (RuntimeInput "PolicyContext")
            Nothing)
          (systemsFunctionValues server)
      server' = server
        { systemsFunctionValues = serverValues
        , systemsFunctionBlocks = Map.insert
            (beginPolicyServerProceedBlock witness) proceedBlock' $
            Map.insert
              (beginPolicyServerRejectBlock witness) rejectBlock' $
              Map.insert
                (beginPolicyCommitBlock witness) commitBlock'
                (systemsFunctionBlocks server)
        }
      clientValues = Map.insert
        (beginPolicyClientRejectReason witness)
        (SystemsValue
          (beginPolicyClientRejectReason witness)
          (RuntimeOpaque "ValidationReason[BeginPolicy]")
          Nothing) $
        Map.delete
          (beginPolicyClientLegacyDiscriminator witness)
          (systemsFunctionValues client)
      clientOffer' = clientOffer
        { systemsBlockOps = clientOps
        , systemsBlockTerminator = TermSessionOffer
            (beginPolicyClientTransport witness)
            (expectedOfferArms witness)
        }
      client' = client
        { systemsFunctionValues = clientValues
        , systemsFunctionBlocks = Map.insert
            (beginPolicyClientOfferBlock witness)
            clientOffer'
            (systemsFunctionBlocks client)
        }
  pure program
    { systemsProgramFunctions = Map.insert
        (beginPolicyClientFunction witness) client' $
        Map.insert
          (beginPolicyServerFunction witness)
          server'
          (systemsProgramFunctions program)
    }

expectedRuntimeArms
  :: BeginPolicySessionChoiceWitness
  -> Map.Map Text SystemsRuntimeChoiceArm
expectedRuntimeArms witness = Map.fromList
  [ ( beginPolicyAcceptedArm witness
    , SystemsRuntimeChoiceArm Nothing (beginPolicyServerProceedBlock witness)
    )
  , ( beginPolicyRejectedArm witness
    , SystemsRuntimeChoiceArm
        (Just (beginPolicyServerRejectReason witness))
        (beginPolicyServerRejectBlock witness)
    )
  ]

expectedOfferArms
  :: BeginPolicySessionChoiceWitness
  -> Map.Map Text SystemsChoiceArm
expectedOfferArms witness = Map.fromList
  [ ( beginPolicyRejectLabel witness
    , SystemsChoiceArm
        (Just (beginPolicyClientRejectReason witness))
        (beginPolicyClientRejectTarget witness)
    )
  , ( beginPolicyProceedLabel witness
    , SystemsChoiceArm Nothing (beginPolicyClientProceedTarget witness)
    )
  ]

extractPredecessorRuntimeSite
  :: SystemsArtifact
  -> BeginPolicySessionChoiceWitness
  -> Either BeginPolicySessionChoiceError RuntimeSiteRef
extractPredecessorRuntimeSite artifact witness = do
  server <- lookupFunction
    (beginPolicyServerFunction witness)
    (systemsArtifactProgram artifact)
  blockValue <- lookupBlock
    (beginPolicyServerFunction witness)
    server
    (beginPolicyCommitBlock witness)
  case systemsBlockTerminator blockValue of
    TermRuntimeCheck _ site yes no
      | runtimeSiteKind site == ValidationBoundary "BeginPolicy"
          && yes == beginPolicyServerProceedBlock witness
          && no == beginPolicyServerRejectBlock witness -> Right site
    other -> Left (BeginPolicyRuntimeChoiceMismatch
      (beginPolicyServerFunction witness)
      (beginPolicyCommitBlock witness)
      other)

extractSuccessorRuntimeSite
  :: SystemsArtifact
  -> BeginPolicySessionChoiceWitness
  -> Either BeginPolicySessionChoiceError RuntimeSiteRef
extractSuccessorRuntimeSite artifact witness = do
  server <- lookupFunction
    (beginPolicyServerFunction witness)
    (systemsArtifactProgram artifact)
  blockValue <- lookupBlock
    (beginPolicyServerFunction witness)
    server
    (beginPolicyCommitBlock witness)
  case systemsBlockTerminator blockValue of
    TermRuntimeChoice name _ (Just site) arms
      | name == beginPolicyRuntimeChoiceName witness
          && arms == expectedRuntimeArms witness -> Right site
    other -> Left (BeginPolicyRuntimeChoiceMismatch
      (beginPolicyServerFunction witness)
      (beginPolicyCommitBlock witness)
      other)

replaceLegacySelect
  :: BeginPolicySessionChoiceWitness
  -> SystemsBlock
  -> Text
  -> Maybe ValueId
  -> Either BeginPolicySessionChoiceError SystemsBlock
replaceLegacySelect witness blockValue label payload =
  case break isLegacy (systemsBlockOps blockValue) of
    (before, _ : after)
      | not (any isLegacy after) -> Right blockValue
          { systemsBlockOps = before <>
              [ OpSessionSelect
                  (beginPolicyServerTransport witness)
                  label
                  payload
                  (beginPolicyLoweringDecision witness)
              ] <> after
          }
      | otherwise -> mismatch
    _ -> mismatch
  where
    isLegacy operation = case operation of
      OpRuntimeCall name inputs outputs site _ ->
        name == "select " <> label
          && inputs == [beginPolicyServerTransport witness]
          && null outputs
          && site == Nothing
      _ -> False
    mismatch = Left (BeginPolicyServerSelectMismatch
      (beginPolicyServerFunction witness)
      (systemsBlockId blockValue)
      (systemsBlockOps blockValue))

stripLegacyReceive
  :: BeginPolicySessionChoiceWitness
  -> [SystemsOp]
  -> Either BeginPolicySessionChoiceError [SystemsOp]
stripLegacyReceive witness operations =
  case [index | (index, operation) <- zip [0 :: Int ..] operations, isLegacyReceive witness operation] of
    [index] -> Right (take index operations <> drop (index + 1) operations)
    _ -> Left (BeginPolicyLegacyReceivePresent
      (beginPolicyClientFunction witness)
      (beginPolicyClientOfferBlock witness)
      (beginPolicyClientLegacyReceiveCall witness))

isLegacyReceive :: BeginPolicySessionChoiceWitness -> SystemsOp -> Bool
isLegacyReceive witness operation = case operation of
  OpRuntimeCall name inputs outputs site _ ->
    name == beginPolicyClientLegacyReceiveCall witness
      && inputs == [beginPolicyClientTransport witness]
      && outputs == [beginPolicyClientLegacyDiscriminator witness]
      && site == Nothing
  _ -> False

verifyRole
  :: Text
  -> SystemsFunction
  -> ValueId
  -> SystemsValueRole
  -> Either BeginPolicySessionChoiceError ()
verifyRole functionName function valueId expected =
  case Map.lookup valueId (systemsFunctionValues function) of
    Nothing -> Left (BeginPolicyValueMissing functionName valueId)
    Just SystemsValue { systemsValueRole = actual }
      | actual == expected -> pure ()
      | otherwise -> Left (BeginPolicyValueRoleMismatch functionName valueId actual)

requireAbsent
  :: Text
  -> SystemsFunction
  -> ValueId
  -> Either BeginPolicySessionChoiceError ()
requireAbsent functionName function valueId =
  when (Map.member valueId (systemsFunctionValues function)) $
    Left (BeginPolicyUnexpectedValuePresent functionName valueId)

lookupFunction
  :: Text
  -> SystemsProgram
  -> Either BeginPolicySessionChoiceError SystemsFunction
lookupFunction functionName program =
  case Map.lookup functionName (systemsProgramFunctions program) of
    Nothing -> Left (BeginPolicyFunctionMissing functionName)
    Just function -> Right function

lookupBlock
  :: Text
  -> SystemsFunction
  -> BlockId
  -> Either BeginPolicySessionChoiceError SystemsBlock
lookupBlock functionName function blockId =
  case Map.lookup blockId (systemsFunctionBlocks function) of
    Nothing -> Left (BeginPolicyBlockMissing functionName blockId)
    Just blockValue -> Right blockValue

valueHasProducer :: SystemsFunction -> ValueId -> Bool
valueHasProducer function valueId = any blockProduces (Map.elems (systemsFunctionBlocks function))
  where
    blockProduces blockValue =
      any opProduces (systemsBlockOps blockValue)
        || terminatorProduces (systemsBlockTerminator blockValue)
    opProduces operation = case operation of
      OpRuntimeCall { runtimeCallOutputs = outputs } -> valueId `elem` outputs
      OpCopy { copyTarget = target } -> valueId == target
      OpScalarLiteral { scalarLiteralOutput = output } -> valueId == output
      _ -> False
    terminatorProduces terminator = case terminator of
      TermRuntimeChoice { runtimeChoiceArms = arms } ->
        any ((== Just valueId) . runtimeChoiceArmPayloadBinding) (Map.elems arms)
      TermSessionOffer { sessionOfferArms = arms } ->
        any ((== Just valueId) . choiceArmPayloadBinding) (Map.elems arms)
      _ -> False

rebindDecisionTarget :: Digest -> LoweringDecision -> LoweringDecision
rebindDecisionTarget targetDigest lowering = provisional
  { loweringDecisionDigest = deriveLoweringDecisionDigest provisional }
  where
    provisional = lowering { loweringTargetArtifactDigest = targetDigest }

deriveBeginPolicyDecision
  :: Digest
  -> Digest
  -> RuntimeSiteRef
  -> BeginPolicySessionChoiceWitness
  -> LoweringDecision
deriveBeginPolicyDecision sourceDigest targetDigest site witness = provisional
  { loweringDecisionDigest = deriveLoweringDecisionDigest provisional }
  where
    provisional = LoweringDecision
      { loweringDecisionId = beginPolicyLoweringDecision witness
      , loweringDecisionDigest = Digest ""
      , loweringSourceArtifactDigest = sourceDigest
      , loweringTargetArtifactDigest = targetDigest
      , loweringSourceRepresentation =
          "implicit BeginPolicy runtime-check operands/result + generic reject/proceed calls + client Bool discriminator"
      , loweringTargetRepresentation =
          "established Begin record + explicit PolicyContext operand + accepted/rejected(reason) local runtime choice + reject(reason)/proceed semantic session choice"
      , loweringSemanticEntities =
          [ "validation:BeginPolicy"
          , "record:Begin"
          , "input:policyContext"
          , "reason:BeginPolicy rejection"
          , "session-label:reject"
          , "session-label:proceed"
          ]
      , loweringObligationRevisions = [runtimeSiteRevision site]
      , loweringAssuranceEntries = [runtimeSiteEvidence site]
      , loweringAssuranceUses = []
      , loweringAction = Materialize
      , loweringRepresentationBefore =
          "payload-free success/failure validator branch and anonymous peer discriminator"
      , loweringRepresentationAfter =
          "payload-bearing rejected validator arm and payload-bearing reject session arm"
      , loweringInvariantsPreserved =
          [ "BeginPolicy validation remains at the exact runtime assurance site"
          , "accepted validation continues to server.proceed"
          , "rejected validation continues to server.reject"
          , "reject reason exists only on rejected/reject arms"
          , "proceed carries no runtime payload"
          ]
      , loweringInvariantsTransferred = []
      , loweringRuntimeResidue =
          [ "existing Begin record representation and provenance are preserved from the recognized-record predecessor"
          , "PolicyContext representation remains target-selected"
          , "validation implementation remains the retained BeginPolicy runtime site"
          , "reject reason representation, code space, and wire encoding are deliberately unselected"
          , "outer framing is not selected by this semantic slice"
          ]
      , loweringCostClass = Just SemanticRequired
      , loweringCostShape = emptyCostShape
          { costCodeSize = Just "explicit policy input/reason identities plus local/session choice structure"
          , costDynamicCheckCount = Just "no new check; the existing BeginPolicy runtime validation is retained"
          , costBranchOrDispatch = Just "same validation branch plus semantic peer-choice dispatch"
          , costFrequency = Just "once per successfully recognized Begin"
          }
      , loweringTargetPreconditions =
          [ "recognized Begin record materialization/projection from the predecessor remains valid before validation"
          , "rejected and reject payload targets are dedicated single-predecessor blocks"
          ]
      , loweringAssumptions = []
      , loweringDerivedObligations = []
      , loweringInspectionPlan =
          [ "verify the predecessor recognized Begin witness still holds exactly"
          , "verify exact BeginPolicy RuntimeSiteRef is preserved"
          , "verify server reject selects exactly the local rejection reason"
          , "verify client reject binds a distinct peer-received reason identity"
          , "verify generic LLVM remains fail-closed until a reject/proceed physical profile is selected"
          ]
      }

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
