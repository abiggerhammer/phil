{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.ClientOutbound
  ( ClientOutboundWitness (..)
  , ClientOutboundBundle (..)
  , ClientOutboundError (..)
  , phase0ClientOutboundWitness
  , phase0ClientOutboundBundle
  , verifyClientOutboundBundle
  , verifyClientOutboundWitness
  ) where

import Control.Monad (unless, when)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Assurance.Types
import Phil.Systems.BeginPolicySessionChoice
import Phil.Systems.Dataflow
import Phil.Systems.HelloPolicyValidation
import Phil.Systems.IR
import Phil.Systems.Verify
import Phil.Systems.VersionChoiceOperands

data ClientOutboundWitness = ClientOutboundWitness
  { clientOutboundFunction :: Text
  , clientOutboundTransport :: ValueId
  , clientOutboundPayload :: ValueId
  , clientOutboundEntryBlock :: BlockId
  , clientOutboundVersionBlock :: BlockId
  , clientOutboundSupportedVersions :: ValueId
  , clientOutboundHelloRecord :: ValueId
  , clientOutboundPayloadView :: ValueId
  , clientOutboundPayloadLength :: ValueId
  , clientOutboundPayloadKind :: ValueId
  , clientOutboundDeclaredDigest :: ValueId
  , clientOutboundBeginRecord :: ValueId
  , clientOutboundSupportedVersionsCall :: Text
  , clientOutboundConstructHelloCall :: Text
  , clientOutboundProjectLengthCall :: Text
  , clientOutboundProjectKindCall :: Text
  , clientOutboundDigestCall :: Text
  , clientOutboundConstructBeginCall :: Text
  , clientOutboundSendHelloCall :: Text
  , clientOutboundSendBeginCall :: Text
  , clientOutboundSemanticCallDecision :: DecisionId
  , clientOutboundRecordDecision :: DecisionId
  , clientOutboundBorrowDecision :: DecisionId
  , clientOutboundDigestDecision :: DecisionId
  , clientOutboundBorrowInvariant :: InvariantId
  }
  deriving (Eq, Show)

data ClientOutboundBundle = ClientOutboundBundle
  { clientOutboundArtifact :: SystemsArtifact
  , clientOutboundContext :: SystemsVerificationContext
  , clientOutboundPredecessor :: HelloPolicyValidationBundle
  , clientOutboundWitness :: ClientOutboundWitness
  }
  deriving (Eq, Show)

data ClientOutboundError
  = ClientOutboundPredecessorError HelloPolicyValidationError
  | ClientOutboundSystemsError SystemsVerificationError
  | ClientOutboundDataflowError ScalarDataflowError
  | ClientOutboundHelloPolicyRegression HelloPolicyValidationError
  | ClientOutboundBeginPolicyRegression BeginPolicySessionChoiceError
  | ClientOutboundVersionOperandsRegression VersionChoiceOperandsError
  | ClientOutboundFunctionMissing Text
  | ClientOutboundBlockMissing Text BlockId
  | ClientOutboundValueMissing Text ValueId
  | ClientOutboundValueRoleMismatch Text ValueId SystemsValueRole
  | ClientOutboundUnexpectedValuePresent Text ValueId
  | ClientOutboundEntryMismatch [SystemsOp]
  | ClientOutboundVersionMismatch [SystemsOp]
  | ClientOutboundUseMismatch ValueId [(BlockId, Text)]
  | ClientOutboundInvariantMismatch InvariantId
  | ClientOutboundDecisionAlreadyPresent DecisionId
  | ClientOutboundDecisionMissing DecisionId
  | ClientOutboundDecisionMismatch DecisionId
  deriving (Eq, Show)

phase0ClientOutboundWitness :: ClientOutboundWitness
phase0ClientOutboundWitness = ClientOutboundWitness
  { clientOutboundFunction = "UploadClient"
  , clientOutboundTransport = ValueId "client.transport"
  , clientOutboundPayload = ValueId "client.payload"
  , clientOutboundEntryBlock = BlockId "client.entry"
  , clientOutboundVersionBlock = BlockId "client.version"
  , clientOutboundSupportedVersions = ValueId "client.supported_versions"
  , clientOutboundHelloRecord = ValueId "client.hello"
  , clientOutboundPayloadView = ValueId "client.payload_view"
  , clientOutboundPayloadLength = ValueId "client.payload_length"
  , clientOutboundPayloadKind = ValueId "client.payload_kind"
  , clientOutboundDeclaredDigest = ValueId "client.declared_digest"
  , clientOutboundBeginRecord = ValueId "client.begin"
  , clientOutboundSupportedVersionsCall = "supported_versions"
  , clientOutboundConstructHelloCall = "construct Hello"
  , clientOutboundProjectLengthCall = "project payload.length"
  , clientOutboundProjectKindCall = "project payload.kind"
  , clientOutboundDigestCall = "sha256 payload"
  , clientOutboundConstructBeginCall = "construct Begin[sha256]"
  , clientOutboundSendHelloCall = "send Hello"
  , clientOutboundSendBeginCall = "send Begin"
  , clientOutboundSemanticCallDecision = DecisionId "lower.runtime.semantic_call"
  , clientOutboundRecordDecision = DecisionId "lower.client.outbound.records"
  , clientOutboundBorrowDecision = DecisionId "lower.client.outbound.digest_borrow"
  , clientOutboundDigestDecision = DecisionId "lower.client.outbound.sha256"
  , clientOutboundBorrowInvariant = InvariantId "invariant.client.payload.digest_borrow_no_copy"
  }

phase0ClientOutboundBundle
  :: Either ClientOutboundError ClientOutboundBundle
phase0ClientOutboundBundle = do
  predecessor <- mapLeft ClientOutboundPredecessorError phase0HelloPolicyValidationBundle
  let baseArtifact = helloPolicyValidationArtifact predecessor
      baseContext = helloPolicyValidationContext predecessor
      witness = phase0ClientOutboundWitness
      predecessorDecisions = loweringLedgerDecisions (systemsArtifactLoweringLedger baseArtifact)
  mapM_ (requireDecisionAbsent predecessorDecisions)
    [ clientOutboundRecordDecision witness
    , clientOutboundBorrowDecision witness
    , clientOutboundDigestDecision witness
    ]
  program <- materializeClientOutbound witness (systemsArtifactProgram baseArtifact)
  let baseContract = systemsArtifactStageContract baseArtifact
      targetDigest = systemsProgramDigest program
      outboundInvariant = StageInvariant
        (clientOutboundBorrowInvariant witness)
        (InvariantBorrowAliases
          (clientOutboundFunction witness)
          (clientOutboundPayloadView witness)
          (clientOutboundPayload witness))
      contract = baseContract
        { stageTargetArtifactDigest = targetDigest
        , stageInvariants = Map.insert
            (clientOutboundBorrowInvariant witness)
            outboundInvariant
            (stageInvariants baseContract)
        , stageTraceRelation = stageTraceRelation baseContract <>
            [ "client supported_versions() -> explicit client.supported_versions -> construct Hello -> send exact client.hello semantic record"
            , "client payload shared borrow -> SHA-256 declared digest; payload.length + payload.kind + fixed sha256 algorithm -> construct Begin -> send exact client.begin semantic record"
            , "the source proof len(supported_versions) > 0 remains compile-time evidence and introduces no runtime proof object in Systems"
            ]
        }
      sourceDigest = stageSourceArtifactDigest contract
      rebound = Map.map (rebindDecisionTarget targetDigest) predecessorDecisions
      recordsDecision = deriveRecordDecision sourceDigest targetDigest witness
      borrowDecision = deriveBorrowDecision sourceDigest targetDigest witness
      digestDecision = deriveDigestDecision sourceDigest targetDigest witness
      decisions = Map.insert (clientOutboundDigestDecision witness) digestDecision $
        Map.insert (clientOutboundBorrowDecision witness) borrowDecision $
        Map.insert (clientOutboundRecordDecision witness) recordsDecision rebound
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
      bundle = ClientOutboundBundle artifact context predecessor witness
  verifyClientOutboundBundle bundle
  pure bundle

verifyClientOutboundBundle
  :: ClientOutboundBundle
  -> Either ClientOutboundError ()
verifyClientOutboundBundle bundle = do
  mapLeft ClientOutboundPredecessorError $
    verifyHelloPolicyValidationBundle (clientOutboundPredecessor bundle)
  mapLeft ClientOutboundSystemsError $
    verifySystemsArtifact
      (clientOutboundContext bundle)
      (clientOutboundArtifact bundle)
  mapLeft ClientOutboundDataflowError $
    verifyScalarDataflow (clientOutboundArtifact bundle)
  mapLeft ClientOutboundHelloPolicyRegression $
    verifyHelloPolicyValidationWitness
      (clientOutboundArtifact bundle)
      phase0HelloPolicyValidationWitness
  mapLeft ClientOutboundBeginPolicyRegression $
    verifyBeginPolicySessionChoiceWitness
      (clientOutboundArtifact bundle)
      phase0BeginPolicySessionChoiceWitness
  mapLeft ClientOutboundVersionOperandsRegression $
    verifyVersionChoiceOperandsWitness
      (clientOutboundArtifact bundle)
      phase0VersionChoiceOperandsWitness
  verifyClientOutboundWitness
    (clientOutboundArtifact bundle)
    (clientOutboundWitness bundle)

verifyClientOutboundWitness
  :: SystemsArtifact
  -> ClientOutboundWitness
  -> Either ClientOutboundError ()
verifyClientOutboundWitness artifact witness = do
  let program = systemsArtifactProgram artifact
      functionName = clientOutboundFunction witness
  client <- lookupFunction functionName program

  verifyRole functionName client (clientOutboundTransport witness) TransportHandle
  verifyRole functionName client (clientOutboundPayload witness)
    (OwnedBuffer "Bytes[payload.length]")
  verifyRole functionName client (clientOutboundSupportedVersions witness)
    (RuntimeOpaque "VersionSet")
  verifyRole functionName client (clientOutboundHelloRecord witness)
    (RuntimeRecord "Hello")
  verifyRole functionName client (clientOutboundPayloadView witness)
    (BorrowedSlice (clientOutboundPayload witness))
  verifyRole functionName client (clientOutboundPayloadLength witness)
    (TypedScalar (ScalarUInt 64))
  verifyRole functionName client (clientOutboundPayloadKind witness)
    (RuntimeOpaque "PayloadKind")
  verifyRole functionName client (clientOutboundDeclaredDigest witness)
    (RuntimeOpaque "SHA256Digest")
  verifyRole functionName client (clientOutboundBeginRecord witness)
    (RuntimeRecord "Begin")

  entryBlock <- lookupBlock functionName client (clientOutboundEntryBlock witness)
  unless (systemsBlockOps entryBlock == expectedEntryOps witness) $
    Left (ClientOutboundEntryMismatch (systemsBlockOps entryBlock))

  versionBlock <- lookupBlock functionName client (clientOutboundVersionBlock witness)
  unless (systemsBlockOps versionBlock == expectedVersionOps witness) $
    Left (ClientOutboundVersionMismatch (systemsBlockOps versionBlock))

  verifyExactUses client witness

  case Map.lookup
      (clientOutboundBorrowInvariant witness)
      (stageInvariants (systemsArtifactStageContract artifact)) of
    Just StageInvariant
      { stageInvariantClaim = InvariantBorrowAliases functionName' view owner
      }
        | functionName' == clientOutboundFunction witness
            && view == clientOutboundPayloadView witness
            && owner == clientOutboundPayload witness -> pure ()
    _ -> Left (ClientOutboundInvariantMismatch (clientOutboundBorrowInvariant witness))

  let decisions = loweringLedgerDecisions (systemsArtifactLoweringLedger artifact)
      sourceDigest = stageSourceArtifactDigest (systemsArtifactStageContract artifact)
      targetDigest = systemsProgramDigest program
  verifyDecision decisions
    (clientOutboundRecordDecision witness)
    (deriveRecordDecision sourceDigest targetDigest witness)
  verifyDecision decisions
    (clientOutboundBorrowDecision witness)
    (deriveBorrowDecision sourceDigest targetDigest witness)
  verifyDecision decisions
    (clientOutboundDigestDecision witness)
    (deriveDigestDecision sourceDigest targetDigest witness)

materializeClientOutbound
  :: ClientOutboundWitness
  -> SystemsProgram
  -> Either ClientOutboundError SystemsProgram
materializeClientOutbound witness program = do
  let functionName = clientOutboundFunction witness
  client <- lookupFunction functionName program
  verifyRole functionName client (clientOutboundTransport witness) TransportHandle
  verifyRole functionName client (clientOutboundPayload witness)
    (OwnedBuffer "Bytes[payload.length]")
  mapM_ (requireValueAbsent functionName client)
    [ clientOutboundSupportedVersions witness
    , clientOutboundHelloRecord witness
    , clientOutboundPayloadView witness
    , clientOutboundPayloadLength witness
    , clientOutboundPayloadKind witness
    , clientOutboundDeclaredDigest witness
    , clientOutboundBeginRecord witness
    ]

  entryBlock <- lookupBlock functionName client (clientOutboundEntryBlock witness)
  versionBlock <- lookupBlock functionName client (clientOutboundVersionBlock witness)

  let legacyHello =
        [ OpRuntimeCall
            (clientOutboundSendHelloCall witness)
            [clientOutboundTransport witness]
            []
            Nothing
            (clientOutboundSemanticCallDecision witness)
        ]
      legacyBegin =
        [ OpRuntimeCall
            (clientOutboundSendBeginCall witness)
            [clientOutboundTransport witness]
            []
            Nothing
            (clientOutboundSemanticCallDecision witness)
        ]
  unless (systemsBlockOps entryBlock == legacyHello) $
    Left (ClientOutboundEntryMismatch (systemsBlockOps entryBlock))
  unless (systemsBlockOps versionBlock == legacyBegin) $
    Left (ClientOutboundVersionMismatch (systemsBlockOps versionBlock))

  let values = foldr insertValue (systemsFunctionValues client)
        [ SystemsValue (clientOutboundSupportedVersions witness)
            (RuntimeOpaque "VersionSet") Nothing
        , SystemsValue (clientOutboundHelloRecord witness)
            (RuntimeRecord "Hello") Nothing
        , SystemsValue (clientOutboundPayloadView witness)
            (BorrowedSlice (clientOutboundPayload witness)) Nothing
        , SystemsValue (clientOutboundPayloadLength witness)
            (TypedScalar (ScalarUInt 64)) Nothing
        , SystemsValue (clientOutboundPayloadKind witness)
            (RuntimeOpaque "PayloadKind") Nothing
        , SystemsValue (clientOutboundDeclaredDigest witness)
            (RuntimeOpaque "SHA256Digest") Nothing
        , SystemsValue (clientOutboundBeginRecord witness)
            (RuntimeRecord "Begin") Nothing
        ]
      entryBlock' = entryBlock { systemsBlockOps = expectedEntryOps witness }
      versionBlock' = versionBlock { systemsBlockOps = expectedVersionOps witness }
      client' = client
        { systemsFunctionValues = values
        , systemsFunctionBlocks = Map.insert
            (clientOutboundVersionBlock witness) versionBlock' $
            Map.insert
              (clientOutboundEntryBlock witness) entryBlock'
              (systemsFunctionBlocks client)
        }
  pure program
    { systemsProgramFunctions = Map.insert
        functionName client' (systemsProgramFunctions program)
    }

expectedEntryOps :: ClientOutboundWitness -> [SystemsOp]
expectedEntryOps witness =
  [ OpRuntimeCall
      (clientOutboundSupportedVersionsCall witness)
      []
      [clientOutboundSupportedVersions witness]
      Nothing
      (clientOutboundSemanticCallDecision witness)
  , OpRuntimeCall
      (clientOutboundConstructHelloCall witness)
      [clientOutboundSupportedVersions witness]
      [clientOutboundHelloRecord witness]
      Nothing
      (clientOutboundRecordDecision witness)
  , OpRuntimeCall
      (clientOutboundSendHelloCall witness)
      [clientOutboundTransport witness, clientOutboundHelloRecord witness]
      []
      Nothing
      (clientOutboundSemanticCallDecision witness)
  ]

expectedVersionOps :: ClientOutboundWitness -> [SystemsOp]
expectedVersionOps witness =
  [ OpBorrowView
      (clientOutboundPayloadView witness)
      (clientOutboundPayload witness)
      (clientOutboundBorrowDecision witness)
  , OpRuntimeCall
      (clientOutboundDigestCall witness)
      [clientOutboundPayloadView witness]
      [clientOutboundDeclaredDigest witness]
      Nothing
      (clientOutboundDigestDecision witness)
  , OpRuntimeCall
      (clientOutboundProjectLengthCall witness)
      [clientOutboundPayload witness]
      [clientOutboundPayloadLength witness]
      Nothing
      (clientOutboundRecordDecision witness)
  , OpRuntimeCall
      (clientOutboundProjectKindCall witness)
      [clientOutboundPayload witness]
      [clientOutboundPayloadKind witness]
      Nothing
      (clientOutboundRecordDecision witness)
  , OpRuntimeCall
      (clientOutboundConstructBeginCall witness)
      [ clientOutboundPayloadLength witness
      , clientOutboundPayloadKind witness
      , clientOutboundDeclaredDigest witness
      ]
      [clientOutboundBeginRecord witness]
      Nothing
      (clientOutboundRecordDecision witness)
  , OpRuntimeCall
      (clientOutboundSendBeginCall witness)
      [clientOutboundTransport witness, clientOutboundBeginRecord witness]
      []
      Nothing
      (clientOutboundSemanticCallDecision witness)
  ]

verifyExactUses
  :: SystemsFunction
  -> ClientOutboundWitness
  -> Either ClientOutboundError ()
verifyExactUses client witness = mapM_ verifyOne expected
  where
    expected =
      [ (clientOutboundSupportedVersions witness,
          [(clientOutboundEntryBlock witness, "runtime-call:" <> clientOutboundConstructHelloCall witness)])
      , (clientOutboundHelloRecord witness,
          [(clientOutboundEntryBlock witness, "runtime-call:" <> clientOutboundSendHelloCall witness)])
      , (clientOutboundPayloadView witness,
          [(clientOutboundVersionBlock witness, "runtime-call:" <> clientOutboundDigestCall witness)])
      , (clientOutboundPayloadLength witness,
          [(clientOutboundVersionBlock witness, "runtime-call:" <> clientOutboundConstructBeginCall witness)])
      , (clientOutboundPayloadKind witness,
          [(clientOutboundVersionBlock witness, "runtime-call:" <> clientOutboundConstructBeginCall witness)])
      , (clientOutboundDeclaredDigest witness,
          [(clientOutboundVersionBlock witness, "runtime-call:" <> clientOutboundConstructBeginCall witness)])
      , (clientOutboundBeginRecord witness,
          [(clientOutboundVersionBlock witness, "runtime-call:" <> clientOutboundSendBeginCall witness)])
      ]
    verifyOne (valueId, expectedUses) =
      let actual = semanticUsesOf valueId client
      in unless (actual == expectedUses) $
          Left (ClientOutboundUseMismatch valueId actual)

semanticUsesOf :: ValueId -> SystemsFunction -> [(BlockId, Text)]
semanticUsesOf valueId function = concatMap blockUses (Map.elems (systemsFunctionBlocks function))
  where
    blockUses blockValue =
      [ (systemsBlockId blockValue, operationDescription operation)
      | operation <- systemsBlockOps blockValue
      , valueId `elem` operationInputs operation
      ] <> [ (systemsBlockId blockValue, "terminator")
           | valueId `elem` terminatorInputs (systemsBlockTerminator blockValue)
           ]

operationInputs :: SystemsOp -> [ValueId]
operationInputs operation = case operation of
  OpReceiveFrame pending frame transport _ _ -> [pending, frame, transport]
  OpBorrowView _ owner _ -> [owner]
  OpCommitIngress pending transport _ -> [pending, transport]
  OpDestroyPending pending frame _ -> [pending, frame]
  OpReleaseOwner owner _ -> [owner]
  OpCleanupPartial owner _ -> [owner]
  OpRuntimeCall _ inputs _ _ _ -> inputs
  OpSessionSelect transport _ payload _ -> transport : maybe [] pure payload
  OpCopy source _ _ -> [source]
  OpEraseFact {} -> []
  OpDiagnostic {} -> []
  OpScalarLiteral {} -> []
  OpTraceEvent _ -> []

terminatorInputs :: SystemsTerminator -> [ValueId]
terminatorInputs terminator = case terminator of
  TermJump _ -> []
  TermBranch condition _ _ -> [condition]
  TermRecognize pending raw _ _ _ -> [pending, raw]
  TermRuntimeCheck inputs _ _ _ -> inputs
  TermReceiveExact transport lengthValue payload _ _ _ -> [transport, lengthValue, payload]
  TermSendExact transport owner _ _ _ -> [transport, owner]
  TermStore owner result _ _ _ -> [owner, result]
  TermSessionOffer transport arms ->
    transport : [payload | arm <- Map.elems arms, Just payload <- [choiceArmPayloadBinding arm]]
  TermRuntimeChoice _ inputs _ arms ->
    inputs <> [payload | arm <- Map.elems arms, Just payload <- [runtimeChoiceArmPayloadBinding arm]]
  TermReturnScalar valueId -> [valueId]
  TermEnd _ -> []
  TermFatal _ -> []

operationDescription :: SystemsOp -> Text
operationDescription operation = case operation of
  OpRuntimeCall name _ _ _ _ -> "runtime-call:" <> name
  OpSessionSelect _ label _ _ -> "session-select:" <> label
  OpBorrowView {} -> "borrow-view"
  OpCopy {} -> "copy"
  _ -> "operation"

lookupFunction
  :: Text
  -> SystemsProgram
  -> Either ClientOutboundError SystemsFunction
lookupFunction functionName program =
  case Map.lookup functionName (systemsProgramFunctions program) of
    Nothing -> Left (ClientOutboundFunctionMissing functionName)
    Just value -> Right value

lookupBlock
  :: Text
  -> SystemsFunction
  -> BlockId
  -> Either ClientOutboundError SystemsBlock
lookupBlock functionName function blockId =
  case Map.lookup blockId (systemsFunctionBlocks function) of
    Nothing -> Left (ClientOutboundBlockMissing functionName blockId)
    Just value -> Right value

verifyRole
  :: Text
  -> SystemsFunction
  -> ValueId
  -> SystemsValueRole
  -> Either ClientOutboundError ()
verifyRole functionName function valueId expected =
  case Map.lookup valueId (systemsFunctionValues function) of
    Nothing -> Left (ClientOutboundValueMissing functionName valueId)
    Just value -> unless (systemsValueRole value == expected) $
      Left (ClientOutboundValueRoleMismatch functionName valueId (systemsValueRole value))

requireValueAbsent
  :: Text
  -> SystemsFunction
  -> ValueId
  -> Either ClientOutboundError ()
requireValueAbsent functionName function valueId =
  when (Map.member valueId (systemsFunctionValues function)) $
    Left (ClientOutboundUnexpectedValuePresent functionName valueId)

insertValue :: SystemsValue -> Map.Map ValueId SystemsValue -> Map.Map ValueId SystemsValue
insertValue value = Map.insert (systemsValueId value) value

requireDecisionAbsent
  :: Map.Map DecisionId LoweringDecision
  -> DecisionId
  -> Either ClientOutboundError ()
requireDecisionAbsent decisions decisionId =
  when (Map.member decisionId decisions) $
    Left (ClientOutboundDecisionAlreadyPresent decisionId)

verifyDecision
  :: Map.Map DecisionId LoweringDecision
  -> DecisionId
  -> LoweringDecision
  -> Either ClientOutboundError ()
verifyDecision decisions decisionId expected =
  case Map.lookup decisionId decisions of
    Nothing -> Left (ClientOutboundDecisionMissing decisionId)
    Just actual -> unless (actual == expected) $
      Left (ClientOutboundDecisionMismatch decisionId)

rebindDecisionTarget :: Digest -> LoweringDecision -> LoweringDecision
rebindDecisionTarget targetDigest lowering = provisional
  { loweringDecisionDigest = deriveLoweringDecisionDigest provisional }
  where
    provisional = lowering { loweringTargetArtifactDigest = targetDigest }

deriveRecordDecision
  :: Digest
  -> Digest
  -> ClientOutboundWitness
  -> LoweringDecision
deriveRecordDecision sourceDigest targetDigest witness = provisional
  { loweringDecisionDigest = deriveLoweringDecisionDigest provisional }
  where
    provisional = LoweringDecision
      { loweringDecisionId = clientOutboundRecordDecision witness
      , loweringDecisionDigest = Digest ""
      , loweringSourceArtifactDigest = sourceDigest
      , loweringTargetArtifactDigest = targetDigest
      , loweringSourceRepresentation =
          "client Hello/Begin source construction and payload field projections"
      , loweringTargetRepresentation =
          "explicit client outbound runtime semantic values and Hello/Begin record identities"
      , loweringSemanticEntities =
          [ "client.supported_versions"
          , "client.hello"
          , "client.payload_length"
          , "client.payload_kind"
          , "client.begin"
          , "Begin.digestAlg=sha256"
          ]
      , loweringObligationRevisions = []
      , loweringAssuranceEntries = []
      , loweringAssuranceUses = []
      , loweringAction = Materialize
      , loweringRepresentationBefore =
          "source construction/projection expressions implicit in the original Systems sketch"
      , loweringRepresentationAfter =
          "explicit semantic values with exact producer/consumer dataflow"
      , loweringInvariantsPreserved =
          [ "Hello.versions is the exact supported_versions() result"
          , "Begin.length and Begin.kind are projected from the exact client payload"
          , "Begin.digest is the exact SHA-256 result over a shared view of the same payload"
          , "Begin.digestAlg is the static sha256 constructor field"
          ]
      , loweringInvariantsTransferred = []
      , loweringRuntimeResidue =
          [ "physical Hello/Begin representation and serialization remain target-selected"
          , "payload kind representation remains target-selected"
          , "supported-version set representation remains target-selected"
          ]
      , loweringCostClass = Just SemanticRequired
      , loweringCostShape = emptyCostShape
          { costCodeSize = Just "explicit outbound construction/projection dataflow"
          , costFrequency = Just "once per upload path reaching each outbound record"
          }
      , loweringTargetPreconditions =
          [ "client payload owner is live on the version branch"
          , "supported_versions() returns the source semantic version set"
          ]
      , loweringAssumptions = []
      , loweringDerivedObligations = []
      , loweringInspectionPlan =
          [ "verify both sends consume the exact constructed record identity"
          , "verify Begin fields are sourced only from the exact payload/digest values"
          , "verify no physical record layout is selected at Systems"
          ]
      }

deriveBorrowDecision
  :: Digest
  -> Digest
  -> ClientOutboundWitness
  -> LoweringDecision
deriveBorrowDecision sourceDigest targetDigest witness = provisional
  { loweringDecisionDigest = deriveLoweringDecisionDigest provisional }
  where
    provisional = LoweringDecision
      { loweringDecisionId = clientOutboundBorrowDecision witness
      , loweringDecisionDigest = Digest ""
      , loweringSourceArtifactDigest = sourceDigest
      , loweringTargetArtifactDigest = targetDigest
      , loweringSourceRepresentation = "borrow payload as payloadView"
      , loweringTargetRepresentation = "non-owning client payload slice"
      , loweringSemanticEntities =
          [ "client.payload"
          , "client.payload_view"
          ]
      , loweringObligationRevisions = []
      , loweringAssuranceEntries = []
      , loweringAssuranceUses = []
      , loweringAction = Borrow
      , loweringRepresentationBefore = "owned client payload"
      , loweringRepresentationAfter = "shared non-owning digest view + unchanged owner"
      , loweringInvariantsPreserved =
          [ "client payload ownership is not transferred by digest computation"
          , "digest view aliases the exact client payload"
          ]
      , loweringInvariantsTransferred = [clientOutboundBorrowInvariant witness]
      , loweringRuntimeResidue = []
      , loweringCostClass = Just SemanticRequired
      , loweringCostShape = emptyCostShape
          { costBytesCopied = Just "0 expected"
          , costFrequency = Just "once per client payload digest computation"
          }
      , loweringTargetPreconditions = ["client payload owner is live"]
      , loweringAssumptions = []
      , loweringDerivedObligations = []
      , loweringInspectionPlan =
          [ "verify the payload view aliases client.payload"
          , "verify the view is used only by the declared SHA-256 operation"
          ]
      }

deriveDigestDecision
  :: Digest
  -> Digest
  -> ClientOutboundWitness
  -> LoweringDecision
deriveDigestDecision sourceDigest targetDigest witness = provisional
  { loweringDecisionDigest = deriveLoweringDecisionDigest provisional }
  where
    provisional = LoweringDecision
      { loweringDecisionId = clientOutboundDigestDecision witness
      , loweringDecisionDigest = Digest ""
      , loweringSourceArtifactDigest = sourceDigest
      , loweringTargetArtifactDigest = targetDigest
      , loweringSourceRepresentation = "sha256(payloadView)"
      , loweringTargetRepresentation = "explicit runtime SHA-256 computation producing client.declared_digest"
      , loweringSemanticEntities =
          [ "client.payload_view"
          , "client.declared_digest"
          ]
      , loweringObligationRevisions = []
      , loweringAssuranceEntries = []
      , loweringAssuranceUses = []
      , loweringAction = Retain
      , loweringRepresentationBefore = "source SHA-256 expression"
      , loweringRepresentationAfter = "runtime SHA-256 semantic operation"
      , loweringInvariantsPreserved =
          [ "digest input is the exact shared view of client.payload"
          , "digest result flows into the exact constructed Begin record"
          ]
      , loweringInvariantsTransferred = []
      , loweringRuntimeResidue =
          [ "physical SHA-256 provider/implementation remains target-selected"
          , "digest byte representation remains target-selected"
          ]
      , loweringCostClass = Just SemanticRequired
      , loweringCostShape = emptyCostShape
          { costHashOrCryptoWork = Just "SHA-256 over client payload bytes"
          , costFrequency = Just "once per upload reaching Begin construction"
          }
      , loweringTargetPreconditions = ["client.payload_view aliases a live client payload"]
      , loweringAssumptions = []
      , loweringDerivedObligations = []
      , loweringInspectionPlan =
          [ "verify the SHA-256 input is client.payload_view"
          , "verify the result has exactly one semantic consumer: Begin construction"
          ]
      }

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
