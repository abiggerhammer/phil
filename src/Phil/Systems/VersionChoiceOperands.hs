{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.VersionChoiceOperands
  ( VersionChoiceOperandsWitness (..)
  , VersionChoiceOperandsBundle (..)
  , VersionChoiceOperandsError (..)
  , phase0VersionChoiceOperandsWitness
  , phase0VersionChoiceOperandsBundle
  , verifyVersionChoiceOperandsBundle
  , verifyVersionChoiceOperandsWitness
  ) where

import Control.Monad (unless, when)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Assurance.Types
import Phil.Systems.Dataflow
import Phil.Systems.IR
import Phil.Systems.LocalRuntimeChoice
import Phil.Systems.PayloadCancelChoice
  ( PayloadCancelChoiceError
  , phase0PayloadCancelChoiceWitness
  , verifyPayloadCancelChoiceWitness
  )
import Phil.Systems.Verify
import Phil.Systems.VersionSessionChoice

data VersionChoiceOperandsWitness = VersionChoiceOperandsWitness
  { versionOperandsServerFunction :: Text
  , versionOperandsHelloCommitBlock :: BlockId
  , versionOperandsChoiceBlock :: BlockId
  , versionOperandsServerSupported :: ValueId
  , versionOperandsHelloRecord :: ValueId
  , versionOperandsHelloVersions :: ValueId
  , versionOperandsSelectedVersion :: ValueId
  , versionOperandsMaterializeCall :: Text
  , versionOperandsProjectionCall :: Text
  , versionOperandsLoweringDecision :: DecisionId
  }
  deriving (Eq, Show)

data VersionChoiceOperandsBundle = VersionChoiceOperandsBundle
  { versionChoiceOperandsArtifact :: SystemsArtifact
  , versionChoiceOperandsContext :: SystemsVerificationContext
  , versionChoiceOperandsPredecessor :: VersionSessionChoiceBundle
  , versionChoiceOperandsWitness :: VersionChoiceOperandsWitness
  }
  deriving (Eq, Show)

data VersionChoiceOperandsError
  = VersionOperandsPredecessorError VersionSessionChoiceError
  | VersionOperandsPayloadCancelRegression PayloadCancelChoiceError
  | VersionOperandsSystemsError SystemsVerificationError
  | VersionOperandsDataflowError ScalarDataflowError
  | VersionOperandsFunctionMissing Text
  | VersionOperandsBlockMissing Text BlockId
  | VersionOperandsValueAlreadyPresent ValueId
  | VersionOperandsValueMissing ValueId
  | VersionOperandsRoleMismatch ValueId SystemsValueRole
  | VersionOperandsHelloOpsMismatch [SystemsOp]
  | VersionOperandsChoiceMismatch SystemsTerminator
  | VersionOperandsInvariantMismatch InvariantId
  | VersionOperandsServerSelectMismatch BlockId [SystemsOp]
  | VersionOperandsClientOfferMismatch SystemsTerminator
  | VersionOperandsClientRefinementMismatch SystemsTerminator
  | VersionOperandsInputHasProducer ValueId
  | VersionOperandsDecisionAlreadyPresent DecisionId
  | VersionOperandsDecisionMissing DecisionId
  | VersionOperandsDecisionMismatch DecisionId
  deriving (Eq, Show)

phase0VersionChoiceOperandsWitness :: VersionChoiceOperandsWitness
phase0VersionChoiceOperandsWitness = VersionChoiceOperandsWitness
  { versionOperandsServerFunction = "UploadServer"
  , versionOperandsHelloCommitBlock = BlockId "server.hello.commit"
  , versionOperandsChoiceBlock = BlockId "server.version.choose"
  , versionOperandsServerSupported = ValueId "server.supported_versions"
  , versionOperandsHelloRecord = ValueId "server.hello"
  , versionOperandsHelloVersions = ValueId "server.hello_versions"
  , versionOperandsSelectedVersion = ValueId "server.selected_version"
  , versionOperandsMaterializeCall = "materialize recognized Hello"
  , versionOperandsProjectionCall = "project recognized Hello.versions"
  , versionOperandsLoweringDecision = DecisionId "lower.version.choice.operands"
  }

phase0VersionChoiceOperandsBundle
  :: Either VersionChoiceOperandsError VersionChoiceOperandsBundle
phase0VersionChoiceOperandsBundle = do
  predecessor <- mapLeft VersionOperandsPredecessorError phase0VersionSessionChoiceBundle
  let baseArtifact = versionSessionChoiceArtifact predecessor
      baseContext = versionSessionChoiceContext predecessor
      witness = phase0VersionChoiceOperandsWitness
      predecessorDecisions = loweringLedgerDecisions (systemsArtifactLoweringLedger baseArtifact)
  when (Map.member (versionOperandsLoweringDecision witness) predecessorDecisions) $
    Left (VersionOperandsDecisionAlreadyPresent (versionOperandsLoweringDecision witness))
  program <- materializeVersionChoiceOperands witness (systemsArtifactProgram baseArtifact)
  let baseContract = systemsArtifactStageContract baseArtifact
      targetDigest = systemsProgramDigest program
      contract = baseContract
        { stageTargetArtifactDigest = targetDigest
        , stageTraceRelation = stageTraceRelation baseContract <>
            [ "architecture serverSupported binding -> explicit server.supported_versions runtime input"
            , "recognized Hello -> explicit runtime record -> explicit hello.versions value -> choose_supported operand"
            ]
        }
      sourceDigest = stageSourceArtifactDigest contract
      rebound = Map.map (rebindDecisionTarget targetDigest) predecessorDecisions
      decision = deriveVersionOperandsDecision sourceDigest targetDigest witness
      decisions = Map.insert (versionOperandsLoweringDecision witness) decision rebound
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
      bundle = VersionChoiceOperandsBundle artifact context predecessor witness
  verifyVersionChoiceOperandsBundle bundle
  pure bundle

verifyVersionChoiceOperandsBundle
  :: VersionChoiceOperandsBundle
  -> Either VersionChoiceOperandsError ()
verifyVersionChoiceOperandsBundle bundle = do
  mapLeft VersionOperandsPredecessorError $
    verifyVersionSessionChoiceBundle (versionChoiceOperandsPredecessor bundle)
  mapLeft VersionOperandsSystemsError $
    verifySystemsArtifact
      (versionChoiceOperandsContext bundle)
      (versionChoiceOperandsArtifact bundle)
  mapLeft VersionOperandsDataflowError $
    verifyScalarDataflow (versionChoiceOperandsArtifact bundle)
  verifyVersionChoiceOperandsWitness
    (versionChoiceOperandsArtifact bundle)
    (versionChoiceOperandsWitness bundle)

verifyVersionChoiceOperandsWitness
  :: SystemsArtifact
  -> VersionChoiceOperandsWitness
  -> Either VersionChoiceOperandsError ()
verifyVersionChoiceOperandsWitness artifact witness = do
  let program = systemsArtifactProgram artifact
      versionWitness = phase0VersionSessionChoiceWitness
      localWitness = phase0LocalRuntimeChoiceWitness
  server <- lookupFunction (versionOperandsServerFunction witness) program
  verifyRole server (versionOperandsServerSupported witness) (RuntimeInput "SupportedVersions")
  verifyRole server (versionOperandsHelloRecord witness) (RuntimeRecord "Hello")
  verifyRole server (versionOperandsHelloVersions witness) (RuntimeOpaque "VersionSet")
  verifyRole server (versionOperandsSelectedVersion witness) (TypedScalar (ScalarUInt 16))
  unless (not (valueHasProducer server (versionOperandsServerSupported witness))) $
    Left (VersionOperandsInputHasProducer (versionOperandsServerSupported witness))

  helloBlock <- lookupBlock
    (versionOperandsServerFunction witness)
    server
    (versionOperandsHelloCommitBlock witness)
  case systemsBlockOps helloBlock of
    OpCommitIngress {} :
      OpRuntimeCall materializeName [] [helloRecord] Nothing materializeDecision
      : OpRuntimeCall projectionName [projectionInput] [helloVersions] Nothing projectionDecision
      : _
        | materializeName == versionOperandsMaterializeCall witness
            && helloRecord == versionOperandsHelloRecord witness
            && materializeDecision == versionOperandsLoweringDecision witness
            && projectionName == versionOperandsProjectionCall witness
            && projectionInput == versionOperandsHelloRecord witness
            && helloVersions == versionOperandsHelloVersions witness
            && projectionDecision == versionOperandsLoweringDecision witness -> pure ()
    operations -> Left (VersionOperandsHelloOpsMismatch operations)

  choiceBlock <- lookupBlock
    (versionOperandsServerFunction witness)
    server
    (versionOperandsChoiceBlock witness)
  let expectedArms = Map.fromList
        [ ("none", SystemsRuntimeChoiceArm Nothing (localChoiceNoneTarget localWitness))
        , ("some", SystemsRuntimeChoiceArm
            (Just (localChoiceSelectedVersion localWitness))
            (localChoiceSomeTarget localWitness))
        ]
      expectedInputs =
        [ versionOperandsServerSupported witness
        , versionOperandsHelloVersions witness
        ]
  case systemsBlockTerminator choiceBlock of
    TermRuntimeChoice name inputs site arms
      | name == localChoiceName localWitness
          && inputs == expectedInputs
          && site == Nothing
          && arms == expectedArms -> pure ()
    other -> Left (VersionOperandsChoiceMismatch other)
  case Map.lookup
      (localChoiceInvariant localWitness)
      (stageInvariants (systemsArtifactStageContract artifact)) of
    Just StageInvariant
      { stageInvariantClaim = InvariantRuntimeChoice functionName blockId name arms
      }
        | functionName == localChoiceFunction localWitness
            && blockId == localChoiceBlock localWitness
            && name == localChoiceName localWitness
            && arms == expectedArms -> pure ()
    _ -> Left (VersionOperandsInvariantMismatch (localChoiceInvariant localWitness))

  verifyServerSelect
    server
    versionWitness
    (versionChoiceServerUnsupportedBlock versionWitness)
    (versionChoiceUnsupportedLabel versionWitness)
    Nothing
  verifyServerSelect
    server
    versionWitness
    (versionChoiceServerVersionBlock versionWitness)
    (versionChoiceVersionLabel versionWitness)
    (Just (versionChoiceServerSelectedVersion versionWitness))
  verifyClientSemantics artifact versionWitness
  mapLeft VersionOperandsPayloadCancelRegression $
    verifyPayloadCancelChoiceWitness artifact phase0PayloadCancelChoiceWitness

  let decisions = loweringLedgerDecisions (systemsArtifactLoweringLedger artifact)
      sourceDigest = stageSourceArtifactDigest (systemsArtifactStageContract artifact)
      targetDigest = systemsProgramDigest program
      expectedDecision = deriveVersionOperandsDecision sourceDigest targetDigest witness
  case Map.lookup (versionOperandsLoweringDecision witness) decisions of
    Nothing -> Left (VersionOperandsDecisionMissing (versionOperandsLoweringDecision witness))
    Just actual -> unless (actual == expectedDecision) $
      Left (VersionOperandsDecisionMismatch (versionOperandsLoweringDecision witness))

verifyRole
  :: SystemsFunction
  -> ValueId
  -> SystemsValueRole
  -> Either VersionChoiceOperandsError ()
verifyRole function valueId expected =
  case Map.lookup valueId (systemsFunctionValues function) of
    Nothing -> Left (VersionOperandsValueMissing valueId)
    Just SystemsValue { systemsValueRole = actual }
      | actual == expected -> pure ()
      | otherwise -> Left (VersionOperandsRoleMismatch valueId actual)

verifyServerSelect
  :: SystemsFunction
  -> VersionSessionChoiceWitness
  -> BlockId
  -> Text
  -> Maybe ValueId
  -> Either VersionChoiceOperandsError ()
verifyServerSelect server versionWitness blockId label payload = do
  blockValue <- lookupBlock (versionChoiceServerFunction versionWitness) server blockId
  let exact operation = case operation of
        OpSessionSelect transport actualLabel actualPayload decisionId ->
          transport == versionChoiceServerTransport versionWitness
            && actualLabel == label
            && actualPayload == payload
            && decisionId == versionChoiceSelectDecision versionWitness
        _ -> False
  unless (any exact (systemsBlockOps blockValue)) $
    Left (VersionOperandsServerSelectMismatch blockId (systemsBlockOps blockValue))

verifyClientSemantics
  :: SystemsArtifact
  -> VersionSessionChoiceWitness
  -> Either VersionChoiceOperandsError ()
verifyClientSemantics artifact witness = do
  client <- lookupFunction
    (versionChoiceClientFunction witness)
    (systemsArtifactProgram artifact)
  offerBlock <- lookupBlock
    (versionChoiceClientFunction witness)
    client
    (versionChoiceClientOfferBlock witness)
  let expectedArms = Map.fromList
        [ ( versionChoiceUnsupportedLabel witness
          , SystemsChoiceArm Nothing (versionChoiceClientUnsupportedTarget witness)
          )
        , ( versionChoiceVersionLabel witness
          , SystemsChoiceArm
              (Just (versionChoiceClientSelectedVersion witness))
              (versionChoiceClientVersionTarget witness)
          )
        ]
  case systemsBlockTerminator offerBlock of
    TermSessionOffer transport arms
      | transport == versionChoiceClientTransport witness
          && arms == expectedArms -> pure ()
    other -> Left (VersionOperandsClientOfferMismatch other)
  refinementBlock <- lookupBlock
    (versionChoiceClientFunction witness)
    client
    (versionChoiceClientVersionTarget witness)
  case systemsBlockTerminator refinementBlock of
    TermRuntimeCheck inputs _ yes no
      | inputs == [versionChoiceClientSelectedVersion witness]
          && yes == versionChoiceClientVersionSuccess witness
          && no == versionChoiceClientVersionFailure witness -> pure ()
    other -> Left (VersionOperandsClientRefinementMismatch other)

materializeVersionChoiceOperands
  :: VersionChoiceOperandsWitness
  -> SystemsProgram
  -> Either VersionChoiceOperandsError SystemsProgram
materializeVersionChoiceOperands witness program = do
  server <- lookupFunction (versionOperandsServerFunction witness) program
  helloBlock <- lookupBlock
    (versionOperandsServerFunction witness)
    server
    (versionOperandsHelloCommitBlock witness)
  choiceBlock <- lookupBlock
    (versionOperandsServerFunction witness)
    server
    (versionOperandsChoiceBlock witness)
  mapM_ (requireAbsent server)
    [ versionOperandsServerSupported witness
    , versionOperandsHelloRecord witness
    , versionOperandsHelloVersions witness
    ]
  let localWitness = phase0LocalRuntimeChoiceWitness
      expectedArms = Map.fromList
        [ ("none", SystemsRuntimeChoiceArm Nothing (localChoiceNoneTarget localWitness))
        , ("some", SystemsRuntimeChoiceArm
            (Just (localChoiceSelectedVersion localWitness))
            (localChoiceSomeTarget localWitness))
        ]
  case systemsBlockTerminator choiceBlock of
    TermRuntimeChoice name [] Nothing arms
      | name == localChoiceName localWitness && arms == expectedArms -> pure ()
    other -> Left (VersionOperandsChoiceMismatch other)

  let values = Map.insert
        (versionOperandsHelloVersions witness)
        (SystemsValue (versionOperandsHelloVersions witness) (RuntimeOpaque "VersionSet") Nothing) $
        Map.insert
          (versionOperandsHelloRecord witness)
          (SystemsValue (versionOperandsHelloRecord witness) (RuntimeRecord "Hello") Nothing) $
          Map.insert
            (versionOperandsServerSupported witness)
            (SystemsValue (versionOperandsServerSupported witness) (RuntimeInput "SupportedVersions") Nothing)
            (systemsFunctionValues server)
      prefix =
        [ OpRuntimeCall
            (versionOperandsMaterializeCall witness)
            []
            [versionOperandsHelloRecord witness]
            Nothing
            (versionOperandsLoweringDecision witness)
        , OpRuntimeCall
            (versionOperandsProjectionCall witness)
            [versionOperandsHelloRecord witness]
            [versionOperandsHelloVersions witness]
            Nothing
            (versionOperandsLoweringDecision witness)
        ]
      helloBlock' = helloBlock
        { systemsBlockOps = insertAfterCommit prefix (systemsBlockOps helloBlock) }
      choiceBlock' = choiceBlock
        { systemsBlockTerminator = TermRuntimeChoice
            (localChoiceName localWitness)
            [ versionOperandsServerSupported witness
            , versionOperandsHelloVersions witness
            ]
            Nothing
            expectedArms
        }
      server' = server
        { systemsFunctionValues = values
        , systemsFunctionBlocks = Map.insert
            (versionOperandsChoiceBlock witness)
            choiceBlock' $
            Map.insert
              (versionOperandsHelloCommitBlock witness)
              helloBlock'
              (systemsFunctionBlocks server)
        }
  pure program
    { systemsProgramFunctions = Map.insert
        (versionOperandsServerFunction witness)
        server'
        (systemsProgramFunctions program)
    }

insertAfterCommit :: [SystemsOp] -> [SystemsOp] -> [SystemsOp]
insertAfterCommit inserted operations = case operations of
  commit@OpCommitIngress {} : rest -> commit : inserted <> rest
  _ -> operations

requireAbsent :: SystemsFunction -> ValueId -> Either VersionChoiceOperandsError ()
requireAbsent function valueId =
  when (Map.member valueId (systemsFunctionValues function)) $
    Left (VersionOperandsValueAlreadyPresent valueId)

valueHasProducer :: SystemsFunction -> ValueId -> Bool
valueHasProducer function valueId = any blockProduces (Map.elems (systemsFunctionBlocks function))
  where
    blockProduces blockValue =
      any opProduces (systemsBlockOps blockValue)
      || termProduces (systemsBlockTerminator blockValue)
    opProduces operation = case operation of
      OpRuntimeCall { runtimeCallOutputs = outputs } -> valueId `elem` outputs
      OpCopy { copyTarget = output } -> output == valueId
      OpScalarLiteral { scalarLiteralOutput = output } -> output == valueId
      _ -> False
    termProduces terminator = case terminator of
      TermRuntimeChoice { runtimeChoiceArms = arms } ->
        any ((== Just valueId) . runtimeChoiceArmPayloadBinding) (Map.elems arms)
      TermSessionOffer { sessionOfferArms = arms } ->
        any ((== Just valueId) . choiceArmPayloadBinding) (Map.elems arms)
      _ -> False

lookupFunction
  :: Text
  -> SystemsProgram
  -> Either VersionChoiceOperandsError SystemsFunction
lookupFunction functionName program = maybe
  (Left (VersionOperandsFunctionMissing functionName))
  Right
  (Map.lookup functionName (systemsProgramFunctions program))

lookupBlock
  :: Text
  -> SystemsFunction
  -> BlockId
  -> Either VersionChoiceOperandsError SystemsBlock
lookupBlock functionName function blockId = maybe
  (Left (VersionOperandsBlockMissing functionName blockId))
  Right
  (Map.lookup blockId (systemsFunctionBlocks function))

rebindDecisionTarget :: Digest -> LoweringDecision -> LoweringDecision
rebindDecisionTarget targetDigest lowering =
  let rebound = lowering { loweringTargetArtifactDigest = targetDigest }
  in rebound { loweringDecisionDigest = deriveLoweringDecisionDigest rebound }

deriveVersionOperandsDecision
  :: Digest
  -> Digest
  -> VersionChoiceOperandsWitness
  -> LoweringDecision
deriveVersionOperandsDecision sourceDigest targetDigest witness =
  let value = LoweringDecision
        { loweringDecisionId = versionOperandsLoweringDecision witness
        , loweringDecisionDigest = Digest ""
        , loweringSourceArtifactDigest = sourceDigest
        , loweringTargetArtifactDigest = targetDigest
        , loweringSourceRepresentation =
            "architecture serverSupported and recognized hello.versions are implicit at Systems choose_supported site"
        , loweringTargetRepresentation =
            "RuntimeInput server.supported_versions + RuntimeRecord server.hello + RuntimeOpaque server.hello_versions + explicit choose_supported inputs"
        , loweringSemanticEntities =
            [ "serverSupported"
            , "hello"
            , "hello.versions"
            , "choose_supported"
            , "server.selected_version"
            ]
        , loweringObligationRevisions = []
        , loweringAssuranceEntries = []
        , loweringAssuranceUses = []
        , loweringAction = Materialize
        , loweringRepresentationBefore =
            "choose_supported none/some result is explicit but its two source operands are absent"
        , loweringRepresentationAfter =
            "architecture input and recognized Hello.versions have explicit value identity and feed choose_supported in source order"
        , loweringInvariantsPreserved =
            [ "choose_supported retains exact none/some labels and selected UInt16 payload"
            , "serverSupported remains unrestricted architecture input"
            , "hello.versions is derived from the recognized Hello value"
            ]
        , loweringInvariantsTransferred = []
        , loweringRuntimeResidue =
            [ "choose_supported implementation"
            , "SupportedVersions target representation"
            , "VersionSet target representation"
            ]
        , loweringCostClass = Just SemanticRequired
        , loweringCostShape = emptyCostShape
            { costFrequency = Just "once per Hello negotiation" }
        , loweringTargetPreconditions =
            [ "backend must map server.supported_versions as an explicit input, never ambient state"
            , "backend must preserve recognized Hello -> hello.versions provenance"
            ]
        , loweringAssumptions = []
        , loweringDerivedObligations = []
        , loweringInspectionPlan =
            [ "check serverSupported has no local producer"
            , "check Hello record materialization precedes versions projection"
            , "check choose_supported input order is serverSupported, hello.versions"
            ]
        }
  in value { loweringDecisionDigest = deriveLoweringDecisionDigest value }

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform = either (Left . transform) Right
