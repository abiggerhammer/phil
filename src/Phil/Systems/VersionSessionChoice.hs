{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.VersionSessionChoice
  ( VersionSessionChoiceWitness (..)
  , VersionSessionChoiceBundle (..)
  , VersionSessionChoiceError (..)
  , phase0VersionSessionChoiceWitness
  , phase0VersionSessionChoiceBundle
  , verifyVersionSessionChoiceBundle
  , verifyVersionSessionChoiceWitness
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

data VersionSessionChoiceWitness = VersionSessionChoiceWitness
  { versionChoiceServerFunction :: Text
  , versionChoiceServerTransport :: ValueId
  , versionChoiceServerChoiceBlock :: BlockId
  , versionChoiceServerUnsupportedBlock :: BlockId
  , versionChoiceServerVersionBlock :: BlockId
  , versionChoiceServerSelectedVersion :: ValueId
  , versionChoiceUnsupportedLabel :: Text
  , versionChoiceVersionLabel :: Text
  , versionChoiceClientFunction :: Text
  , versionChoiceClientTransport :: ValueId
  , versionChoiceClientOfferBlock :: BlockId
  , versionChoiceClientVersionTarget :: BlockId
  , versionChoiceClientUnsupportedTarget :: BlockId
  , versionChoiceClientSelectedVersion :: ValueId
  , versionChoiceClientLegacyDiscriminator :: ValueId
  , versionChoiceClientLegacyReceiveCall :: Text
  , versionChoiceClientVersionSuccess :: BlockId
  , versionChoiceClientVersionFailure :: BlockId
  , versionChoiceSelectDecision :: DecisionId
  , versionChoiceLoweringDecision :: DecisionId
  }
  deriving (Eq, Show)

data VersionSessionChoiceBundle = VersionSessionChoiceBundle
  { versionSessionChoiceArtifact :: SystemsArtifact
  , versionSessionChoiceContext :: SystemsVerificationContext
  , versionSessionChoicePredecessor :: LocalRuntimeChoiceBundle
  , versionSessionChoiceWitness :: VersionSessionChoiceWitness
  }
  deriving (Eq, Show)

data VersionSessionChoiceError
  = VersionChoicePredecessorError LocalRuntimeChoiceError
  | VersionChoicePayloadCancelRegression PayloadCancelChoiceError
  | VersionChoiceSystemsError SystemsVerificationError
  | VersionChoiceDataflowError ScalarDataflowError
  | VersionChoiceFunctionMissing Text
  | VersionChoiceBlockMissing Text BlockId
  | VersionChoiceValueMissing Text ValueId
  | VersionChoiceValueRoleMismatch Text ValueId SystemsValueRole
  | VersionChoiceUnexpectedValuePresent Text ValueId
  | VersionChoiceLegacyDiscriminatorPresent Text ValueId
  | VersionChoiceLegacyReceivePresent Text BlockId Text
  | VersionChoiceServerSelectMismatch Text BlockId [SystemsOp]
  | VersionChoiceClientOfferMismatch Text BlockId SystemsTerminator
  | VersionChoiceClientRefinementMismatch Text BlockId SystemsTerminator
  | VersionChoiceLocalDecisionMismatch Text BlockId SystemsTerminator
  | VersionChoiceInvariantMismatch InvariantId
  | VersionChoiceDecisionAlreadyPresent DecisionId
  | VersionChoiceDecisionMissing DecisionId
  | VersionChoiceDecisionMismatch DecisionId
  deriving (Eq, Show)

phase0VersionSessionChoiceWitness :: VersionSessionChoiceWitness
phase0VersionSessionChoiceWitness = VersionSessionChoiceWitness
  { versionChoiceServerFunction = "UploadServer"
  , versionChoiceServerTransport = ValueId "server.transport"
  , versionChoiceServerChoiceBlock = BlockId "server.version.choose"
  , versionChoiceServerUnsupportedBlock = BlockId "server.unsupported"
  , versionChoiceServerVersionBlock = BlockId "server.version"
  , versionChoiceServerSelectedVersion = ValueId "server.selected_version"
  , versionChoiceUnsupportedLabel = "unsupported"
  , versionChoiceVersionLabel = "version"
  , versionChoiceClientFunction = "UploadClient"
  , versionChoiceClientTransport = ValueId "client.transport"
  , versionChoiceClientOfferBlock = BlockId "client.entry"
  , versionChoiceClientVersionTarget = BlockId "client.version.check"
  , versionChoiceClientUnsupportedTarget = BlockId "client.unsupported"
  , versionChoiceClientSelectedVersion = ValueId "client.selected_version"
  , versionChoiceClientLegacyDiscriminator = ValueId "client.version_branch"
  , versionChoiceClientLegacyReceiveCall = "receive version/unsupported label"
  , versionChoiceClientVersionSuccess = BlockId "client.version"
  , versionChoiceClientVersionFailure = BlockId "client.version_failure"
  , versionChoiceSelectDecision = DecisionId "lower.session.version_choice"
  , versionChoiceLoweringDecision = DecisionId "lower.session.version_choice"
  }

phase0VersionSessionChoiceBundle
  :: Either VersionSessionChoiceError VersionSessionChoiceBundle
phase0VersionSessionChoiceBundle = do
  predecessor <- mapLeft VersionChoicePredecessorError phase0LocalRuntimeChoiceBundle
  let baseArtifact = localRuntimeChoiceArtifact predecessor
      baseContext = localRuntimeChoiceContext predecessor
      witness = phase0VersionSessionChoiceWitness
      predecessorDecisions = loweringLedgerDecisions (systemsArtifactLoweringLedger baseArtifact)
  when (Map.member (versionChoiceLoweringDecision witness) predecessorDecisions) $
    Left (VersionChoiceDecisionAlreadyPresent (versionChoiceLoweringDecision witness))
  program <- materializeVersionSessionChoice witness (systemsArtifactProgram baseArtifact)
  let baseContract = systemsArtifactStageContract baseArtifact
      targetDigest = systemsProgramDigest program
      contract = baseContract
        { stageTargetArtifactDigest = targetDigest
        , stageTraceRelation = stageTraceRelation baseContract <>
            [ "version/unsupported dual session choice preserves exact labels, transport identity, payload identity, and continuations"
            , "client version refinement consumes the selected UInt16 received on the version arm"
            ]
        }
      sourceDigest = stageSourceArtifactDigest contract
      rebound = Map.map (rebindDecisionTarget targetDigest) predecessorDecisions
      choiceDecision = deriveVersionChoiceDecision sourceDigest targetDigest witness
      decisions = Map.insert (versionChoiceLoweringDecision witness) choiceDecision rebound
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
      bundle = VersionSessionChoiceBundle artifact context predecessor witness
  verifyVersionSessionChoiceBundle bundle
  pure bundle

verifyVersionSessionChoiceBundle
  :: VersionSessionChoiceBundle
  -> Either VersionSessionChoiceError ()
verifyVersionSessionChoiceBundle bundle = do
  mapLeft VersionChoicePredecessorError $
    verifyLocalRuntimeChoiceBundle (versionSessionChoicePredecessor bundle)
  mapLeft VersionChoiceSystemsError $
    verifySystemsArtifact
      (versionSessionChoiceContext bundle)
      (versionSessionChoiceArtifact bundle)
  mapLeft VersionChoiceDataflowError $
    verifyScalarDataflow (versionSessionChoiceArtifact bundle)
  verifyVersionSessionChoiceWitness
    (versionSessionChoiceArtifact bundle)
    (versionSessionChoiceWitness bundle)

verifyVersionSessionChoiceWitness
  :: SystemsArtifact
  -> VersionSessionChoiceWitness
  -> Either VersionSessionChoiceError ()
verifyVersionSessionChoiceWitness artifact witness = do
  let program = systemsArtifactProgram artifact
  server <- lookupFunction (versionChoiceServerFunction witness) program
  client <- lookupFunction (versionChoiceClientFunction witness) program

  verifyTransport
    (versionChoiceServerFunction witness)
    server
    (versionChoiceServerTransport witness)
  verifyTransport
    (versionChoiceClientFunction witness)
    client
    (versionChoiceClientTransport witness)

  verifyUInt16
    (versionChoiceServerFunction witness)
    server
    (versionChoiceServerSelectedVersion witness)
  verifyUInt16
    (versionChoiceClientFunction witness)
    client
    (versionChoiceClientSelectedVersion witness)

  case Map.lookup (versionChoiceClientLegacyDiscriminator witness) (systemsFunctionValues client) of
    Nothing -> pure ()
    Just _ -> Left (VersionChoiceLegacyDiscriminatorPresent
      (versionChoiceClientFunction witness)
      (versionChoiceClientLegacyDiscriminator witness))

  verifyLocalChoicePreserved artifact witness server

  verifyExactServerSelect
    witness
    server
    (versionChoiceServerUnsupportedBlock witness)
    (versionChoiceUnsupportedLabel witness)
    Nothing
  verifyExactServerSelect
    witness
    server
    (versionChoiceServerVersionBlock witness)
    (versionChoiceVersionLabel witness)
    (Just (versionChoiceServerSelectedVersion witness))

  offerBlock <- lookupBlock
    (versionChoiceClientFunction witness)
    client
    (versionChoiceClientOfferBlock witness)
  unless (not (any isLegacyReceive (systemsBlockOps offerBlock))) $
    Left (VersionChoiceLegacyReceivePresent
      (versionChoiceClientFunction witness)
      (versionChoiceClientOfferBlock witness)
      (versionChoiceClientLegacyReceiveCall witness))
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
    other -> Left (VersionChoiceClientOfferMismatch
      (versionChoiceClientFunction witness)
      (versionChoiceClientOfferBlock witness)
      other)

  versionCheck <- lookupBlock
    (versionChoiceClientFunction witness)
    client
    (versionChoiceClientVersionTarget witness)
  case systemsBlockTerminator versionCheck of
    TermRuntimeCheck inputs _ yes no
      | inputs == [versionChoiceClientSelectedVersion witness]
          && yes == versionChoiceClientVersionSuccess witness
          && no == versionChoiceClientVersionFailure witness -> pure ()
    other -> Left (VersionChoiceClientRefinementMismatch
      (versionChoiceClientFunction witness)
      (versionChoiceClientVersionTarget witness)
      other)

  mapLeft VersionChoicePayloadCancelRegression $
    verifyPayloadCancelChoiceWitness artifact phase0PayloadCancelChoiceWitness

  let decisions = loweringLedgerDecisions (systemsArtifactLoweringLedger artifact)
      sourceDigest = stageSourceArtifactDigest (systemsArtifactStageContract artifact)
      targetDigest = systemsProgramDigest program
      expectedDecision = deriveVersionChoiceDecision sourceDigest targetDigest witness
  case Map.lookup (versionChoiceLoweringDecision witness) decisions of
    Nothing -> Left (VersionChoiceDecisionMissing (versionChoiceLoweringDecision witness))
    Just actual -> unless (actual == expectedDecision) $
      Left (VersionChoiceDecisionMismatch (versionChoiceLoweringDecision witness))
  where
    isLegacyReceive operation = case operation of
      OpRuntimeCall { runtimeCallName = name } ->
        name == versionChoiceClientLegacyReceiveCall witness
      _ -> False

verifyTransport
  :: Text
  -> SystemsFunction
  -> ValueId
  -> Either VersionSessionChoiceError ()
verifyTransport functionName function valueId = do
  value <- lookupValue functionName function valueId
  case systemsValueRole value of
    TransportHandle -> pure ()
    other -> Left (VersionChoiceValueRoleMismatch functionName valueId other)

verifyUInt16
  :: Text
  -> SystemsFunction
  -> ValueId
  -> Either VersionSessionChoiceError ()
verifyUInt16 functionName function valueId = do
  value <- lookupValue functionName function valueId
  case systemsValueRole value of
    TypedScalar (ScalarUInt 16) -> pure ()
    other -> Left (VersionChoiceValueRoleMismatch functionName valueId other)

verifyLocalChoicePreserved
  :: SystemsArtifact
  -> VersionSessionChoiceWitness
  -> SystemsFunction
  -> Either VersionSessionChoiceError ()
verifyLocalChoicePreserved artifact witness server = do
  let localWitness = phase0LocalRuntimeChoiceWitness
      expectedArms = Map.fromList
        [ ("none", SystemsRuntimeChoiceArm Nothing (localChoiceNoneTarget localWitness))
        , ("some", SystemsRuntimeChoiceArm
            (Just (localChoiceSelectedVersion localWitness))
            (localChoiceSomeTarget localWitness))
        ]
  choiceBlock <- lookupBlock
    (versionChoiceServerFunction witness)
    server
    (versionChoiceServerChoiceBlock witness)
  case systemsBlockTerminator choiceBlock of
    TermRuntimeChoice name inputs site arms
      | name == localChoiceName localWitness
          && null inputs
          && site == Nothing
          && arms == expectedArms -> pure ()
    other -> Left (VersionChoiceLocalDecisionMismatch
      (versionChoiceServerFunction witness)
      (versionChoiceServerChoiceBlock witness)
      other)
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
    _ -> Left (VersionChoiceInvariantMismatch (localChoiceInvariant localWitness))

verifyExactServerSelect
  :: VersionSessionChoiceWitness
  -> SystemsFunction
  -> BlockId
  -> Text
  -> Maybe ValueId
  -> Either VersionSessionChoiceError ()
verifyExactServerSelect witness server blockId label payload = do
  blockValue <- lookupBlock (versionChoiceServerFunction witness) server blockId
  let exact operation = case operation of
        OpSessionSelect transport actualLabel actualPayload decisionId ->
          transport == versionChoiceServerTransport witness
            && actualLabel == label
            && actualPayload == payload
            && decisionId == versionChoiceSelectDecision witness
        _ -> False
      legacy operation = case operation of
        OpRuntimeCall { runtimeCallName = name } -> name == "select " <> label
        _ -> False
  unless (any exact (systemsBlockOps blockValue) && not (any legacy (systemsBlockOps blockValue))) $
    Left (VersionChoiceServerSelectMismatch
      (versionChoiceServerFunction witness)
      blockId
      (systemsBlockOps blockValue))

materializeVersionSessionChoice
  :: VersionSessionChoiceWitness
  -> SystemsProgram
  -> Either VersionSessionChoiceError SystemsProgram
materializeVersionSessionChoice witness program = do
  server <- lookupFunction (versionChoiceServerFunction witness) program
  client <- lookupFunction (versionChoiceClientFunction witness) program
  serverUnsupported <- lookupBlock
    (versionChoiceServerFunction witness)
    server
    (versionChoiceServerUnsupportedBlock witness)
  serverVersion <- lookupBlock
    (versionChoiceServerFunction witness)
    server
    (versionChoiceServerVersionBlock witness)
  clientOffer <- lookupBlock
    (versionChoiceClientFunction witness)
    client
    (versionChoiceClientOfferBlock witness)
  clientVersionCheck <- lookupBlock
    (versionChoiceClientFunction witness)
    client
    (versionChoiceClientVersionTarget witness)

  when (Map.member (versionChoiceClientSelectedVersion witness) (systemsFunctionValues client)) $
    Left (VersionChoiceUnexpectedValuePresent
      (versionChoiceClientFunction witness)
      (versionChoiceClientSelectedVersion witness))

  case systemsBlockTerminator clientOffer of
    TermBranch condition yes no
      | condition == versionChoiceClientLegacyDiscriminator witness
          && yes == versionChoiceClientVersionTarget witness
          && no == versionChoiceClientUnsupportedTarget witness -> pure ()
    other -> Left (VersionChoiceClientOfferMismatch
      (versionChoiceClientFunction witness)
      (versionChoiceClientOfferBlock witness)
      other)

  case systemsBlockTerminator clientVersionCheck of
    TermRuntimeCheck [] _ yes no
      | yes == versionChoiceClientVersionSuccess witness
          && no == versionChoiceClientVersionFailure witness -> pure ()
    other -> Left (VersionChoiceClientRefinementMismatch
      (versionChoiceClientFunction witness)
      (versionChoiceClientVersionTarget witness)
      other)

  let serverUnsupported' = serverUnsupported
        { systemsBlockOps = replaceLegacySelect
            (versionChoiceUnsupportedLabel witness)
            Nothing
            (systemsBlockOps serverUnsupported)
        }
      serverVersion' = serverVersion
        { systemsBlockOps = replaceLegacySelect
            (versionChoiceVersionLabel witness)
            (Just (versionChoiceServerSelectedVersion witness))
            (systemsBlockOps serverVersion)
        }
      serverBlocks = Map.insert
        (versionChoiceServerVersionBlock witness)
        serverVersion' $
        Map.insert
          (versionChoiceServerUnsupportedBlock witness)
          serverUnsupported'
          (systemsFunctionBlocks server)
      server' = server { systemsFunctionBlocks = serverBlocks }

      selectedValue = SystemsValue
        (versionChoiceClientSelectedVersion witness)
        (TypedScalar (ScalarUInt 16))
        Nothing
      clientValues = Map.insert
        (versionChoiceClientSelectedVersion witness)
        selectedValue $
        Map.delete
          (versionChoiceClientLegacyDiscriminator witness)
          (systemsFunctionValues client)
      clientArms = Map.fromList
        [ ( versionChoiceUnsupportedLabel witness
          , SystemsChoiceArm Nothing (versionChoiceClientUnsupportedTarget witness)
          )
        , ( versionChoiceVersionLabel witness
          , SystemsChoiceArm
              (Just (versionChoiceClientSelectedVersion witness))
              (versionChoiceClientVersionTarget witness)
          )
        ]
      clientOffer' = clientOffer
        { systemsBlockOps = filter (not . isLegacyReceive) (systemsBlockOps clientOffer)
        , systemsBlockTerminator = TermSessionOffer
            (versionChoiceClientTransport witness)
            clientArms
        }
      clientVersionCheck' = clientVersionCheck
        { systemsBlockTerminator = case systemsBlockTerminator clientVersionCheck of
            TermRuntimeCheck _ site yes no ->
              TermRuntimeCheck [versionChoiceClientSelectedVersion witness] site yes no
            other -> other
        }
      clientBlocks = Map.insert
        (versionChoiceClientVersionTarget witness)
        clientVersionCheck' $
        Map.insert
          (versionChoiceClientOfferBlock witness)
          clientOffer'
          (systemsFunctionBlocks client)
      client' = client
        { systemsFunctionValues = clientValues
        , systemsFunctionBlocks = clientBlocks
        }
      functions = Map.insert
        (versionChoiceClientFunction witness)
        client' $
        Map.insert
          (versionChoiceServerFunction witness)
          server'
          (systemsProgramFunctions program)
  pure program { systemsProgramFunctions = functions }
  where
    replaceLegacySelect label payload operations =
      case break (legacySelect label payload) operations of
        (before, _old : after) ->
          before <>
          [ OpSessionSelect
              { sessionSelectTransport = versionChoiceServerTransport witness
              , sessionSelectLabel = label
              , sessionSelectPayload = payload
              , sessionSelectDecision = versionChoiceSelectDecision witness
              }
          ] <> after
        _ -> operations

    legacySelect label payload operation = case operation of
      OpRuntimeCall
        { runtimeCallName = name
        , runtimeCallInputs = inputs
        , runtimeCallOutputs = outputs
        , runtimeCallSite = site
        }
          -> name == "select " <> label
              && inputs == versionChoiceServerTransport witness : maybe [] pure payload
              && null outputs
              && site == Nothing
      _ -> False

    isLegacyReceive operation = case operation of
      OpRuntimeCall
        { runtimeCallName = name
        , runtimeCallInputs = inputs
        , runtimeCallOutputs = outputs
        , runtimeCallSite = site
        }
          -> name == versionChoiceClientLegacyReceiveCall witness
              && inputs == [versionChoiceClientTransport witness]
              && outputs == [versionChoiceClientLegacyDiscriminator witness]
              && site == Nothing
      _ -> False

lookupFunction
  :: Text
  -> SystemsProgram
  -> Either VersionSessionChoiceError SystemsFunction
lookupFunction functionName program =
  case Map.lookup functionName (systemsProgramFunctions program) of
    Nothing -> Left (VersionChoiceFunctionMissing functionName)
    Just value -> Right value

lookupValue
  :: Text
  -> SystemsFunction
  -> ValueId
  -> Either VersionSessionChoiceError SystemsValue
lookupValue functionName function valueId =
  case Map.lookup valueId (systemsFunctionValues function) of
    Nothing -> Left (VersionChoiceValueMissing functionName valueId)
    Just value -> Right value

lookupBlock
  :: Text
  -> SystemsFunction
  -> BlockId
  -> Either VersionSessionChoiceError SystemsBlock
lookupBlock functionName function blockId =
  case Map.lookup blockId (systemsFunctionBlocks function) of
    Nothing -> Left (VersionChoiceBlockMissing functionName blockId)
    Just value -> Right value

rebindDecisionTarget :: Digest -> LoweringDecision -> LoweringDecision
rebindDecisionTarget targetDigest lowering =
  let rebound = lowering { loweringTargetArtifactDigest = targetDigest }
  in rebound { loweringDecisionDigest = deriveLoweringDecisionDigest rebound }

deriveVersionChoiceDecision
  :: Digest
  -> Digest
  -> VersionSessionChoiceWitness
  -> LoweringDecision
deriveVersionChoiceDecision sourceDigest targetDigest witness =
  let value = LoweringDecision
        { loweringDecisionId = versionChoiceLoweringDecision witness
        , loweringDecisionDigest = Digest ""
        , loweringSourceArtifactDigest = sourceDigest
        , loweringTargetArtifactDigest = targetDigest
        , loweringSourceRepresentation = "server generic select unsupported/version calls; client receive version/unsupported label -> Bool"
        , loweringTargetRepresentation = "server semantic session selects unsupported/version(selected); client semantic session offer with branch-local UInt16 selected version"
        , loweringSemanticEntities =
            [ "unsupported"
            , "version(selected)"
            , "server.selected_version"
            , "client.selected_version"
            ]
        , loweringObligationRevisions = []
        , loweringAssuranceEntries = []
        , loweringAssuranceUses = []
        , loweringAction = Materialize
        , loweringRepresentationBefore = "anonymous client Bool discriminator; selected version absent from client Systems dataflow"
        , loweringRepresentationAfter = "dual semantic labels with exact transport identity and branch-local UInt16 payload"
        , loweringInvariantsPreserved =
            [ "server choose_supported remains local none/some computation"
            , "unsupported carries no branch payload"
            , "version carries exactly the selected UInt16"
            , "client refinement consumes exactly the received selected version"
            ]
        , loweringInvariantsTransferred = []
        , loweringRuntimeResidue =
            [ "wire discriminator representation remains target-selected"
            , "UInt16 payload wire layout remains target-selected"
            ]
        , loweringCostClass = Just SemanticRequired
        , loweringCostShape = emptyCostShape
            { costBranchOrDispatch = Just "one peer-visible version/unsupported choice"
            , costFrequency = Just "once per Hello negotiation"
            }
        , loweringTargetPreconditions =
            [ "version offer target is dedicated to its branch-local UInt16 binding" ]
        , loweringAssumptions = []
        , loweringDerivedObligations = []
        , loweringInspectionPlan =
            [ "check exact server labels and payload identity"
            , "check exact client offer labels, payload binding, and continuations"
            , "check client version refinement consumes client.selected_version"
            ]
        }
  in value { loweringDecisionDigest = deriveLoweringDecisionDigest value }

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
