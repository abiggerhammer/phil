{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.PayloadCancelChoice
  ( PayloadCancelChoiceWitness (..)
  , PayloadCancelChoiceBundle (..)
  , PayloadCancelChoiceError (..)
  , phase0PayloadCancelChoiceWitness
  , phase0PayloadCancelChoiceBundle
  , verifyPayloadCancelChoiceBundle
  , verifyPayloadCancelChoiceWitness
  ) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Assurance.Types
import Phil.Systems.IR
import Phil.Systems.SessionChoice
import Phil.Systems.Verify

data PayloadCancelChoiceWitness = PayloadCancelChoiceWitness
  { payloadCancelServerFunction :: Text
  , payloadCancelServerOfferBlock :: BlockId
  , payloadCancelServerTransport :: ValueId
  , payloadCancelPayloadLabel :: Text
  , payloadCancelPayloadTarget :: BlockId
  , payloadCancelCancelLabel :: Text
  , payloadCancelCancelTarget :: BlockId
  , payloadCancelLegacyDiscriminator :: ValueId
  , payloadCancelLegacyReceiveCall :: Text
  , payloadCancelClientFunction :: Text
  , payloadCancelClientTransport :: ValueId
  , payloadCancelClientDecisionBlock :: BlockId
  , payloadCancelClientDecisionValue :: ValueId
  , payloadCancelClientPayloadSelectBlock :: BlockId
  , payloadCancelClientCancelSelectBlock :: BlockId
  , payloadCancelSelectDecision :: DecisionId
  , payloadCancelLoweringDecision :: DecisionId
  }
  deriving (Eq, Show)

data PayloadCancelChoiceBundle = PayloadCancelChoiceBundle
  { payloadCancelChoiceArtifact :: SystemsArtifact
  , payloadCancelChoiceContext :: SystemsVerificationContext
  , payloadCancelChoicePredecessor :: SessionChoiceBundle
  , payloadCancelChoiceWitness :: PayloadCancelChoiceWitness
  }
  deriving (Eq, Show)

data PayloadCancelChoiceError
  = PayloadCancelSessionChoiceError SessionChoiceError
  | PayloadCancelSystemsError SystemsVerificationError
  | PayloadCancelFunctionMissing Text
  | PayloadCancelBlockMissing Text BlockId
  | PayloadCancelValueMissing Text ValueId
  | PayloadCancelValueRoleMismatch Text ValueId SystemsValueRole
  | PayloadCancelLegacyDiscriminatorPresent Text ValueId
  | PayloadCancelLegacyReceivePresent Text BlockId Text
  | PayloadCancelServerOfferMismatch Text BlockId SystemsTerminator
  | PayloadCancelClientSelectMismatch Text BlockId [SystemsOp]
  | PayloadCancelLocalDecisionMismatch Text BlockId SystemsTerminator
  | PayloadCancelFinalResponseRegression SessionChoiceError
  | PayloadCancelDecisionMissing DecisionId
  | PayloadCancelDecisionMismatch DecisionId
  deriving (Eq, Show)

phase0PayloadCancelChoiceWitness :: PayloadCancelChoiceWitness
phase0PayloadCancelChoiceWitness = PayloadCancelChoiceWitness
  { payloadCancelServerFunction = "UploadServer"
  , payloadCancelServerOfferBlock = BlockId "server.proceed"
  , payloadCancelServerTransport = ValueId "server.transport"
  , payloadCancelPayloadLabel = "payload"
  , payloadCancelPayloadTarget = BlockId "server.payload"
  , payloadCancelCancelLabel = "cancel"
  , payloadCancelCancelTarget = BlockId "server.cancel"
  , payloadCancelLegacyDiscriminator = ValueId "server.payload_choice"
  , payloadCancelLegacyReceiveCall = "receive payload/cancel label"
  , payloadCancelClientFunction = "UploadClient"
  , payloadCancelClientTransport = ValueId "client.transport"
  , payloadCancelClientDecisionBlock = BlockId "client.proceed"
  , payloadCancelClientDecisionValue = ValueId "client.should_cancel"
  , payloadCancelClientPayloadSelectBlock = BlockId "client.payload"
  , payloadCancelClientCancelSelectBlock = BlockId "client.cancel"
  , payloadCancelSelectDecision = DecisionId "lower.session.payload_cancel_choice"
  , payloadCancelLoweringDecision = DecisionId "lower.session.payload_cancel_choice"
  }

phase0PayloadCancelChoiceBundle
  :: Either PayloadCancelChoiceError PayloadCancelChoiceBundle
phase0PayloadCancelChoiceBundle = do
  predecessor <- mapLeft PayloadCancelSessionChoiceError phase0SessionChoiceBundle
  let baseArtifact = sessionChoiceArtifact predecessor
      baseContext = sessionChoiceContext predecessor
      witness = phase0PayloadCancelChoiceWitness
  program <- materializePayloadCancelChoice witness (systemsArtifactProgram baseArtifact)
  let baseContract = systemsArtifactStageContract baseArtifact
      targetDigest = systemsProgramDigest program
      contract = baseContract
        { stageTargetArtifactDigest = targetDigest
        , stageTraceRelation = stageTraceRelation baseContract <>
            [ "payload/cancel dual session choice preserves exact labels, transport identity, and continuations"
            , "should_cancel_upload remains a local computational Boolean branch"
            ]
        }
      sourceDigest = stageSourceArtifactDigest contract
      predecessorDecisions = loweringLedgerDecisions (systemsArtifactLoweringLedger baseArtifact)
      rebound = Map.map (rebindDecisionTarget targetDigest) predecessorDecisions
      choiceDecision = derivePayloadCancelDecision sourceDigest targetDigest witness
      decisions = Map.insert (payloadCancelLoweringDecision witness) choiceDecision rebound
      loweringRoot = deriveLoweringLedgerRoot decisions
      loweringLedger = LoweringLedger decisions loweringRoot
      artifact = SystemsArtifact program contract loweringLedger
      assuranceLedger = systemsAssuranceLedger baseContext
      baseManifest = systemsAssuranceManifest baseContext
      provisionalManifest = baseManifest
        { manifestImplementationDigest = systemsArtifactDigest artifact
        , manifestLoweringLedgerRoot = loweringRoot
        }
      manifest = provisionalManifest
        { manifestId = deriveManifestId assuranceLedger provisionalManifest }
      baseAssuranceContext = systemsAssuranceVerificationContext baseContext
      assuranceContext = baseAssuranceContext
        { verificationImplementationDigest = systemsArtifactDigest artifact
        , verificationLoweringLedgerRoot = loweringRoot
        }
      context = baseContext
        { systemsAssuranceManifest = manifest
        , systemsAssuranceVerificationContext = assuranceContext
        }
      bundle = PayloadCancelChoiceBundle artifact context predecessor witness
  verifyPayloadCancelChoiceBundle bundle
  pure bundle

verifyPayloadCancelChoiceBundle
  :: PayloadCancelChoiceBundle
  -> Either PayloadCancelChoiceError ()
verifyPayloadCancelChoiceBundle bundle = do
  mapLeft PayloadCancelSessionChoiceError $
    verifySessionChoiceBundle (payloadCancelChoicePredecessor bundle)
  mapLeft PayloadCancelSystemsError $
    verifySystemsArtifact
      (payloadCancelChoiceContext bundle)
      (payloadCancelChoiceArtifact bundle)
  verifyPayloadCancelChoiceWitness
    (payloadCancelChoiceArtifact bundle)
    (payloadCancelChoiceWitness bundle)

verifyPayloadCancelChoiceWitness
  :: SystemsArtifact
  -> PayloadCancelChoiceWitness
  -> Either PayloadCancelChoiceError ()
verifyPayloadCancelChoiceWitness artifact witness = do
  let program = systemsArtifactProgram artifact
  server <- lookupFunction (payloadCancelServerFunction witness) program
  client <- lookupFunction (payloadCancelClientFunction witness) program

  verifyTransport
    (payloadCancelServerFunction witness)
    server
    (payloadCancelServerTransport witness)
  verifyTransport
    (payloadCancelClientFunction witness)
    client
    (payloadCancelClientTransport witness)

  localDecision <- lookupValue
    (payloadCancelClientFunction witness)
    client
    (payloadCancelClientDecisionValue witness)
  case systemsValueRole localDecision of
    RuntimeScalar "Bool" -> pure ()
    other -> Left (PayloadCancelValueRoleMismatch
      (payloadCancelClientFunction witness)
      (payloadCancelClientDecisionValue witness)
      other)

  case Map.lookup (payloadCancelLegacyDiscriminator witness) (systemsFunctionValues server) of
    Nothing -> pure ()
    Just _ -> Left (PayloadCancelLegacyDiscriminatorPresent
      (payloadCancelServerFunction witness)
      (payloadCancelLegacyDiscriminator witness))

  offerBlock <- lookupBlock
    (payloadCancelServerFunction witness)
    server
    (payloadCancelServerOfferBlock witness)
  unless (not (any isLegacyReceive (systemsBlockOps offerBlock))) $
    Left (PayloadCancelLegacyReceivePresent
      (payloadCancelServerFunction witness)
      (payloadCancelServerOfferBlock witness)
      (payloadCancelLegacyReceiveCall witness))

  let expectedArms = Map.fromList
        [ ( payloadCancelPayloadLabel witness
          , SystemsChoiceArm Nothing (payloadCancelPayloadTarget witness)
          )
        , ( payloadCancelCancelLabel witness
          , SystemsChoiceArm Nothing (payloadCancelCancelTarget witness)
          )
        ]
  case systemsBlockTerminator offerBlock of
    TermSessionOffer transport arms
      | transport == payloadCancelServerTransport witness
          && arms == expectedArms -> pure ()
    other -> Left (PayloadCancelServerOfferMismatch
      (payloadCancelServerFunction witness)
      (payloadCancelServerOfferBlock witness)
      other)

  verifyExactSelect
    client
    (payloadCancelClientFunction witness)
    (payloadCancelClientPayloadSelectBlock witness)
    (payloadCancelClientTransport witness)
    (payloadCancelPayloadLabel witness)
    (payloadCancelSelectDecision witness)
  verifyExactSelect
    client
    (payloadCancelClientFunction witness)
    (payloadCancelClientCancelSelectBlock witness)
    (payloadCancelClientTransport witness)
    (payloadCancelCancelLabel witness)
    (payloadCancelSelectDecision witness)

  decisionBlock <- lookupBlock
    (payloadCancelClientFunction witness)
    client
    (payloadCancelClientDecisionBlock witness)
  case systemsBlockTerminator decisionBlock of
    TermBranch condition yes no
      | condition == payloadCancelClientDecisionValue witness
          && yes == payloadCancelClientCancelSelectBlock witness
          && no == payloadCancelClientPayloadSelectBlock witness -> pure ()
    other -> Left (PayloadCancelLocalDecisionMismatch
      (payloadCancelClientFunction witness)
      (payloadCancelClientDecisionBlock witness)
      other)

  mapLeft PayloadCancelFinalResponseRegression $
    verifySessionChoiceWitness artifact phase0FinalResponseChoiceWitness

  let decisions = loweringLedgerDecisions (systemsArtifactLoweringLedger artifact)
      sourceDigest = stageSourceArtifactDigest (systemsArtifactStageContract artifact)
      targetDigest = systemsProgramDigest program
      expectedDecision = derivePayloadCancelDecision sourceDigest targetDigest witness
  case Map.lookup (payloadCancelLoweringDecision witness) decisions of
    Nothing -> Left (PayloadCancelDecisionMissing (payloadCancelLoweringDecision witness))
    Just actual -> unless (actual == expectedDecision) $
      Left (PayloadCancelDecisionMismatch (payloadCancelLoweringDecision witness))
  where
    isLegacyReceive operation = case operation of
      OpRuntimeCall { runtimeCallName = name } ->
        name == payloadCancelLegacyReceiveCall witness
      _ -> False

verifyTransport
  :: Text
  -> SystemsFunction
  -> ValueId
  -> Either PayloadCancelChoiceError ()
verifyTransport functionName function valueId = do
  value <- lookupValue functionName function valueId
  case systemsValueRole value of
    TransportHandle -> pure ()
    other -> Left (PayloadCancelValueRoleMismatch functionName valueId other)

verifyExactSelect
  :: SystemsFunction
  -> Text
  -> BlockId
  -> ValueId
  -> Text
  -> DecisionId
  -> Either PayloadCancelChoiceError ()
verifyExactSelect function functionName blockId transport label decisionId = do
  blockValue <- lookupBlock functionName function blockId
  case systemsBlockOps blockValue of
    OpSessionSelect
      { sessionSelectTransport = actualTransport
      , sessionSelectLabel = actualLabel
      , sessionSelectPayload = Nothing
      , sessionSelectDecision = actualDecision
      } : _
        | actualTransport == transport
            && actualLabel == label
            && actualDecision == decisionId
            && not (any (legacySelect label) (systemsBlockOps blockValue)) -> pure ()
    operations -> Left (PayloadCancelClientSelectMismatch functionName blockId operations)
  where
    legacySelect expected operation = case operation of
      OpRuntimeCall { runtimeCallName = name } -> name == "select " <> expected
      _ -> False

materializePayloadCancelChoice
  :: PayloadCancelChoiceWitness
  -> SystemsProgram
  -> Either PayloadCancelChoiceError SystemsProgram
materializePayloadCancelChoice witness program = do
  server <- lookupFunction (payloadCancelServerFunction witness) program
  client <- lookupFunction (payloadCancelClientFunction witness) program
  serverOffer <- lookupBlock
    (payloadCancelServerFunction witness)
    server
    (payloadCancelServerOfferBlock witness)
  clientPayload <- lookupBlock
    (payloadCancelClientFunction witness)
    client
    (payloadCancelClientPayloadSelectBlock witness)
  clientCancel <- lookupBlock
    (payloadCancelClientFunction witness)
    client
    (payloadCancelClientCancelSelectBlock witness)

  let serverValues = Map.delete
        (payloadCancelLegacyDiscriminator witness)
        (systemsFunctionValues server)
      serverOffer' = serverOffer
        { systemsBlockOps = filter (not . isLegacyReceive) (systemsBlockOps serverOffer)
        , systemsBlockTerminator = TermSessionOffer
            (payloadCancelServerTransport witness)
            (Map.fromList
              [ ( payloadCancelPayloadLabel witness
                , SystemsChoiceArm Nothing (payloadCancelPayloadTarget witness)
                )
              , ( payloadCancelCancelLabel witness
                , SystemsChoiceArm Nothing (payloadCancelCancelTarget witness)
                )
              ])
        }
      server' = server
        { systemsFunctionValues = serverValues
        , systemsFunctionBlocks = Map.insert
            (payloadCancelServerOfferBlock witness)
            serverOffer'
            (systemsFunctionBlocks server)
        }
      clientPayload' = clientPayload
        { systemsBlockOps = replaceSelect
            (payloadCancelPayloadLabel witness)
            (systemsBlockOps clientPayload)
        }
      clientCancel' = clientCancel
        { systemsBlockOps = replaceSelect
            (payloadCancelCancelLabel witness)
            (systemsBlockOps clientCancel)
        }
      clientBlocks = Map.insert
        (payloadCancelClientCancelSelectBlock witness)
        clientCancel' $
        Map.insert
          (payloadCancelClientPayloadSelectBlock witness)
          clientPayload'
          (systemsFunctionBlocks client)
      client' = client { systemsFunctionBlocks = clientBlocks }
      functions = Map.insert
        (payloadCancelClientFunction witness)
        client' $
        Map.insert
          (payloadCancelServerFunction witness)
          server'
          (systemsProgramFunctions program)
  pure program { systemsProgramFunctions = functions }
  where
    isLegacyReceive operation = case operation of
      OpRuntimeCall { runtimeCallName = name } ->
        name == payloadCancelLegacyReceiveCall witness
      _ -> False

    replaceSelect label operations =
      case break (legacySelect label) operations of
        (before, _old : after) ->
          before <>
          [ OpSessionSelect
              { sessionSelectTransport = payloadCancelClientTransport witness
              , sessionSelectLabel = label
              , sessionSelectPayload = Nothing
              , sessionSelectDecision = payloadCancelSelectDecision witness
              }
          ] <> after
        _ -> operations

    legacySelect label operation = case operation of
      OpRuntimeCall
        { runtimeCallName = name
        , runtimeCallInputs = inputs
        , runtimeCallOutputs = outputs
        , runtimeCallSite = site
        }
          -> name == "select " <> label
              && inputs == [payloadCancelClientTransport witness]
              && null outputs
              && site == Nothing
      _ -> False

lookupFunction
  :: Text
  -> SystemsProgram
  -> Either PayloadCancelChoiceError SystemsFunction
lookupFunction functionName program =
  case Map.lookup functionName (systemsProgramFunctions program) of
    Nothing -> Left (PayloadCancelFunctionMissing functionName)
    Just value -> Right value

lookupValue
  :: Text
  -> SystemsFunction
  -> ValueId
  -> Either PayloadCancelChoiceError SystemsValue
lookupValue functionName function valueId =
  case Map.lookup valueId (systemsFunctionValues function) of
    Nothing -> Left (PayloadCancelValueMissing functionName valueId)
    Just value -> Right value

lookupBlock
  :: Text
  -> SystemsFunction
  -> BlockId
  -> Either PayloadCancelChoiceError SystemsBlock
lookupBlock functionName function blockId =
  case Map.lookup blockId (systemsFunctionBlocks function) of
    Nothing -> Left (PayloadCancelBlockMissing functionName blockId)
    Just value -> Right value

rebindDecisionTarget :: Digest -> LoweringDecision -> LoweringDecision
rebindDecisionTarget targetDigest lowering =
  let rebound = lowering { loweringTargetArtifactDigest = targetDigest }
  in rebound { loweringDecisionDigest = deriveLoweringDecisionDigest rebound }

derivePayloadCancelDecision
  :: Digest
  -> Digest
  -> PayloadCancelChoiceWitness
  -> LoweringDecision
derivePayloadCancelDecision sourceDigest targetDigest witness =
  let provisional = LoweringDecision
        { loweringDecisionId = payloadCancelLoweringDecision witness
        , loweringDecisionDigest = Digest ""
        , loweringSourceArtifactDigest = sourceDigest
        , loweringTargetArtifactDigest = targetDigest
        , loweringSourceRepresentation =
            "dual payload/cancel session choice represented as generic runtime calls and anonymous Bool"
        , loweringTargetRepresentation =
            "OpSessionSelect on client plus TermSessionOffer on server"
        , loweringSemanticEntities =
            [ "client select payload"
            , "client select cancel"
            , "server offer payload/cancel"
            ]
        , loweringObligationRevisions = []
        , loweringAssuranceEntries = []
        , loweringAssuranceUses = []
        , loweringAction = Materialize
        , loweringRepresentationBefore =
            "generic select calls plus receive-label runtime call and payload_choice Bool"
        , loweringRepresentationAfter =
            "semantic session labels, exact transport identity, and exact continuations on both dual endpoints"
        , loweringInvariantsPreserved =
            [ "payload and cancel labels remain protocol identities"
            , "client payload selection is dual to server payload arm"
            , "client cancel selection is dual to server cancel arm"
            , "payload/cancel carries no branch payload in Phase 0"
            , "should_cancel_upload remains local computation rather than protocol state"
            , "no wire discriminator or target layout is chosen in Systems"
            ]
        , loweringInvariantsTransferred = []
        , loweringRuntimeResidue =
            [ "client-selected session label remains runtime work"
            , "server peer-selected session offer remains runtime work"
            , "physical select/offer encoding is deferred to a target profile"
            ]
        , loweringCostClass = Just SemanticRequired
        , loweringCostShape = emptyCostShape
            { costBranchOrDispatch = Just "one local decision plus one protocol select/offer"
            , costFrequency = Just "per upload payload attempt"
            }
        , loweringTargetPreconditions =
            [ "backend must explicitly lower OpSessionSelect before LLVM certification"
            , "backend must explicitly lower TermSessionOffer before LLVM certification"
            ]
        , loweringAssumptions = []
        , loweringDerivedObligations = []
        , loweringInspectionPlan =
            [ "inspect exact client label/transport select operations"
            , "inspect exact server label/target offer map"
            , "reject legacy payload_choice Bool and receive-label call"
            , "preserve the local should_cancel_upload TermBranch"
            , "re-verify the final accepted/rejected session choice"
            ]
        }
  in provisional { loweringDecisionDigest = deriveLoweringDecisionDigest provisional }

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
