{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.SessionChoice
  ( SessionChoiceWitness (..)
  , SessionChoiceBundle (..)
  , SessionChoiceError (..)
  , phase0FinalResponseChoiceWitness
  , phase0SessionChoiceBundle
  , verifySessionChoiceBundle
  , verifySessionChoiceWitness
  ) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Assurance.Types
import Phil.Systems.IR
import Phil.Systems.RejectedResponse
import Phil.Systems.Verify

data SessionChoiceWitness = SessionChoiceWitness
  { sessionChoiceFunction :: Text
  , sessionChoiceOfferBlock :: BlockId
  , sessionChoiceTransport :: ValueId
  , sessionChoiceAcceptedLabel :: Text
  , sessionChoiceAcceptedPayload :: ValueId
  , sessionChoiceAcceptedTarget :: BlockId
  , sessionChoiceRejectedLabel :: Text
  , sessionChoiceRejectedPayload :: ValueId
  , sessionChoiceRejectedTarget :: BlockId
  , sessionChoiceLegacyDiscriminator :: ValueId
  , sessionChoiceLegacyReceiveCall :: Text
  , sessionChoiceRecordOperation :: Text
  , sessionChoiceRecordDecision :: DecisionId
  , sessionChoiceLoweringDecision :: DecisionId
  }
  deriving (Eq, Show)

data SessionChoiceBundle = SessionChoiceBundle
  { sessionChoiceArtifact :: SystemsArtifact
  , sessionChoiceContext :: SystemsVerificationContext
  , sessionChoicePredecessor :: RejectedResponseBundle
  , sessionChoiceWitness :: SessionChoiceWitness
  }
  deriving (Eq, Show)

data SessionChoiceError
  = SessionChoiceRejectedResponseError RejectedResponseError
  | SessionChoiceSystemsError SystemsVerificationError
  | SessionChoiceFunctionMissing Text
  | SessionChoiceBlockMissing Text BlockId
  | SessionChoiceValueMissing Text ValueId
  | SessionChoiceValueRoleMismatch Text ValueId SystemsValueRole
  | SessionChoiceLegacyDiscriminatorPresent Text ValueId
  | SessionChoiceLegacyReceivePresent Text BlockId Text
  | SessionChoiceOfferMismatch Text BlockId SystemsTerminator
  | SessionChoiceAcceptedOperationMismatch Text BlockId [SystemsOp]
  | SessionChoiceAcceptedOutcomeMismatch Text BlockId SystemsTerminator
  | SessionChoiceRejectedOutcomeMismatch Text BlockId SystemsTerminator
  | SessionChoicePayloadUseEscapes Text ValueId BlockId [BlockId]
  | SessionChoiceDecisionMissing DecisionId
  | SessionChoiceDecisionMismatch DecisionId
  deriving (Eq, Show)

phase0FinalResponseChoiceWitness :: SessionChoiceWitness
phase0FinalResponseChoiceWitness = SessionChoiceWitness
  { sessionChoiceFunction = "UploadClient"
  , sessionChoiceOfferBlock = BlockId "client.payload"
  , sessionChoiceTransport = ValueId "client.transport"
  , sessionChoiceAcceptedLabel = "accepted"
  , sessionChoiceAcceptedPayload = ValueId "client.upload_id"
  , sessionChoiceAcceptedTarget = BlockId "client.accepted"
  , sessionChoiceRejectedLabel = "rejected"
  , sessionChoiceRejectedPayload = ValueId "client.digest_failure"
  , sessionChoiceRejectedTarget = BlockId "client.rejected"
  , sessionChoiceLegacyDiscriminator = ValueId "client.result_branch"
  , sessionChoiceLegacyReceiveCall = "receive accepted/rejected label"
  , sessionChoiceRecordOperation = "record_upload_id"
  , sessionChoiceRecordDecision = DecisionId "lower.runtime.semantic_call"
  , sessionChoiceLoweringDecision = DecisionId "lower.session.final_response_offer"
  }

phase0SessionChoiceBundle :: Either SessionChoiceError SessionChoiceBundle
phase0SessionChoiceBundle = do
  predecessor <- mapLeft SessionChoiceRejectedResponseError phase0RejectedResponseBundle
  let baseArtifact = rejectedResponseArtifact predecessor
      baseContext = rejectedResponseContext predecessor
      witness = phase0FinalResponseChoiceWitness
  program <- materializeFinalResponseChoice witness (systemsArtifactProgram baseArtifact)
  let baseContract = systemsArtifactStageContract baseArtifact
      targetDigest = systemsProgramDigest program
      contract = baseContract
        { stageTargetArtifactDigest = targetDigest
        , stageTraceRelation = stageTraceRelation baseContract <>
            [ "client final external choice preserves label -> branch-local payload -> continuation identity" ]
        }
      sourceDigest = stageSourceArtifactDigest contract
      predecessorDecisions = loweringLedgerDecisions (systemsArtifactLoweringLedger baseArtifact)
      rebound = Map.map (rebindDecisionTarget targetDigest) predecessorDecisions
      choiceDecision = deriveSessionChoiceDecision sourceDigest targetDigest witness
      decisions = Map.insert (sessionChoiceLoweringDecision witness) choiceDecision rebound
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
      bundle = SessionChoiceBundle artifact context predecessor witness
  verifySessionChoiceBundle bundle
  pure bundle

verifySessionChoiceBundle :: SessionChoiceBundle -> Either SessionChoiceError ()
verifySessionChoiceBundle bundle = do
  mapLeft SessionChoiceRejectedResponseError $
    verifyRejectedResponseBundle (sessionChoicePredecessor bundle)
  mapLeft SessionChoiceSystemsError $
    verifySystemsArtifact (sessionChoiceContext bundle) (sessionChoiceArtifact bundle)
  verifySessionChoiceWitness (sessionChoiceArtifact bundle) (sessionChoiceWitness bundle)

verifySessionChoiceWitness
  :: SystemsArtifact
  -> SessionChoiceWitness
  -> Either SessionChoiceError ()
verifySessionChoiceWitness artifact witness = do
  let program = systemsArtifactProgram artifact
      functionName = sessionChoiceFunction witness
  function <- lookupFunction functionName program

  transport <- lookupValue functionName function (sessionChoiceTransport witness)
  case systemsValueRole transport of
    TransportHandle -> pure ()
    other -> Left (SessionChoiceValueRoleMismatch
      functionName (sessionChoiceTransport witness) other)

  acceptedPayload <- lookupValue functionName function (sessionChoiceAcceptedPayload witness)
  case systemsValueRole acceptedPayload of
    RuntimeScalar "UploadId" -> pure ()
    other -> Left (SessionChoiceValueRoleMismatch
      functionName (sessionChoiceAcceptedPayload witness) other)

  rejectedPayload <- lookupValue functionName function (sessionChoiceRejectedPayload witness)
  case systemsValueRole rejectedPayload of
    RuntimeScalar "DigestFailure" -> pure ()
    other -> Left (SessionChoiceValueRoleMismatch
      functionName (sessionChoiceRejectedPayload witness) other)

  case Map.lookup (sessionChoiceLegacyDiscriminator witness) (systemsFunctionValues function) of
    Nothing -> pure ()
    Just _ -> Left (SessionChoiceLegacyDiscriminatorPresent
      functionName (sessionChoiceLegacyDiscriminator witness))

  offerBlock <- lookupBlock functionName function (sessionChoiceOfferBlock witness)
  unless (not (any isLegacyReceive (systemsBlockOps offerBlock))) $
    Left (SessionChoiceLegacyReceivePresent
      functionName
      (sessionChoiceOfferBlock witness)
      (sessionChoiceLegacyReceiveCall witness))

  let expectedArms = Map.fromList
        [ ( sessionChoiceAcceptedLabel witness
          , SystemsChoiceArm
              (Just (sessionChoiceAcceptedPayload witness))
              (sessionChoiceAcceptedTarget witness)
          )
        , ( sessionChoiceRejectedLabel witness
          , SystemsChoiceArm
              (Just (sessionChoiceRejectedPayload witness))
              (sessionChoiceRejectedTarget witness)
          )
        ]
  case systemsBlockTerminator offerBlock of
    TermSessionOffer transportId arms
      | transportId == sessionChoiceTransport witness
          && arms == expectedArms -> pure ()
    other -> Left (SessionChoiceOfferMismatch
      functionName (sessionChoiceOfferBlock witness) other)

  acceptedBlock <- lookupBlock functionName function (sessionChoiceAcceptedTarget witness)
  case systemsBlockOps acceptedBlock of
    [ OpRuntimeCall
        { runtimeCallName = name
        , runtimeCallInputs = inputs
        , runtimeCallOutputs = outputs
        , runtimeCallSite = site
        , runtimeCallDecision = decisionId
        }
      ]
      | name == sessionChoiceRecordOperation witness
          && inputs == [sessionChoiceAcceptedPayload witness]
          && null outputs
          && site == Nothing
          && decisionId == sessionChoiceRecordDecision witness -> pure ()
    operations -> Left (SessionChoiceAcceptedOperationMismatch
      functionName (sessionChoiceAcceptedTarget witness) operations)
  case systemsBlockTerminator acceptedBlock of
    TermEnd "success" -> pure ()
    other -> Left (SessionChoiceAcceptedOutcomeMismatch
      functionName (sessionChoiceAcceptedTarget witness) other)

  rejectedBlock <- lookupBlock functionName function (sessionChoiceRejectedTarget witness)
  case systemsBlockTerminator rejectedBlock of
    TermEnd "failure" -> pure ()
    other -> Left (SessionChoiceRejectedOutcomeMismatch
      functionName (sessionChoiceRejectedTarget witness) other)

  verifyPayloadUses
    functionName
    function
    (sessionChoiceAcceptedPayload witness)
    (sessionChoiceAcceptedTarget witness)
    True
  verifyPayloadUses
    functionName
    function
    (sessionChoiceRejectedPayload witness)
    (sessionChoiceRejectedTarget witness)
    False

  let decisions = loweringLedgerDecisions (systemsArtifactLoweringLedger artifact)
      sourceDigest = stageSourceArtifactDigest (systemsArtifactStageContract artifact)
      targetDigest = systemsProgramDigest program
      expectedDecision = deriveSessionChoiceDecision sourceDigest targetDigest witness
  case Map.lookup (sessionChoiceLoweringDecision witness) decisions of
    Nothing -> Left (SessionChoiceDecisionMissing (sessionChoiceLoweringDecision witness))
    Just actual -> unless (actual == expectedDecision) $
      Left (SessionChoiceDecisionMismatch (sessionChoiceLoweringDecision witness))
  where
    isLegacyReceive operation = case operation of
      OpRuntimeCall { runtimeCallName = name } ->
        name == sessionChoiceLegacyReceiveCall witness
      _ -> False

verifyPayloadUses
  :: Text
  -> SystemsFunction
  -> ValueId
  -> BlockId
  -> Bool
  -> Either SessionChoiceError ()
verifyPayloadUses functionName function payload target requireUse = do
  let blocks = valueUseBlocks function payload
      escaped = filter (/= target) blocks
  unless (null escaped) $
    Left (SessionChoicePayloadUseEscapes functionName payload target escaped)
  if requireUse
    then unless (blocks == [target]) $
      Left (SessionChoicePayloadUseEscapes functionName payload target blocks)
    else pure ()

valueUseBlocks :: SystemsFunction -> ValueId -> [BlockId]
valueUseBlocks function payload =
  [ systemsBlockId blockValue
  | blockValue <- Map.elems (systemsFunctionBlocks function)
  , payload `elem` concatMap operationInputs (systemsBlockOps blockValue)
  ]

operationInputs :: SystemsOp -> [ValueId]
operationInputs operation = case operation of
  OpReceiveFrame pending frame transport _ _ -> [pending, frame, transport]
  OpBorrowView view owner _ -> [view, owner]
  OpCommitIngress pending transport _ -> [pending, transport]
  OpDestroyPending pending owner _ -> [pending, owner]
  OpReleaseOwner owner _ -> [owner]
  OpCleanupPartial owner _ -> [owner]
  OpRuntimeCall _ inputs _ _ _ -> inputs
  OpCopy source target _ -> [source, target]
  OpEraseFact {} -> []
  OpDiagnostic {} -> []
  OpScalarLiteral output _ -> [output]
  OpTraceEvent _ -> []

materializeFinalResponseChoice
  :: SessionChoiceWitness
  -> SystemsProgram
  -> Either SessionChoiceError SystemsProgram
materializeFinalResponseChoice witness program = do
  let functionName = sessionChoiceFunction witness
  function <- lookupFunction functionName program
  offerBlock <- lookupBlock functionName function (sessionChoiceOfferBlock witness)
  acceptedBlock <- lookupBlock functionName function (sessionChoiceAcceptedTarget witness)
  _ <- lookupBlock functionName function (sessionChoiceRejectedTarget witness)

  let acceptedValue = SystemsValue
        (sessionChoiceAcceptedPayload witness)
        (RuntimeScalar "UploadId")
        Nothing
      rejectedValue = SystemsValue
        (sessionChoiceRejectedPayload witness)
        (RuntimeScalar "DigestFailure")
        Nothing
      values = Map.insert
        (sessionChoiceRejectedPayload witness)
        rejectedValue $
        Map.insert
          (sessionChoiceAcceptedPayload witness)
          acceptedValue $
          Map.delete
            (sessionChoiceLegacyDiscriminator witness)
            (systemsFunctionValues function)
      offerOps = filter (not . isLegacyReceive) (systemsBlockOps offerBlock)
      arms = Map.fromList
        [ ( sessionChoiceAcceptedLabel witness
          , SystemsChoiceArm
              (Just (sessionChoiceAcceptedPayload witness))
              (sessionChoiceAcceptedTarget witness)
          )
        , ( sessionChoiceRejectedLabel witness
          , SystemsChoiceArm
              (Just (sessionChoiceRejectedPayload witness))
              (sessionChoiceRejectedTarget witness)
          )
        ]
      offerBlock' = offerBlock
        { systemsBlockOps = offerOps
        , systemsBlockTerminator = TermSessionOffer (sessionChoiceTransport witness) arms
        }
      recordOperation = OpRuntimeCall
        { runtimeCallName = sessionChoiceRecordOperation witness
        , runtimeCallInputs = [sessionChoiceAcceptedPayload witness]
        , runtimeCallOutputs = []
        , runtimeCallSite = Nothing
        , runtimeCallDecision = sessionChoiceRecordDecision witness
        }
      acceptedBlock' = acceptedBlock
        { systemsBlockOps = systemsBlockOps acceptedBlock <> [recordOperation] }
      blocks = Map.insert
        (sessionChoiceAcceptedTarget witness)
        acceptedBlock' $
        Map.insert
          (sessionChoiceOfferBlock witness)
          offerBlock'
          (systemsFunctionBlocks function)
      function' = function
        { systemsFunctionValues = values
        , systemsFunctionBlocks = blocks
        }
  pure program
    { systemsProgramFunctions = Map.insert
        functionName
        function'
        (systemsProgramFunctions program)
    }
  where
    isLegacyReceive operation = case operation of
      OpRuntimeCall { runtimeCallName = name } ->
        name == sessionChoiceLegacyReceiveCall witness
      _ -> False

lookupFunction :: Text -> SystemsProgram -> Either SessionChoiceError SystemsFunction
lookupFunction functionName program =
  case Map.lookup functionName (systemsProgramFunctions program) of
    Nothing -> Left (SessionChoiceFunctionMissing functionName)
    Just value -> Right value

lookupValue :: Text -> SystemsFunction -> ValueId -> Either SessionChoiceError SystemsValue
lookupValue functionName function valueId =
  case Map.lookup valueId (systemsFunctionValues function) of
    Nothing -> Left (SessionChoiceValueMissing functionName valueId)
    Just value -> Right value

lookupBlock :: Text -> SystemsFunction -> BlockId -> Either SessionChoiceError SystemsBlock
lookupBlock functionName function blockId =
  case Map.lookup blockId (systemsFunctionBlocks function) of
    Nothing -> Left (SessionChoiceBlockMissing functionName blockId)
    Just value -> Right value

rebindDecisionTarget :: Digest -> LoweringDecision -> LoweringDecision
rebindDecisionTarget targetDigest lowering =
  let rebound = lowering { loweringTargetArtifactDigest = targetDigest }
  in rebound { loweringDecisionDigest = deriveLoweringDecisionDigest rebound }

deriveSessionChoiceDecision
  :: Digest
  -> Digest
  -> SessionChoiceWitness
  -> LoweringDecision
deriveSessionChoiceDecision sourceDigest targetDigest witness =
  let provisional = LoweringDecision
        { loweringDecisionId = sessionChoiceLoweringDecision witness
        , loweringDecisionDigest = Digest ""
        , loweringSourceArtifactDigest = sourceDigest
        , loweringTargetArtifactDigest = targetDigest
        , loweringSourceRepresentation =
            "client final Offer accepted(id)/rejected(reason) session semantics"
        , loweringTargetRepresentation =
            "TermSessionOffer label -> branch-local payload binding -> target"
        , loweringSemanticEntities =
            [ "client final external choice"
            , "accepted(id : UploadId)"
            , "rejected(reason : DigestFailure)"
            ]
        , loweringObligationRevisions = []
        , loweringAssuranceEntries = []
        , loweringAssuranceUses = []
        , loweringAction = Materialize
        , loweringRepresentationBefore =
            "anonymous runtime Bool discriminator plus payload-erasing TermBranch"
        , loweringRepresentationAfter =
            "semantic labels with edge-defined payload identities and continuations"
        , loweringInvariantsPreserved =
            [ "choice labels remain protocol identities"
            , "accepted UploadId reaches only accepted continuation"
            , "rejected DigestFailure belongs only to rejected continuation"
            , "no target discriminator or payload layout is chosen in Systems"
            ]
        , loweringInvariantsTransferred = []
        , loweringRuntimeResidue =
            [ "peer-selected branch remains runtime work"
            , "physical response decoding is deferred to a target profile"
            ]
        , loweringCostClass = Just SemanticRequired
        , loweringCostShape = emptyCostShape
            { costBranchOrDispatch = Just "one peer-selected session branch"
            , costFrequency = Just "per final upload response"
            }
        , loweringTargetPreconditions =
            [ "backend must explicitly lower TermSessionOffer before LLVM certification" ]
        , loweringAssumptions = []
        , loweringDerivedObligations = []
        , loweringInspectionPlan =
            [ "inspect exact label/payload/target map"
            , "reject legacy anonymous result discriminator"
            , "reject payload use outside its branch-local target"
            ]
        }
  in provisional { loweringDecisionDigest = deriveLoweringDecisionDigest provisional }

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
