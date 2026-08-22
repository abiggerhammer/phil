{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.LocalRuntimeChoice
  ( LocalRuntimeChoiceWitness (..)
  , LocalRuntimeChoiceBundle (..)
  , LocalRuntimeChoiceError (..)
  , phase0LocalRuntimeChoiceWitness
  , phase0LocalRuntimeChoiceBundle
  , verifyLocalRuntimeChoiceBundle
  , verifyLocalRuntimeChoiceWitness
  ) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Assurance.Types
import Phil.Systems.Dataflow
import Phil.Systems.IR
import Phil.Systems.PayloadCancelChoice
import Phil.Systems.Verify

data LocalRuntimeChoiceWitness = LocalRuntimeChoiceWitness
  { localChoiceFunction :: Text
  , localChoiceBlock :: BlockId
  , localChoiceName :: Text
  , localChoiceSomeTarget :: BlockId
  , localChoiceNoneTarget :: BlockId
  , localChoiceSelectedVersion :: ValueId
  , localChoiceLegacyDiscriminator :: ValueId
  , localChoiceVersionSelectBlock :: BlockId
  , localChoiceServerTransport :: ValueId
  , localChoiceLoweringDecision :: DecisionId
  }
  deriving (Eq, Show)

data LocalRuntimeChoiceBundle = LocalRuntimeChoiceBundle
  { localRuntimeChoiceArtifact :: SystemsArtifact
  , localRuntimeChoiceContext :: SystemsVerificationContext
  , localRuntimeChoicePredecessor :: PayloadCancelChoiceBundle
  , localRuntimeChoiceWitness :: LocalRuntimeChoiceWitness
  }
  deriving (Eq, Show)

data LocalRuntimeChoiceError
  = LocalRuntimeChoicePredecessorError PayloadCancelChoiceError
  | LocalRuntimeChoiceSystemsError SystemsVerificationError
  | LocalRuntimeChoiceDataflowError ScalarDataflowError
  | LocalRuntimeChoiceMismatch Text
  deriving (Eq, Show)

phase0LocalRuntimeChoiceWitness :: LocalRuntimeChoiceWitness
phase0LocalRuntimeChoiceWitness = LocalRuntimeChoiceWitness
  { localChoiceFunction = "UploadServer"
  , localChoiceBlock = BlockId "server.version.choose"
  , localChoiceName = "choose_supported"
  , localChoiceSomeTarget = BlockId "server.version"
  , localChoiceNoneTarget = BlockId "server.unsupported"
  , localChoiceSelectedVersion = ValueId "server.selected_version"
  , localChoiceLegacyDiscriminator = ValueId "server.has_version"
  , localChoiceVersionSelectBlock = BlockId "server.version"
  , localChoiceServerTransport = ValueId "server.transport"
  , localChoiceLoweringDecision = DecisionId "lower.local.choose_supported"
  }

phase0LocalRuntimeChoiceBundle :: Either LocalRuntimeChoiceError LocalRuntimeChoiceBundle
phase0LocalRuntimeChoiceBundle = do
  predecessor <- mapLeft LocalRuntimeChoicePredecessorError phase0PayloadCancelChoiceBundle
  let baseArtifact = payloadCancelChoiceArtifact predecessor
      baseContext = payloadCancelChoiceContext predecessor
      witness = phase0LocalRuntimeChoiceWitness
  program <- materialize witness (systemsArtifactProgram baseArtifact)
  let baseContract = systemsArtifactStageContract baseArtifact
      targetDigest = systemsProgramDigest program
      contract = baseContract
        { stageTargetArtifactDigest = targetDigest
        , stageTraceRelation = stageTraceRelation baseContract <>
            [ "choose_supported preserves none/some identity and branch-local selected UInt16"
            , "selected version reaches select version while proof witnesses remain compile-time assurance"
            ]
        }
      sourceDigest = stageSourceArtifactDigest contract
      rebound = Map.map (rebind targetDigest)
        (loweringLedgerDecisions (systemsArtifactLoweringLedger baseArtifact))
      decisions = Map.insert (localChoiceLoweringDecision witness)
        (deriveDecision sourceDigest targetDigest witness) rebound
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
      bundle = LocalRuntimeChoiceBundle artifact context predecessor witness
  verifyLocalRuntimeChoiceBundle bundle
  pure bundle

verifyLocalRuntimeChoiceBundle :: LocalRuntimeChoiceBundle -> Either LocalRuntimeChoiceError ()
verifyLocalRuntimeChoiceBundle bundle = do
  mapLeft LocalRuntimeChoicePredecessorError $
    verifyPayloadCancelChoiceBundle (localRuntimeChoicePredecessor bundle)
  mapLeft LocalRuntimeChoiceSystemsError $
    verifySystemsArtifact (localRuntimeChoiceContext bundle) (localRuntimeChoiceArtifact bundle)
  mapLeft LocalRuntimeChoiceDataflowError $
    verifyScalarDataflow (localRuntimeChoiceArtifact bundle)
  verifyLocalRuntimeChoiceWitness (localRuntimeChoiceArtifact bundle) (localRuntimeChoiceWitness bundle)

verifyLocalRuntimeChoiceWitness :: SystemsArtifact -> LocalRuntimeChoiceWitness -> Either LocalRuntimeChoiceError ()
verifyLocalRuntimeChoiceWitness artifact witness = do
  function <- needFunction witness (systemsArtifactProgram artifact)
  case Map.lookup (localChoiceSelectedVersion witness) (systemsFunctionValues function) of
    Just SystemsValue { systemsValueRole = TypedScalar (ScalarUInt 16) } -> pure ()
    _ -> Left (LocalRuntimeChoiceMismatch "selected version is not UInt16")
  unless (Map.notMember (localChoiceLegacyDiscriminator witness) (systemsFunctionValues function)) $
    Left (LocalRuntimeChoiceMismatch "legacy has_version Bool remains")
  choiceBlock <- needBlock witness function (localChoiceBlock witness)
  unless (not (any isLegacyChoose (systemsBlockOps choiceBlock))) $
    Left (LocalRuntimeChoiceMismatch "legacy choose_supported runtime call remains")
  let expectedArms = Map.fromList
        [ ("none", SystemsRuntimeChoiceArm Nothing (localChoiceNoneTarget witness))
        , ("some", SystemsRuntimeChoiceArm (Just (localChoiceSelectedVersion witness)) (localChoiceSomeTarget witness))
        ]
  unless (systemsBlockTerminator choiceBlock == TermRuntimeChoice (localChoiceName witness) [] Nothing expectedArms) $
    Left (LocalRuntimeChoiceMismatch "local runtime choice shape drifted")
  versionBlock <- needBlock witness function (localChoiceVersionSelectBlock witness)
  unless (any exactVersionSelect (systemsBlockOps versionBlock)) $
    Left (LocalRuntimeChoiceMismatch "select version does not consume selected_version")
  noneBlock <- needBlock witness function (localChoiceNoneTarget witness)
  unless (not (blockUses (localChoiceSelectedVersion witness) noneBlock)) $
    Left (LocalRuntimeChoiceMismatch "none arm observes some-arm payload")
  mapLeft LocalRuntimeChoicePredecessorError $
    verifyPayloadCancelChoiceWitness artifact phase0PayloadCancelChoiceWitness
  let decisions = loweringLedgerDecisions (systemsArtifactLoweringLedger artifact)
      sourceDigest = stageSourceArtifactDigest (systemsArtifactStageContract artifact)
      targetDigest = systemsProgramDigest (systemsArtifactProgram artifact)
  unless (Map.lookup (localChoiceLoweringDecision witness) decisions == Just (deriveDecision sourceDigest targetDigest witness)) $
    Left (LocalRuntimeChoiceMismatch "local runtime choice lowering decision drifted")
  where
    isLegacyChoose OpRuntimeCall { runtimeCallName = name } = name == localChoiceName witness
    isLegacyChoose _ = False
    exactVersionSelect OpRuntimeCall
      { runtimeCallName = "select version"
      , runtimeCallInputs = inputs
      , runtimeCallOutputs = []
      , runtimeCallSite = Nothing
      } = inputs == [localChoiceServerTransport witness, localChoiceSelectedVersion witness]
    exactVersionSelect _ = False

materialize :: LocalRuntimeChoiceWitness -> SystemsProgram -> Either LocalRuntimeChoiceError SystemsProgram
materialize witness program = do
  function <- needFunction witness program
  choiceBlock <- needBlock witness function (localChoiceBlock witness)
  versionBlock <- needBlock witness function (localChoiceVersionSelectBlock witness)
  let values = Map.insert (localChoiceSelectedVersion witness)
        (SystemsValue (localChoiceSelectedVersion witness) (TypedScalar (ScalarUInt 16)) Nothing) $
        Map.delete (localChoiceLegacyDiscriminator witness) (systemsFunctionValues function)
      choiceBlock' = choiceBlock
        { systemsBlockOps = filter (not . isLegacyChoose) (systemsBlockOps choiceBlock)
        , systemsBlockTerminator = TermRuntimeChoice (localChoiceName witness) [] Nothing $
            Map.fromList
              [ ("none", SystemsRuntimeChoiceArm Nothing (localChoiceNoneTarget witness))
              , ("some", SystemsRuntimeChoiceArm (Just (localChoiceSelectedVersion witness)) (localChoiceSomeTarget witness))
              ]
        }
      versionBlock' = versionBlock
        { systemsBlockOps = map addSelectedVersion (systemsBlockOps versionBlock) }
      function' = function
        { systemsFunctionValues = values
        , systemsFunctionBlocks = Map.insert (localChoiceVersionSelectBlock witness) versionBlock' $
            Map.insert (localChoiceBlock witness) choiceBlock' (systemsFunctionBlocks function)
        }
  pure program
    { systemsProgramFunctions = Map.insert (localChoiceFunction witness) function' (systemsProgramFunctions program) }
  where
    isLegacyChoose OpRuntimeCall
      { runtimeCallName = name
      , runtimeCallInputs = []
      , runtimeCallOutputs = outputs
      , runtimeCallSite = Nothing
      } = name == localChoiceName witness && outputs == [localChoiceLegacyDiscriminator witness]
    isLegacyChoose _ = False
    addSelectedVersion operation@OpRuntimeCall
      { runtimeCallName = "select version"
      , runtimeCallInputs = inputs
      , runtimeCallOutputs = []
      , runtimeCallSite = Nothing
      }
      | inputs == [localChoiceServerTransport witness] =
          operation { runtimeCallInputs = [localChoiceServerTransport witness, localChoiceSelectedVersion witness] }
    addSelectedVersion other = other

blockUses :: ValueId -> SystemsBlock -> Bool
blockUses value blockValue = any opUses (systemsBlockOps blockValue) || termUses (systemsBlockTerminator blockValue)
  where
    opUses OpRuntimeCall { runtimeCallInputs = inputs } = value `elem` inputs
    opUses OpSessionSelect { sessionSelectPayload = payload } = payload == Just value
    opUses OpCopy { copySource = source } = source == value
    opUses _ = False
    termUses TermBranch condition _ _ = condition == value
    termUses TermRuntimeCheck { checkInputs = inputs } = value `elem` inputs
    termUses TermReceiveExact { exactLength = lengthValue } = lengthValue == value
    termUses TermRuntimeChoice { runtimeChoiceInputs = inputs } = value `elem` inputs
    termUses TermReturnScalar returned = returned == value
    termUses _ = False

needFunction :: LocalRuntimeChoiceWitness -> SystemsProgram -> Either LocalRuntimeChoiceError SystemsFunction
needFunction witness program = maybe
  (Left (LocalRuntimeChoiceMismatch "UploadServer missing"))
  Right
  (Map.lookup (localChoiceFunction witness) (systemsProgramFunctions program))

needBlock :: LocalRuntimeChoiceWitness -> SystemsFunction -> BlockId -> Either LocalRuntimeChoiceError SystemsBlock
needBlock _ function blockId = maybe
  (Left (LocalRuntimeChoiceMismatch "required block missing"))
  Right
  (Map.lookup blockId (systemsFunctionBlocks function))

rebind :: Digest -> LoweringDecision -> LoweringDecision
rebind targetDigest lowering =
  let value = lowering { loweringTargetArtifactDigest = targetDigest }
  in value { loweringDecisionDigest = deriveLoweringDecisionDigest value }

deriveDecision :: Digest -> Digest -> LocalRuntimeChoiceWitness -> LoweringDecision
deriveDecision sourceDigest targetDigest witness =
  let value = LoweringDecision
        { loweringDecisionId = localChoiceLoweringDecision witness
        , loweringDecisionDigest = Digest ""
        , loweringSourceArtifactDigest = sourceDigest
        , loweringTargetArtifactDigest = targetDigest
        , loweringSourceRepresentation = "choose_supported -> has_version Bool -> TermBranch"
        , loweringTargetRepresentation = "TermRuntimeChoice none/some with branch-local UInt16 selected version"
        , loweringSemanticEntities = ["choose_supported", "none(noCommon)", "some(version,offered,supported)", "server.selected_version"]
        , loweringObligationRevisions = []
        , loweringAssuranceEntries = []
        , loweringAssuranceUses = []
        , loweringAction = Materialize
        , loweringRepresentationBefore = "anonymous Bool; selected version discarded"
        , loweringRepresentationAfter = "local sum constructor plus branch-local selected version; proof witnesses remain compile-time assurance"
        , loweringInvariantsPreserved = ["none -> server.unsupported", "some -> server.version", "selected version only on some continuation"]
        , loweringInvariantsTransferred = []
        , loweringRuntimeResidue = ["choose_supported"]
        , loweringCostClass = Just SemanticRequired
        , loweringCostShape = emptyCostShape { costBranchOrDispatch = Just "one local none/some dispatch", costFrequency = Just "once per Hello negotiation" }
        , loweringTargetPreconditions = ["some target dedicated to branch-local payload"]
        , loweringAssumptions = []
        , loweringDerivedObligations = []
        , loweringInspectionPlan = ["check none/some labels", "check UInt16 binding", "check select version consumes binding"]
        }
  in value { loweringDecisionDigest = deriveLoweringDecisionDigest value }

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
