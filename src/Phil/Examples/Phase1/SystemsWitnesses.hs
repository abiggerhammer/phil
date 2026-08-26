{-# LANGUAGE OverloadedStrings #-}

module Phil.Examples.Phase1.SystemsWitnesses
  ( uploadPhase1StageBundle
  , stevePhase1StageBundle
  , steveHostAbiDecisionId
  , steveHostAbiTargetPrecondition
  , steveHostAbiObligationRevision
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import Phil.Assurance.Types (RevisionId (..), digestText)
import Phil.Core.ProviderQualificationIdentity
  ( CheckedProviderQualificationAdmissionIdentity (..)
  , ProviderQualificationEvidenceIdentityInput (..)
  , QualificationAdmissionRevision (..)
  )
import Phil.Core.Static (InstanceRevision (..), RealizationRevision (..))
import Phil.Examples.Steve.ProviderQualifications
import Phil.Systems.IR
import Phil.Systems.Phase0 (phase0SystemsArtifact)
import Phil.Systems.Phase1Stage

uploadPhase1StageBundle :: Phase1StageBundle
uploadPhase1StageBundle = accountArtifact
  (InstanceRevision "phase1.upload.instance.v1")
  (RealizationRevision "phase1.upload.realization.host.v1")
  "phase1-stage-verifier.v1"
  phase0SystemsArtifact
  (Set.singleton "realization:upload.host.v1")
  Set.empty
  Set.empty

stevePhase1StageBundle :: Either String Phase1StageBundle
stevePhase1StageBundle = do
  qualifications <- mapLeft (show . unSteveProviderQualificationError)
    materializeSteveProviderQualifications
  let digestArtifact = steveDigestProviderQualification qualifications
      blobArtifact = steveBlobProviderQualification qualifications
      qualificationRefs = Set.fromList
        [ admissionText (steveProviderCheckedAdmission digestArtifact)
        , admissionText (steveProviderCheckedAdmission blobArtifact)
        ]
      assumptions = Set.unions
        [ qualificationEvidenceAssumptions digestArtifact
        , qualificationEvidenceAssumptions blobArtifact
        ]
  pure (accountArtifact
    (InstanceRevision "phase1.steve.instance.v1")
    (RealizationRevision "phase1.steve.realization.host.v1")
    "phase1-stage-verifier.v1"
    steveSystemsArtifact
    (Set.singleton "realization:steve.host.v1")
    qualificationRefs
    assumptions)

-- | One witness-neutral accounting constructor.  It has no upload/Steve branch:
-- the caller supplies an artifact and the exact realization/qualification facts
-- that justify its target graph.
accountArtifact
  :: InstanceRevision
  -> RealizationRevision
  -> Text
  -> SystemsArtifact
  -> Set Text
  -> Set Text
  -> Set Text
  -> Phase1StageBundle
accountArtifact instanceRevision realizationRevision verifierProfile artifact realizationRefs qualificationRefs assumptions =
  makePhase1StageBundle
    instanceRevision
    realizationRevision
    verifierProfile
    artifact
    dispositions
    justifications
  where
    facts = collectSourceFacts artifact
    mechanisms = collectSystemsMechanisms artifact

    -- SYS-001 establishes accounting completeness, not yet the finer SYS-002+
    -- relation taxonomy. Each source responsibility is therefore related to the
    -- exact witness Systems graph as a bounded realized relation.
    disposition = case Set.null assumptions of
      True -> Phase1FactRealized mechanisms
      False -> Phase1FactAssumptionDependent assumptions (Phase1FactRealized mechanisms)
    dispositions = Map.fromSet (const disposition) facts

    justification = SystemsJustification
      { systemsJustificationSourceFacts = facts
      , systemsJustificationRealizationRefs = realizationRefs
      , systemsJustificationQualificationRefs = qualificationRefs
      , systemsJustificationAssumptionRefs = assumptions
      }
    justifications = Map.fromSet (const justification) mechanisms

qualificationEvidenceAssumptions
  :: SteveProviderQualificationArtifact
  -> Set Text
qualificationEvidenceAssumptions artifact =
  qualificationEvidenceAssumptionRefs (steveProviderIdentityEvidence artifact)

admissionText :: CheckedProviderQualificationAdmissionIdentity -> Text
admissionText checked = case checkedQualificationAdmissionRevision checked of
  QualificationAdmissionRevision value -> value

steveHostAbiDecisionId :: DecisionId
steveHostAbiDecisionId = DecisionId "lower.steve.host-abi"

steveHostAbiTargetPrecondition :: Text
steveHostAbiTargetPrecondition =
  "host BlobProvider byte-slice ABI preserves pointer/length pairing and length range"

steveHostAbiObligationRevision :: RevisionId
steveHostAbiObligationRevision =
  RevisionId "obligation.phase1.steve.host-abi.v1"

steveSystemsArtifact :: SystemsArtifact
steveSystemsArtifact = SystemsArtifact
  { systemsArtifactProgram = steveProgram
  , systemsArtifactStageContract = steveStageContract
  , systemsArtifactLoweringLedger = steveLoweringLedger
  }

steveProgram :: SystemsProgram
steveProgram = SystemsProgram
  { systemsProgramName = "steve"
  , systemsProgramProfile = CheckedRuntime
  , systemsProgramFunctions = Map.fromList
      [ (systemsFunctionName stevePutFunction, stevePutFunction)
      , (systemsFunctionName steveGetFunction, steveGetFunction)
      ]
  }

stevePutFunction :: SystemsFunction
stevePutFunction = SystemsFunction
  { systemsFunctionName = "StevePut"
  , systemsFunctionEntry = blockId "put.entry"
  , systemsFunctionValues = valueMap
      [ ownerValue "put.candidate" "steve.candidate"
      , viewValue "put.digest-view" "put.candidate"
      , viewValue "put.install-view" "put.candidate"
      , scalarValue "put.id" "ContentId[SHA256]"
      ]
  , systemsFunctionBlocks = blockMap
      [ block "put.entry" []
          (runtimeChoice "DigestProvider.compute" ["put.digest-view"]
            [ ("computed", "put.install") ])
      , block "put.install" []
          (runtimeChoice "BlobProvider.install-if-absent"
            ["put.id", "put.install-view"]
            [ ("installed", "put.ok")
            , ("already-exists", "put.ok")
            , ("storage-failure", "put.failure")
            ])
      , block "put.ok" [OpTraceEvent "steve.put.commit"] (TermEnd "success")
      , block "put.failure" [] (TermEnd "storage-failure")
      ]
  }

steveGetFunction :: SystemsFunction
steveGetFunction = SystemsFunction
  { systemsFunctionName = "SteveGet"
  , systemsFunctionEntry = blockId "get.entry"
  , systemsFunctionValues = valueMap
      [ scalarValue "get.id" "ContentId[SHA256]"
      , ownerValue "get.bytes" "steve.read-result"
      , viewValue "get.bytes-view" "get.bytes"
      ]
  , systemsFunctionBlocks = blockMap
      [ block "get.entry" []
          (runtimeChoice "BlobProvider.read" ["get.id"]
            [ ("found", "get.check")
            , ("not-found", "get.not-found")
            , ("storage-failure", "get.failure")
            ])
      , block "get.check" []
          (runtimeChoice "DigestProvider.check" ["get.id", "get.bytes-view"]
            [ ("accepted", "get.ok")
            , ("rejected", "get.integrity-failure")
            ])
      , block "get.ok" [OpTraceEvent "steve.get.commit"] (TermEnd "success")
      , block "get.not-found" [] (TermEnd "not-found")
      , block "get.integrity-failure" [] (TermEnd "integrity-failure")
      , block "get.failure" [] (TermEnd "storage-failure")
      ]
  }

steveSourceArtifactDigest =
  digestText "Steve Phase 1 architecture/provider semantic source"

steveTargetArtifactDigest = systemsProgramDigest steveProgram

steveStageContract :: StageContract
steveStageContract = StageContract
  { stageContractId = "phase1.steve.provider-to-systems.v1"
  , stageSourceArtifactDigest = steveSourceArtifactDigest
  , stageTargetArtifactDigest = steveTargetArtifactDigest
  , stageFacts = map sourceFact
      [ "steve.digest.stable-subject"
      , "steve.digest.sha256-profile"
      , "steve.blob.borrow-preservation"
      , "steve.blob.no-replace"
      , "steve.blob.atomic-visibility"
      , "steve.blob.authority-confinement"
      , "steve.provider.admission-lineage"
      ]
  , stageInvariants = Map.empty
  , stageRequiredEdges = []
  , stageDerivedObligations = [steveHostAbiObligationRevision]
  , stageAssumptions =
      [ "sha256.semantic-profile.v1"
      , "blob.no-out-of-band-mutation.v1"
      , "blob.atomic-publication.v1"
      , "blob.internal-authority-confinement.v1"
      ]
  , stageTraceRelation =
      [ "StevePut commit follows digest compute and BlobProvider install outcome"
      , "SteveGet success follows BlobProvider read and DigestProvider check"
      ]
  , stageResourceFailureRelation =
      [ "DigestProvider and BlobProvider observe candidate bytes through shared borrows"
      , "typed storage/integrity outcomes remain distinct"
      ]
  }

sourceFact :: Text -> FactTransfer
sourceFact key = FactTransfer
  { factTransferId = key
  , factSourceRevision = Nothing
  , factDisposition = FactConsumed "indexed by Phase1Stage bidirectional accounting"
  }

steveLoweringLedger :: LoweringLedger
steveLoweringLedger = LoweringLedger
  { loweringLedgerDecisions = decisions
  , loweringLedgerRoot = deriveLoweringLedgerRoot decisions
  }
  where
    decisions = Map.singleton steveHostAbiDecisionId steveHostAbiDecision

steveHostAbiDecision :: LoweringDecision
steveHostAbiDecision = provisional
  { loweringDecisionDigest = deriveLoweringDecisionDigest provisional }
  where
    provisional = LoweringDecision
      { loweringDecisionId = steveHostAbiDecisionId
      , loweringDecisionDigest = digestText "pending"
      , loweringSourceArtifactDigest = steveSourceArtifactDigest
      , loweringTargetArtifactDigest = steveTargetArtifactDigest
      , loweringSourceRepresentation = "Steve BlobProvider semantic byte slice"
      , loweringTargetRepresentation = "host pointer/length byte-slice ABI"
      , loweringSemanticEntities = ["steve.blob.byte-slice"]
      , loweringObligationRevisions = []
      , loweringAssuranceEntries = []
      , loweringAssuranceUses = []
      , loweringAction = ChooseLayout
      , loweringRepresentationBefore = "OwnedBytes / shared semantic byte view"
      , loweringRepresentationAfter = "host pointer + length pair"
      , loweringInvariantsPreserved = []
      , loweringInvariantsTransferred = []
      , loweringRuntimeResidue = []
      , loweringCostClass = Just TargetRequired
      , loweringCostShape = emptyCostShape
      , loweringTargetPreconditions = [steveHostAbiTargetPrecondition]
      , loweringAssumptions = []
      , loweringDerivedObligations = [steveHostAbiObligationRevision]
      , loweringInspectionPlan =
          [ "verify selected host ABI preserves pointer/length pairing"
          , "verify host length representation covers the semantic byte length range"
          ]
      }

runtimeChoice :: Text -> [Text] -> [(Text, Text)] -> SystemsTerminator
runtimeChoice name inputs arms = TermRuntimeChoice
  { runtimeChoiceName = name
  , runtimeChoiceInputs = map valueId inputs
  , runtimeChoiceSite = Nothing
  , runtimeChoiceArms = Map.fromList
      [ (label, SystemsRuntimeChoiceArm Nothing (blockId target))
      | (label, target) <- arms
      ]
  }

block :: Text -> [SystemsOp] -> SystemsTerminator -> SystemsBlock
block key operations terminator = SystemsBlock
  { systemsBlockId = blockId key
  , systemsBlockOps = operations
  , systemsBlockTerminator = terminator
  }

blockMap :: [SystemsBlock] -> Map BlockId SystemsBlock
blockMap blocks = Map.fromList [(systemsBlockId value, value) | value <- blocks]

valueMap :: [SystemsValue] -> Map ValueId SystemsValue
valueMap values = Map.fromList [(systemsValueId value, value) | value <- values]

ownerValue :: Text -> Text -> SystemsValue
ownerValue key storage = SystemsValue
  { systemsValueId = valueId key
  , systemsValueRole = OwnedBuffer "OwnedBytes"
  , systemsStorageIdentity = Just storage
  }

viewValue :: Text -> Text -> SystemsValue
viewValue key owner = SystemsValue
  { systemsValueId = valueId key
  , systemsValueRole = BorrowedSlice (valueId owner)
  , systemsStorageIdentity = Nothing
  }

scalarValue :: Text -> Text -> SystemsValue
scalarValue key role = SystemsValue
  { systemsValueId = valueId key
  , systemsValueRole = RuntimeInput role
  , systemsStorageIdentity = Nothing
  }

valueId :: Text -> ValueId
valueId = ValueId

blockId :: Text -> BlockId
blockId = BlockId

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
