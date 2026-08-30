{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.Static (RealizationRevision (..))
import Phil.Systems.IR (CostClass (..), CostShape (..), emptyCostShape)
import Phil.Systems.StorageRealization
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "MEM-001 allocation strategy is nonsemantic for ordinary values"
        ordinaryStrategyIsNonsemantic
    , test "MEM-001 allocation strategy is nonsemantic for explicit storage resources"
        semanticStorageStrategyIsNonsemantic
    , test "MEM-001 physical storage coincidence cannot establish semantic identity"
        physicalCoincidenceRejected
    , test "MEM-001 one physical object cannot collapse distinct semantic subjects"
        distinctSubjectsStayDistinct
    , test "MEM-002 unaccounted allocation failure widens semantics and rejects"
        unaccountedFailureRejected
    , test "MEM-003 exact source-modeled allocation failure accepts"
        sourceFailureMappingAccepted
    , test "MEM-003 undeclared source failure mapping rejects"
        undeclaredSourceFailureRejected
    , test "MEM-003 checked capacity evidence may make allocation failure unreachable"
        capacityGuaranteeAccepted
    , test "MEM-003 exact allocation assumption remains explicit"
        allocationAssumptionAccepted
    , test "MEM-003 deployment capacity requirement remains explicit"
        deploymentRequirementAccepted
    , test "MEM-004 live semantic storage owner blocks terminal closure"
        liveSemanticOwnerRejects
    , test "MEM-004 released semantic storage owner permits terminal closure"
        releasedSemanticOwnerAccepts
    , test "MEM-004 only exact permitted terminal storage disposition accepts"
        terminalDispositionIsExact
    , test "MEM-005 physical leak does not rewrite semantic terminal closure"
        physicalLeakIsSeparateFromSemanticClosure
    , test "MEM-005 exact profile retention may realize physical reclamation"
        profileRetentionAccepted
    , test "MEM-005 wrong retention profile rejects realization"
        wrongRetentionProfileRejected
    , test "MEM-006 alternate storage strategies preserve semantics with distinct costs"
        alternateStorageCostsAreAttributable
    , test "MEM-006 missing storage cost attribution rejects"
        missingStorageCostRejected
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

ordinaryStrategyIsNonsemantic :: Either String ()
ordinaryStrategyIsNonsemantic = do
  inline <- checked ordinaryInlineRelation
  heap <- checked ordinaryHeapRelation
  mapLeft show $ checkEquivalentStorageRealizations inline heap
  assert
    (checkedStoragePhysicalStrategy inline /= checkedStoragePhysicalStrategy heap)
    "fixture storage strategies unexpectedly coincide"

semanticStorageStrategyIsNonsemantic :: Either String ()
semanticStorageStrategyIsNonsemantic = do
  arena <- checked semanticArenaRelation
  device <- checked semanticDeviceRelation
  mapLeft show $ checkEquivalentStorageRealizations arena device
  assert
    (checkedStoragePhysicalObjects arena /= checkedStoragePhysicalObjects device)
    "fixture physical storage domains unexpectedly coincide"

physicalCoincidenceRejected :: Either String ()
physicalCoincidenceRejected =
  case checkStorageRealization ordinaryHeapRelation
      { storageRelationSubject = PhysicalStorageCoincidence heapObject } of
    Left (StoragePhysicalCoincidenceIsNotSemanticIdentity actual) ->
      assert (actual == heapObject) "wrong physical-coincidence object"
    other -> Left ("physical storage coincidence established semantic identity: " <> show other)

distinctSubjectsStayDistinct :: Either String ()
distinctSubjectsStayDistinct = do
  first <- checked ordinaryHeapRelation
  second <- checked ordinaryHeapRelation
    { storageRelationSubject = ExactStorageSemanticSubject otherOrdinarySubject }
  case checkEquivalentStorageRealizations first second of
    Left (StorageSemanticIdentityMismatch expected actual) -> do
      assert
        (storageIdentitySubject expected == ordinarySubject)
        "wrong first semantic subject"
      assert
        (storageIdentitySubject actual == otherOrdinarySubject)
        "wrong second semantic subject"
      assert
        (checkedStoragePhysicalObjects first == checkedStoragePhysicalObjects second)
        "fixture physical object changed while testing subject distinction"
    other -> Left ("distinct semantic subjects collapsed through one physical object: " <> show other)

unaccountedFailureRejected :: Either String ()
unaccountedFailureRejected =
  case checkStorageRealization ordinaryInlineRelation
      { storageRelationAllocationFailure =
          PhysicalAllocationMayFail StorageFailureUnaccounted } of
    Left StorageUnaccountedAllocationFailure -> Right ()
    other -> Left ("unaccounted allocation failure was accepted: " <> show other)

sourceFailureMappingAccepted :: Either String ()
sourceFailureMappingAccepted = do
  _ <- checked ordinaryHeapRelation
    { storageRelationSourceFailureSurface =
        SourceStorageFailures (Set.singleton allocationFailure)
    , storageRelationAllocationFailure =
        PhysicalAllocationMayFail (StorageFailureMapsToSource allocationFailure)
    }
  Right ()

undeclaredSourceFailureRejected :: Either String ()
undeclaredSourceFailureRejected =
  let declared = StorageFailureKey "storage.quota-exhausted"
      relation = ordinaryHeapRelation
        { storageRelationSourceFailureSurface = SourceStorageFailures (Set.singleton declared)
        , storageRelationAllocationFailure =
            PhysicalAllocationMayFail (StorageFailureMapsToSource allocationFailure)
        }
  in case checkStorageRealization relation of
      Left (StorageFailureNotDeclared actual) ->
        assert (actual == allocationFailure) "wrong undeclared source failure"
      other -> Left ("undeclared allocation failure mapping was accepted: " <> show other)

capacityGuaranteeAccepted :: Either String ()
capacityGuaranteeAccepted = do
  _ <- checked ordinaryHeapRelation
    { storageRelationAllocationFailure = PhysicalAllocationMayFail
        (StorageFailureProvedUnreachable capacityEvidence) }
  Right ()

allocationAssumptionAccepted :: Either String ()
allocationAssumptionAccepted = do
  _ <- checked ordinaryHeapRelation
    { storageRelationAllocationFailure = PhysicalAllocationMayFail
        (StorageFailureAssumption allocationAssumption) }
  Right ()

deploymentRequirementAccepted :: Either String ()
deploymentRequirementAccepted = do
  _ <- checked ordinaryHeapRelation
    { storageRelationAllocationFailure = PhysicalAllocationMayFail
        (StorageFailureDeploymentRequirement deploymentCapacity) }
  Right ()

liveSemanticOwnerRejects :: Either String ()
liveSemanticOwnerRejects =
  case checkSemanticStorageTerminalClosure Map.empty
      [SemanticStorageOwner semanticStorageKey SemanticStorageOwnerLive] of
    Left (LiveSemanticStorageOwner actual) ->
      assert (actual == semanticStorageKey) "wrong live semantic storage owner"
    other -> Left ("terminal closure accepted a live semantic storage owner: " <> show other)

releasedSemanticOwnerAccepts :: Either String ()
releasedSemanticOwnerAccepts = mapLeft show $
  checkSemanticStorageTerminalClosure Map.empty
    [SemanticStorageOwner semanticStorageKey SemanticStorageOwnerReleased]

terminalDispositionIsExact :: Either String ()
terminalDispositionIsExact = do
  let permitted = Map.singleton semanticStorageKey (Set.singleton processExitDisposition)
      owner = SemanticStorageOwner semanticStorageKey
        (SemanticStorageOwnerTerminalDisposition processExitDisposition)
  mapLeft show $ checkSemanticStorageTerminalClosure permitted [owner]
  let wrong = StorageTerminalDispositionKey "storage.keep-forever"
      wrongOwner = owner { semanticStorageOwnerState =
        SemanticStorageOwnerTerminalDisposition wrong }
  case checkSemanticStorageTerminalClosure permitted [wrongOwner] of
    Left (UnpermittedSemanticStorageTerminalDisposition key actual) -> do
      assert (key == semanticStorageKey) "wrong terminal-disposition owner"
      assert (actual == wrong) "wrong rejected terminal disposition"
    other -> Left ("unpermitted semantic terminal disposition was accepted: " <> show other)

physicalLeakIsSeparateFromSemanticClosure :: Either String ()
physicalLeakIsSeparateFromSemanticClosure = do
  mapLeft show $ checkSemanticStorageTerminalClosure Map.empty []
  case checkPhysicalStorageReclamation RequirePhysicalReclamation
      [PhysicalStorageObjectState heapObject PhysicalStorageLeaked] of
    Left (PhysicalStorageLeak actual) ->
      assert (actual == heapObject) "wrong leaked physical object"
    other -> Left ("physical leak was accepted by realization checker: " <> show other)

profileRetentionAccepted :: Either String ()
profileRetentionAccepted = mapLeft show $
  checkPhysicalStorageReclamation (PermitPhysicalRetention exitReclamationProfile)
    [ PhysicalStorageObjectState heapObject
        (PhysicalStorageRetainedByProfile exitReclamationProfile)
    ]

wrongRetentionProfileRejected :: Either String ()
wrongRetentionProfileRejected =
  let actualProfile = StorageProfileRevision "profile.heap.region-v2"
  in case checkPhysicalStorageReclamation
      (PermitPhysicalRetention exitReclamationProfile)
      [PhysicalStorageObjectState heapObject (PhysicalStorageRetainedByProfile actualProfile)] of
      Left (PhysicalStorageRetentionProfileMismatch object expected actual) -> do
        assert (object == heapObject) "wrong retained physical object"
        assert (expected == exitReclamationProfile) "wrong expected reclamation profile"
        assert (actual == actualProfile) "wrong actual reclamation profile"
      other -> Left ("wrong physical retention profile was accepted: " <> show other)

alternateStorageCostsAreAttributable :: Either String ()
alternateStorageCostsAreAttributable = do
  inline <- checked ordinaryInlineRelation
  heap <- checked ordinaryHeapRelation
  mapLeft show $ checkEquivalentStorageRealizations inline heap
  _ <- mapLeft show $ checkStorageCostLineage inline inlineCost
  _ <- mapLeft show $ checkStorageCostLineage heap heapCost
  assert (inlineCost /= heapCost) "alternate storage strategies lost distinct cost lineage"

missingStorageCostRejected :: Either String ()
missingStorageCostRejected = do
  inline <- checked ordinaryInlineRelation
  let missing = StorageCostLineage
        { storageCostSubject = ordinarySubject
        , storageCostPhysicalObjects = Set.empty
        , storageCostClass = TargetRequired
        , storageCostShape = emptyCostShape
        , storageCostResidencyRefs = Set.empty
        , storageCostCleanupRefs = Set.empty
        }
  case checkStorageCostLineage inline missing of
    Left StorageCostHasNoAttributableStorageFact -> Right ()
    other -> Left ("missing storage cost lineage was accepted: " <> show other)

checked :: StorageRealizationRelation -> Either String CheckedStorageRealization
checked = mapLeft show . checkStorageRealization

ordinaryInlineRelation, ordinaryHeapRelation :: StorageRealizationRelation
ordinaryInlineRelation = baseRelation
  (ExactStorageSemanticSubject ordinarySubject)
  (PhysicalStorageStrategy "register-or-inline")
  Set.empty
  (RealizationRevision "realization.value.inline.v1")
  PhysicalAllocationCannotFail

ordinaryHeapRelation = baseRelation
  (ExactStorageSemanticSubject ordinarySubject)
  (PhysicalStorageStrategy "qualified-hidden-heap")
  (Set.singleton heapObject)
  (RealizationRevision "realization.value.heap.v1")
  (PhysicalAllocationMayFail (StorageFailureProvedUnreachable capacityEvidence))

semanticArenaRelation, semanticDeviceRelation :: StorageRealizationRelation
semanticArenaRelation = (baseRelation
  (ExactStorageSemanticSubject semanticStorageSubject)
  (PhysicalStorageStrategy "qualified-arena-region")
  (Set.singleton arenaObject)
  (RealizationRevision "realization.storage.arena.v1")
  PhysicalAllocationCannotFail)
  { storageRelationSourceSemanticRevision = semanticStorageRevision
  , storageRelationSourceOutcomeRevision = semanticStorageOutcomeRevision
  }

semanticDeviceRelation = (baseRelation
  (ExactStorageSemanticSubject semanticStorageSubject)
  (PhysicalStorageStrategy "qualified-device-storage")
  (Set.singleton deviceObject)
  (RealizationRevision "realization.storage.device.v1")
  (PhysicalAllocationMayFail (StorageFailureDeploymentRequirement deploymentCapacity)))
  { storageRelationSourceSemanticRevision = semanticStorageRevision
  , storageRelationSourceOutcomeRevision = semanticStorageOutcomeRevision
  }

baseRelation
  :: StorageSubjectBinding
  -> PhysicalStorageStrategy
  -> Set.Set PhysicalStorageObjectKey
  -> RealizationRevision
  -> PhysicalAllocationFailure
  -> StorageRealizationRelation
baseRelation subject strategy objects realization physicalFailure = StorageRealizationRelation
  { storageRelationSubject = subject
  , storageRelationSourceSemanticRevision = ordinarySemanticRevision
  , storageRelationSourceOutcomeRevision = ordinaryOutcomeRevision
  , storageRelationPhysicalStrategy = strategy
  , storageRelationPhysicalObjects = objects
  , storageRelationRealizationRevision = realization
  , storageRelationSourceFailureSurface = SourceStorageInfallible
  , storageRelationAllocationFailure = physicalFailure
  }

inlineCost, heapCost :: StorageCostLineage
inlineCost = StorageCostLineage
  { storageCostSubject = ordinarySubject
  , storageCostPhysicalObjects = Set.empty
  , storageCostClass = TargetRequired
  , storageCostShape = emptyCostShape
      { costAllocationCount = Just "0"
      , costPeakLiveMemory = Just "0 hidden bytes"
      }
  , storageCostResidencyRefs = Set.singleton (StorageResidencyRef "residency.register-or-inline")
  , storageCostCleanupRefs = Set.empty
  }

heapCost = StorageCostLineage
  { storageCostSubject = ordinarySubject
  , storageCostPhysicalObjects = Set.singleton heapObject
  , storageCostClass = TargetRequired
  , storageCostShape = emptyCostShape
      { costAllocationCount = Just "1"
      , costPeakLiveMemory = Just "4096 bytes"
      , costBytesCopied = Just "0"
      }
  , storageCostResidencyRefs = Set.singleton (StorageResidencyRef "residency.heap")
  , storageCostCleanupRefs = Set.singleton (StorageCleanupRef "cleanup.heap.release")
  }

ordinarySubject, otherOrdinarySubject, semanticStorageSubject :: StorageSemanticSubject
ordinarySubject = OrdinarySemanticValue (SemanticValueKey "value.record.001")
otherOrdinarySubject = OrdinarySemanticValue (SemanticValueKey "value.record.002")
semanticStorageSubject = ExplicitSemanticStorageResource semanticStorageKey

semanticStorageKey :: SemanticStorageResourceKey
semanticStorageKey = SemanticStorageResourceKey "storage.region.001"

ordinarySemanticRevision, semanticStorageRevision :: StorageSemanticRevision
ordinarySemanticRevision = StorageSemanticRevision "semantic.value.record.v1"
semanticStorageRevision = StorageSemanticRevision "semantic.storage.region.v1"

ordinaryOutcomeRevision, semanticStorageOutcomeRevision :: StorageOutcomeRevision
ordinaryOutcomeRevision = StorageOutcomeRevision "outcomes.value.construct.infallible.v1"
semanticStorageOutcomeRevision = StorageOutcomeRevision "outcomes.storage.region.v1"

heapObject, arenaObject, deviceObject :: PhysicalStorageObjectKey
heapObject = PhysicalStorageObjectKey "physical.heap.object.001"
arenaObject = PhysicalStorageObjectKey "physical.arena.region.001"
deviceObject = PhysicalStorageObjectKey "physical.device.buffer.001"

allocationFailure :: StorageFailureKey
allocationFailure = StorageFailureKey "storage.allocation-failure"

capacityEvidence :: StorageCapacityEvidenceKey
capacityEvidence = StorageCapacityEvidenceKey "evidence.heap.capacity.4096.v1"

allocationAssumption :: StorageAssumptionKey
allocationAssumption = StorageAssumptionKey "assume.allocator.success.scope.v1"

deploymentCapacity :: StorageDeploymentRequirementKey
deploymentCapacity = StorageDeploymentRequirementKey "deploy.storage.capacity.4096.v1"

processExitDisposition :: StorageTerminalDispositionKey
processExitDisposition = StorageTerminalDispositionKey "storage.region.release-at-process-exit.v1"

exitReclamationProfile :: StorageProfileRevision
exitReclamationProfile = StorageProfileRevision "profile.heap.process-exit-reclamation.v1"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
