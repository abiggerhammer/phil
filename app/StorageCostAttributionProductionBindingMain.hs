{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Static (RealizationRevision (..))
import Phil.Examples.Phase1.StageClosureWitnesses (uploadStageClosureBundle)
import Phil.Systems.CostAttribution
  ( CostAttributionStageBundle (..)
  , CostChargeIdentity (..)
  , CostContribution (..)
  )
import Phil.Systems.IR
  ( CostClass (..)
  , CostShape (..)
  , emptyCostShape
  )
import Phil.Systems.NextStageRequirement
  ( NextStageRequirementStageBundle (..)
  )
import Phil.Systems.StageClosure (StageClosureBundle (..))
import Phil.Systems.Storage
import Phil.Systems.StorageCostAttributionCertification
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "certified storage cost attribution accepts real StageClosure charge binding"
        certifiedAttributionAccepted
    , test "native storage subject diagnostic precedes storage cost kernel"
        subjectMismatchNativePrecedence
    , test "native physical-domain diagnostic precedes storage cost kernel"
        physicalDomainNativePrecedence
    , test "native missing-attribution diagnostic precedes storage cost kernel"
        missingAttributionNativePrecedence
    , test "injected storage-lineage disagreement fails closed"
        lineageInjectedDisagreement
    , test "wrong SYS-018 charge identity rejects binding"
        wrongChargeRejected
    , test "wrong SYS-018 cost class rejects binding"
        wrongClassRejected
    , test "wrong SYS-018 cost shape rejects binding"
        wrongShapeRejected
    , test "injected storage/runtime binding disagreement fails closed"
        bindingInjectedDisagreement
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

certifiedAttributionAccepted :: Either String ()
certifiedAttributionAccepted = do
  (stage, relation, lineage, binding, _, _) <- fixture
  _ <- mapLeft show $ certifyStorageCostAttribution stage relation lineage binding
  Right ()

subjectMismatchNativePrecedence :: Either String ()
subjectMismatchNativePrecedence = do
  (stage, relation, lineage, binding, _, _) <- fixture
  let wrongSubject = ExplicitSemanticStorageResource
        (SemanticStorageResourceKey "storage.cost.subject.other")
      wrong = lineage { storageCostSubject = wrongSubject }
      expected = storageCostSubject lineage
  case certifyStorageCostAttribution stage relation wrong binding of
    Left (StorageCostAttributionNativeStorageError
      (StorageCostSubjectMismatch actualExpected actualWrong)) -> do
        assert (actualExpected == expected) "subject mismatch lost expected subject"
        assert (actualWrong == wrongSubject) "subject mismatch lost actual subject"
    other -> Left ("subject mismatch did not preserve native diagnostic: " <> show other)

physicalDomainNativePrecedence :: Either String ()
physicalDomainNativePrecedence = do
  (stage, relation, lineage, binding, _, _) <- fixture
  let wrongObjects = Set.singleton (PhysicalStorageObjectKey "storage.cost.object.other")
      wrong = lineage { storageCostPhysicalObjects = wrongObjects }
      expected = storageCostPhysicalObjects lineage
  case certifyStorageCostAttribution stage relation wrong binding of
    Left (StorageCostAttributionNativeStorageError
      (StorageCostPhysicalDomainMismatch actualExpected actualWrong)) -> do
        assert (actualExpected == expected) "physical mismatch lost expected domain"
        assert (actualWrong == wrongObjects) "physical mismatch lost actual domain"
    other -> Left ("physical mismatch did not preserve native diagnostic: " <> show other)

missingAttributionNativePrecedence :: Either String ()
missingAttributionNativePrecedence = do
  (stage, relation, lineage, binding, _, _) <- fixture
  let missing = lineage
        { storageCostShape = emptyCostShape
        , storageCostResidencyRefs = Set.empty
        , storageCostCleanupRefs = Set.empty
        }
  case certifyStorageCostAttribution stage relation missing binding of
    Left (StorageCostAttributionNativeStorageError
      StorageCostHasNoAttributableStorageFact) -> Right ()
    other -> Left ("missing attribution did not preserve native diagnostic: " <> show other)

lineageInjectedDisagreement :: Either String ()
lineageInjectedDisagreement =
  let facts = StorageCostLineageKernelFacts
        { storageCostKernelSubjectExact = False
        , storageCostKernelPhysicalDomainExact = True
        , storageCostKernelAllocationCountPresent = True
        , storageCostKernelPeakLiveMemoryPresent = False
        , storageCostKernelBytesCopiedPresent = False
        , storageCostKernelResidencyRefPresent = False
        , storageCostKernelCleanupRefPresent = False
        }
  in case verifyStorageCostLineageKernelFacts facts of
      Left (StorageCostAttributionLineageKernelDisagreement actual) ->
        assert (actual == facts) "lineage disagreement lost reflected facts"
      other -> Left ("lineage disagreement did not fail closed: " <> show other)

wrongChargeRejected :: Either String ()
wrongChargeRejected = do
  (stage, _, lineage, binding, expectedCharge, _) <- fixture
  let wrongCharge = CostChargeIdentity "storage.cost.wrong-charge"
      wrongBinding = binding { storageRuntimeCostCharge = wrongCharge }
  case checkStorageRuntimeCostBindingCertified stage lineage wrongBinding of
    Left (StorageCostAttributionChargeMismatch actual requested) -> do
      assert (actual == expectedCharge) "charge mismatch lost actual SYS-018 charge"
      assert (requested == wrongCharge) "charge mismatch lost requested charge"
    other -> Left ("wrong charge did not reject: " <> show other)

wrongClassRejected :: Either String ()
wrongClassRejected = do
  (stage, _, lineage, binding, _, contribution) <- fixture
  let nativeClass = costContributionClass contribution
      wrongClass = differentCostClass nativeClass
      wrong = lineage { storageCostClass = wrongClass }
  case checkStorageRuntimeCostBindingCertified stage wrong binding of
    Left (StorageCostAttributionClassMismatch actual requested) -> do
      assert (actual == nativeClass) "class mismatch lost SYS-018 class"
      assert (requested == wrongClass) "class mismatch lost storage class"
    other -> Left ("wrong class did not reject: " <> show other)

wrongShapeRejected :: Either String ()
wrongShapeRejected = do
  (stage, _, lineage, binding, _, contribution) <- fixture
  let nativeShape = costContributionShape contribution
      wrongShape = differentCostShape nativeShape
      wrong = lineage { storageCostShape = wrongShape }
  case checkStorageRuntimeCostBindingCertified stage wrong binding of
    Left (StorageCostAttributionShapeMismatch actual requested) -> do
      assert (actual == nativeShape) "shape mismatch lost SYS-018 shape"
      assert (requested == wrongShape) "shape mismatch lost storage shape"
    other -> Left ("wrong shape did not reject: " <> show other)

bindingInjectedDisagreement :: Either String ()
bindingInjectedDisagreement =
  let facts = StorageRuntimeCostBindingKernelFacts
        { storageRuntimeCostContributionInCharge = True
        , storageRuntimeCostClassExact = False
        , storageRuntimeCostShapeExact = True
        }
  in case verifyStorageRuntimeCostBindingKernelFacts facts of
      Left (StorageCostAttributionBindingKernelDisagreement actual) ->
        assert (actual == facts) "binding disagreement lost reflected facts"
      other -> Left ("binding disagreement did not fail closed: " <> show other)

fixture
  :: Either String
       ( StageClosureBundle
       , StorageRealizationRelation
       , StorageCostLineage
       , StorageRuntimeCostBinding
       , CostChargeIdentity
       , CostContribution
       )
fixture = do
  stage <- uploadStageClosureBundle
  let costStage = nextStageRequirementStageBase (stageClosureNextStage stage)
  (contributionId, contribution) <- case Map.toAscList
      (costAttributionStageContributions costStage) of
    [] -> Left "upload StageClosure has no SYS-018 cost contribution"
    first : _ -> Right first
  charge <- maybe
    (Left "upload StageClosure contribution has no final charge")
    Right
    (Map.lookup contributionId (costAttributionStageContributionCharges costStage))
  let subject = OrdinarySemanticValue (SemanticValueKey "storage.cost.subject")
      objects = Set.singleton (PhysicalStorageObjectKey "storage.cost.object")
      relation = StorageRealizationRelation
        { storageRelationSubject = ExactStorageSemanticSubject subject
        , storageRelationSourceSemanticRevision = StorageSemanticRevision "semantic.storage.cost.v1"
        , storageRelationSourceOutcomeRevision = StorageOutcomeRevision "outcome.storage.cost.v1"
        , storageRelationPhysicalStrategy = PhysicalStorageStrategy "qualified-storage-cost"
        , storageRelationPhysicalObjects = objects
        , storageRelationRealizationRevision = RealizationRevision "realization.storage.cost.v1"
        , storageRelationSourceFailureSurface = SourceStorageInfallible
        , storageRelationAllocationFailure = PhysicalAllocationCannotFail
        }
      lineage = StorageCostLineage
        { storageCostSubject = subject
        , storageCostPhysicalObjects = objects
        , storageCostClass = costContributionClass contribution
        , storageCostShape = costContributionShape contribution
        , storageCostResidencyRefs = Set.singleton
            (StorageResidencyRef "storage.cost.residency")
        , storageCostCleanupRefs = Set.empty
        }
      binding = StorageRuntimeCostBinding
        { storageRuntimeCostContribution = contributionId
        , storageRuntimeCostCharge = charge
        }
  Right (stage, relation, lineage, binding, charge, contribution)

differentCostClass :: CostClass -> CostClass
differentCostClass value
  | value == SemanticRequired = RuntimeAssuranceRequired
  | otherwise = SemanticRequired

differentCostShape :: CostShape -> CostShape
differentCostShape shape = shape
  { costCompileTime = differentMaybeText (costCompileTime shape) }

differentMaybeText :: Maybe Text -> Maybe Text
differentMaybeText value
  | value == Just "storage-cost-mismatch" = Just "storage-cost-other"
  | otherwise = Just "storage-cost-mismatch"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
