{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as Set
import Phil.Core.Static (RealizationRevision (..))
import Phil.Systems.Storage
import Phil.Systems.StorageAllocationFailureCertification
import Phil.Systems.StorageRealizationCertification
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "certified MEM-002/003 accepts cannot-fail realization"
        cannotFailAccepts
    , test "certified MEM-002/003 accepts exact declared source mapping"
        mappedFailureAccepts
    , test "certified MEM-002/003 accepts checked-capacity evidence"
        capacityEvidenceAccepts
    , test "certified MEM-002/003 accepts explicit assumption"
        assumptionAccepts
    , test "certified MEM-002/003 accepts explicit deployment requirement"
        deploymentRequirementAccepts
    , test "native unaccounted-failure diagnostic precedes allocation kernel"
        unaccountedNativeDiagnosticPrecedesKernel
    , test "native undeclared-source diagnostic precedes allocation kernel"
        undeclaredSourceNativeDiagnosticPrecedesKernel
    , test "mapped-failure reflection preserves exact two proof facts"
        mappedFailureReflectionExact
    , test "injected mapped-failure disagreement fails closed"
        mappedFailureDisagreementFailsClosed
    , test "unaccounted extracted gate fails closed"
        unaccountedGateFailsClosed
    , test "outer extracted gate rejects predecessor failure"
        outerPredecessorFailureRejects
    , test "outer extracted gate rejects disposition failure"
        outerDispositionFailureRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

cannotFailAccepts :: Either String ()
cannotFailAccepts = do
  _ <- mapLeft show $ checkStorageAllocationFailureCertified cannotFailRelation
  Right ()

mappedFailureAccepts :: Either String ()
mappedFailureAccepts = do
  _ <- mapLeft show $ checkStorageAllocationFailureCertified mappedFailureRelation
  Right ()

capacityEvidenceAccepts :: Either String ()
capacityEvidenceAccepts = do
  _ <- mapLeft show $ checkStorageAllocationFailureCertified capacityRelation
  Right ()

assumptionAccepts :: Either String ()
assumptionAccepts = do
  _ <- mapLeft show $ checkStorageAllocationFailureCertified assumptionRelation
  Right ()

deploymentRequirementAccepts :: Either String ()
deploymentRequirementAccepts = do
  _ <- mapLeft show $ checkStorageAllocationFailureCertified deploymentRelation
  Right ()

unaccountedNativeDiagnosticPrecedesKernel :: Either String ()
unaccountedNativeDiagnosticPrecedesKernel =
  case checkStorageAllocationFailureCertified unaccountedRelation of
    Left (StorageAllocationFailureCertificationPredecessorError
      (StorageRealizationCertificationNativeError
        StorageUnaccountedAllocationFailure)) -> Right ()
    other -> Left ("wrong unaccounted-failure result: " <> show other)

undeclaredSourceNativeDiagnosticPrecedesKernel :: Either String ()
undeclaredSourceNativeDiagnosticPrecedesKernel =
  case checkStorageAllocationFailureCertified undeclaredMappedRelation of
    Left (StorageAllocationFailureCertificationPredecessorError
      (StorageRealizationCertificationNativeError
        (StorageFailureNotDeclared actual))) ->
      assert (actual == allocationFailure) "wrong undeclared source failure"
    other -> Left ("wrong undeclared-source result: " <> show other)

mappedFailureReflectionExact :: Either String ()
mappedFailureReflectionExact =
  assert
    (storageAllocationFailureDispositionKernelFacts mappedFailureRelation
      == StorageFailureMapsToSourceKernelFacts True True)
    "mapped-failure proof facts changed"

mappedFailureDisagreementFailsClosed :: Either String ()
mappedFailureDisagreementFailsClosed =
  let facts = StorageFailureMapsToSourceKernelFacts True False
  in case verifyStorageAllocationFailureDispositionKernelFacts facts of
      Left (StorageAllocationFailureCertificationDispositionKernelDisagreement actual) ->
        assert (actual == facts) "wrong mapped-failure disagreement facts"
      other -> Left ("injected mapped-failure disagreement accepted: " <> show other)

unaccountedGateFailsClosed :: Either String ()
unaccountedGateFailsClosed =
  let facts = StorageFailureUnaccountedKernelFacts
  in case verifyStorageAllocationFailureDispositionKernelFacts facts of
      Left (StorageAllocationFailureCertificationDispositionKernelDisagreement actual) ->
        assert (actual == facts) "wrong unaccounted disagreement facts"
      other -> Left ("unaccounted extracted gate accepted: " <> show other)

outerPredecessorFailureRejects :: Either String ()
outerPredecessorFailureRejects =
  case verifyStorageAllocationFailureRealizationKernelFacts False True of
    Left (StorageAllocationFailureCertificationRealizationKernelDisagreement
      False True) -> Right ()
    other -> Left ("outer gate accepted false predecessor: " <> show other)

outerDispositionFailureRejects :: Either String ()
outerDispositionFailureRejects =
  case verifyStorageAllocationFailureRealizationKernelFacts True False of
    Left (StorageAllocationFailureCertificationRealizationKernelDisagreement
      True False) -> Right ()
    other -> Left ("outer gate accepted false disposition: " <> show other)

cannotFailRelation :: StorageRealizationRelation
cannotFailRelation = baseRelation SourceStorageInfallible PhysicalAllocationCannotFail

mappedFailureRelation :: StorageRealizationRelation
mappedFailureRelation = baseRelation
  (SourceStorageFailures (Set.singleton allocationFailure))
  (PhysicalAllocationMayFail (StorageFailureMapsToSource allocationFailure))

capacityRelation :: StorageRealizationRelation
capacityRelation = baseRelation SourceStorageInfallible
  (PhysicalAllocationMayFail (StorageFailureProvedUnreachable capacityEvidence))

assumptionRelation :: StorageRealizationRelation
assumptionRelation = baseRelation SourceStorageInfallible
  (PhysicalAllocationMayFail (StorageFailureAssumption allocationAssumption))

deploymentRelation :: StorageRealizationRelation
deploymentRelation = baseRelation SourceStorageInfallible
  (PhysicalAllocationMayFail
    (StorageFailureDeploymentRequirement deploymentRequirement))

unaccountedRelation :: StorageRealizationRelation
unaccountedRelation = baseRelation SourceStorageInfallible
  (PhysicalAllocationMayFail StorageFailureUnaccounted)

undeclaredMappedRelation :: StorageRealizationRelation
undeclaredMappedRelation = baseRelation SourceStorageInfallible
  (PhysicalAllocationMayFail (StorageFailureMapsToSource allocationFailure))

baseRelation
  :: SourceStorageFailureSurface
  -> PhysicalAllocationFailure
  -> StorageRealizationRelation
baseRelation sourceSurface physicalFailure = StorageRealizationRelation
  { storageRelationSubject = ExactStorageSemanticSubject
      (OrdinarySemanticValue (SemanticValueKey "value.record.001"))
  , storageRelationSourceSemanticRevision =
      StorageSemanticRevision "semantic.value.record.v1"
  , storageRelationSourceOutcomeRevision =
      StorageOutcomeRevision "outcomes.value.construct.v1"
  , storageRelationPhysicalStrategy =
      PhysicalStorageStrategy "qualified-hidden-heap"
  , storageRelationPhysicalObjects =
      Set.singleton (PhysicalStorageObjectKey "physical.heap.object.001")
  , storageRelationRealizationRevision =
      RealizationRevision "realization.value.heap.v1"
  , storageRelationSourceFailureSurface = sourceSurface
  , storageRelationAllocationFailure = physicalFailure
  }

allocationFailure :: StorageFailureKey
allocationFailure = StorageFailureKey "storage.allocation-failure"

capacityEvidence :: StorageCapacityEvidenceKey
capacityEvidence = StorageCapacityEvidenceKey "evidence.heap.capacity.4096.v1"

allocationAssumption :: StorageAssumptionKey
allocationAssumption = StorageAssumptionKey "assume.allocator.success.scope.v1"

deploymentRequirement :: StorageDeploymentRequirementKey
deploymentRequirement =
  StorageDeploymentRequirementKey "deploy.storage.capacity.4096.v1"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
