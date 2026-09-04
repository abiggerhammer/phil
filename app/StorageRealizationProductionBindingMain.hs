{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as Set
import Phil.Core.Static (RealizationRevision (..))
import Phil.Systems.Storage
import Phil.Systems.StorageRealizationCertification
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "certified MEM-001 accepts native-valid realization" certifiedAccepts
    , test "native physical-coincidence diagnostic precedes kernel" physicalCoincidencePrecedesKernel
    , test "native semantic-revision diagnostic precedes kernel" emptySemanticRevisionPrecedesKernel
    , test "native realization-revision diagnostic precedes kernel" emptyRealizationRevisionPrecedesKernel
    , test "reflected valid realization produces all seven true facts" reflectedFactsAreExact
    , test "exact extracted seven-fact gate accepts all true" allTrueFactsAccept
    , test "kernel disagreement fails closed for every single false fact" everySingleFalseFactRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

certifiedAccepts :: Either String ()
certifiedAccepts = do
  _ <- mapLeft show (checkStorageRealizationCertified validRelation)
  Right ()

physicalCoincidencePrecedesKernel :: Either String ()
physicalCoincidencePrecedesKernel =
  case checkStorageRealizationCertified validRelation
      { storageRelationSubject = PhysicalStorageCoincidence physicalObject } of
    Left (StorageRealizationCertificationNativeError
      (StoragePhysicalCoincidenceIsNotSemanticIdentity actual))
        | actual == physicalObject -> Right ()
    other -> Left ("unexpected result: " <> show other)

emptySemanticRevisionPrecedesKernel :: Either String ()
emptySemanticRevisionPrecedesKernel =
  case checkStorageRealizationCertified validRelation
      { storageRelationSourceSemanticRevision = StorageSemanticRevision "" } of
    Left (StorageRealizationCertificationNativeError
      (StorageMissingIdentity "source semantic revision")) -> Right ()
    other -> Left ("unexpected result: " <> show other)

emptyRealizationRevisionPrecedesKernel :: Either String ()
emptyRealizationRevisionPrecedesKernel =
  case checkStorageRealizationCertified validRelation
      { storageRelationRealizationRevision = RealizationRevision "" } of
    Left (StorageRealizationCertificationNativeError
      (StorageMissingIdentity "architecture realization revision")) -> Right ()
    other -> Left ("unexpected result: " <> show other)

reflectedFactsAreExact :: Either String ()
reflectedFactsAreExact =
  assert (storageRealizationKernelFacts validRelation == allTrueFacts)
    "valid concrete realization did not reflect to all seven proof facts"

allTrueFactsAccept :: Either String ()
allTrueFactsAccept = mapLeft show $ verifyStorageRealizationKernelFacts allTrueFacts

everySingleFalseFactRejects :: Either String ()
everySingleFalseFactRejects =
  mapM_ rejects singleFalseFacts
  where
    rejects facts = case verifyStorageRealizationKernelFacts facts of
      Left (StorageRealizationCertificationKernelDisagreement actual)
        | actual == facts -> Right ()
      other -> Left ("kernel did not fail closed for " <> show facts <> ": " <> show other)

singleFalseFacts :: [StorageRealizationKernelFacts]
singleFalseFacts =
  [ allTrueFacts { storageKernelSubjectBasisAdmitted = False }
  , allTrueFacts { storageKernelExactSubjectPresent = False }
  , allTrueFacts { storageKernelSemanticRevisionNonzero = False }
  , allTrueFacts { storageKernelOutcomeRevisionNonzero = False }
  , allTrueFacts { storageKernelPhysicalStrategyNonzero = False }
  , allTrueFacts { storageKernelSelectedSemanticsNonzero = False }
  , allTrueFacts { storageKernelPhysicalObjectsNonzero = False }
  ]

allTrueFacts :: StorageRealizationKernelFacts
allTrueFacts = StorageRealizationKernelFacts
  { storageKernelSubjectBasisAdmitted = True
  , storageKernelExactSubjectPresent = True
  , storageKernelSemanticRevisionNonzero = True
  , storageKernelOutcomeRevisionNonzero = True
  , storageKernelPhysicalStrategyNonzero = True
  , storageKernelSelectedSemanticsNonzero = True
  , storageKernelPhysicalObjectsNonzero = True
  }

validRelation :: StorageRealizationRelation
validRelation = StorageRealizationRelation
  { storageRelationSubject = ExactStorageSemanticSubject semanticSubject
  , storageRelationSourceSemanticRevision = StorageSemanticRevision "semantic.value.v1"
  , storageRelationSourceOutcomeRevision = StorageOutcomeRevision "outcomes.value.v1"
  , storageRelationPhysicalStrategy = PhysicalStorageStrategy "qualified-hidden-heap"
  , storageRelationPhysicalObjects = Set.singleton physicalObject
  , storageRelationRealizationRevision = RealizationRevision "realization.value.heap.v1"
  , storageRelationSourceFailureSurface = SourceStorageInfallible
  , storageRelationAllocationFailure = PhysicalAllocationCannotFail
  }

semanticSubject :: StorageSemanticSubject
semanticSubject = OrdinarySemanticValue (SemanticValueKey "value.record.001")

physicalObject :: PhysicalStorageObjectKey
physicalObject = PhysicalStorageObjectKey "physical.heap.object.001"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
