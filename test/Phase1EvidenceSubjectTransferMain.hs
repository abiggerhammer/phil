{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Examples.Phase1.BoundaryCommitWitnesses
  ( uploadBoundaryCommitStageBundle
  )
import Phil.Examples.Phase1.EvidenceTransferWitnesses
import Phil.Examples.Phase1.SubjectWitnesses
  ( steveCandidateSubject
  , steveReadSubject
  )
import Phil.Systems.BoundaryCommitCorrespondence
  ( verifyBoundaryCommitStageBundle
  )
import Phil.Systems.EvidenceSubjectTransfer
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SYS-011 SYS-010 upload predecessor remains valid" uploadBoundaryRegression
    , test "SYS-011 upload evidence rebind without relation rejects" uploadMissingRelationRejected
    , test "SYS-011 Steve evidence rebind without relation rejects" steveMissingRelationRejected
    , test "SYS-011 exact checked copy relation permits named evidence" checkedCopyAccepted
    , test "SYS-011 runtime representation coincidence is not copy correspondence" runtimeCoincidenceRejected
    , test "SYS-011 relation endpoints must match rebinding endpoints" endpointMismatchRejected
    , test "SYS-011 evidence must exist on exact source subject" missingSourceEvidenceRejected
    , test "SYS-011 copy relation is proposition-specific" unlistedEvidenceRejected
    , test "SYS-011 unknown relation rejects" unknownRelationRejected
    , test "SYS-011 empty rebinding evidence set rejects" emptyEvidenceRejected
    , test "SYS-011 transfer-stage identity is deterministic" deterministicIdentity
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

uploadBoundaryRegression :: Either String ()
uploadBoundaryRegression = do
  bundle <- uploadBoundaryCommitStageBundle
  mapLeft show (verifyBoundaryCommitStageBundle bundle)

uploadMissingRelationRejected :: Either String ()
uploadMissingRelationRejected =
  case verifyEvidenceTransferStageBundle uploadEvidenceTransferWithoutRelation of
    Left (EvidenceRebindingMissingRelation key)
      | key == evidenceRebindingKey uploadUncheckedRebinding -> Right ()
    other -> Left ("upload evidence rebind was not rejected correctly: " <> show other)

steveMissingRelationRejected :: Either String ()
steveMissingRelationRejected = do
  bundle <- steveEvidenceTransferWithoutRelation
  case verifyEvidenceTransferStageBundle bundle of
    Left (EvidenceRebindingMissingRelation key)
      | key == evidenceRebindingKey steveUncheckedRebinding -> Right ()
    other -> Left ("Steve evidence rebind was not rejected correctly: " <> show other)

checkedCopyAccepted :: Either String ()
checkedCopyAccepted = do
  bundle <- steveCheckedCopyTransfer
  mapLeft show (verifyEvidenceTransferStageBundle bundle)

runtimeCoincidenceRejected :: Either String ()
runtimeCoincidenceRejected = do
  original <- steveCheckedCopyTransfer
  let relationKey = subjectTransferRelationKey steveSyntheticCopyRelation
      badRelation = steveSyntheticCopyRelation
        { subjectTransferBasis = RuntimeSubjectCoincidence
            "same allocation address and equal bytes" }
      mutated = makeEvidenceTransferStageBundle
        (evidenceTransferStageBase original)
        (Map.singleton relationKey badRelation)
        (evidenceTransferStageRebindings original)
  case verifyEvidenceTransferStageBundle mutated of
    Left (SubjectTransferRuntimeCoincidenceRejected actual _)
      | actual == relationKey -> Right ()
    other -> Left ("runtime coincidence was accepted as copy relation: " <> show other)

endpointMismatchRejected :: Either String ()
endpointMismatchRejected = do
  original <- steveCheckedCopyTransfer
  let relationKey = subjectTransferRelationKey steveSyntheticCopyRelation
      reversed = steveSyntheticCopyRelation
        { subjectTransferSource = steveReadSubject
        , subjectTransferTarget = steveCandidateSubject
        }
      mutated = makeEvidenceTransferStageBundle
        (evidenceTransferStageBase original)
        (Map.singleton relationKey reversed)
        (evidenceTransferStageRebindings original)
  case verifyEvidenceTransferStageBundle mutated of
    Left (EvidenceRebindingRelationEndpointMismatch key actual _ _)
      | key == evidenceRebindingKey steveCheckedRebinding
          && actual == relationKey -> Right ()
    other -> Left ("relation endpoint mismatch was accepted: " <> show other)

missingSourceEvidenceRejected :: Either String ()
missingSourceEvidenceRejected = do
  original <- steveCheckedCopyTransfer
  let badClaim = steveCheckedRebinding
        { evidenceRebindingEvidenceRefs = Set.singleton "steve.provider.admission-lineage" }
      mutated = makeEvidenceTransferStageBundle
        (evidenceTransferStageBase original)
        (evidenceTransferStageRelations original)
        (Map.singleton (evidenceRebindingKey badClaim) badClaim)
  case verifyEvidenceTransferStageBundle mutated of
    Left (EvidenceRebindingSourceEvidenceMissing key evidenceRef)
      | key == evidenceRebindingKey badClaim
          && evidenceRef == "steve.provider.admission-lineage" -> Right ()
    other -> Left ("missing source evidence was accepted: " <> show other)

unlistedEvidenceRejected :: Either String ()
unlistedEvidenceRejected = do
  original <- steveCheckedCopyTransfer
  let badClaim = steveCheckedRebinding
        { evidenceRebindingEvidenceRefs = Set.singleton "steve.digest.stable-subject" }
      mutated = makeEvidenceTransferStageBundle
        (evidenceTransferStageBase original)
        (evidenceTransferStageRelations original)
        (Map.singleton (evidenceRebindingKey badClaim) badClaim)
  case verifyEvidenceTransferStageBundle mutated of
    Left (EvidenceRebindingEvidenceNotTransferable key relationKey evidenceRef)
      | key == evidenceRebindingKey badClaim
          && relationKey == subjectTransferRelationKey steveSyntheticCopyRelation
          && evidenceRef == "steve.digest.stable-subject" -> Right ()
    other -> Left ("unlisted evidence was transferred: " <> show other)

unknownRelationRejected :: Either String ()
unknownRelationRejected = do
  original <- steveCheckedCopyTransfer
  let missing = SubjectTransferRelationKey "copy.not-registered"
      badClaim = steveCheckedRebinding { evidenceRebindingRelation = Just missing }
      mutated = makeEvidenceTransferStageBundle
        (evidenceTransferStageBase original)
        (evidenceTransferStageRelations original)
        (Map.singleton (evidenceRebindingKey badClaim) badClaim)
  case verifyEvidenceTransferStageBundle mutated of
    Left (EvidenceRebindingUnknownRelation key actual)
      | key == evidenceRebindingKey badClaim && actual == missing -> Right ()
    other -> Left ("unknown relation was accepted: " <> show other)

emptyEvidenceRejected :: Either String ()
emptyEvidenceRejected = do
  original <- steveCheckedCopyTransfer
  let badClaim = steveCheckedRebinding { evidenceRebindingEvidenceRefs = Set.empty }
      mutated = makeEvidenceTransferStageBundle
        (evidenceTransferStageBase original)
        (evidenceTransferStageRelations original)
        (Map.singleton (evidenceRebindingKey badClaim) badClaim)
  case verifyEvidenceTransferStageBundle mutated of
    Left (EvidenceRebindingEmptyEvidenceSet key)
      | key == evidenceRebindingKey badClaim -> Right ()
    other -> Left ("empty evidence rebind was accepted: " <> show other)

deterministicIdentity :: Either String ()
deterministicIdentity = do
  original <- steveCheckedCopyTransfer
  let secondKey = EvidenceRebindingKey "test.steve.borrow-evidence.rebind-with-copy.second"
      secondClaim = steveCheckedRebinding { evidenceRebindingKey = secondKey }
      claims = Map.fromList
        [ (evidenceRebindingKey steveCheckedRebinding, steveCheckedRebinding)
        , (secondKey, secondClaim)
        ]
      forward = makeEvidenceTransferStageBundle
        (evidenceTransferStageBase original)
        (evidenceTransferStageRelations original)
        claims
      reverseOrder = makeEvidenceTransferStageBundle
        (evidenceTransferStageBase original)
        (Map.fromList (reverse (Map.toAscList (evidenceTransferStageRelations original))))
        (Map.fromList (reverse (Map.toAscList claims)))
  assert (evidenceTransferStageRevision forward == evidenceTransferStageRevision reverseOrder)
    "evidence-transfer revision changed with map enumeration order"
  mapLeft show (verifyEvidenceTransferStageBundle reverseOrder)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
