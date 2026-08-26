{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Examples.Phase1.EvidenceErasureWitnesses
import Phil.Examples.Phase1.EvidenceTransferWitnesses
  ( steveCheckedCopyTransfer
  )
import Phil.Examples.Phase1.SubjectWitnesses
  ( steveCandidateSubject
  )
import Phil.Systems.EvidenceErasure
import Phil.Systems.EvidenceSubjectTransfer
  ( verifyEvidenceTransferStageBundle
  )
import Phil.Systems.Phase1Stage
  ( SourceFactKey (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SYS-012 SYS-011 predecessor remains valid" evidenceTransferRegression
    , test "SYS-012 upload erasure without discharge rejects" uploadMissingDischargeRejected
    , test "SYS-012 Steve erasure without discharge rejects" steveMissingDischargeRejected
    , test "SYS-012 upload exact erasure after discharge accepts" uploadDischargedErasureAccepted
    , test "SYS-012 Steve exact erasure after discharge accepts" steveDischargedErasureAccepted
    , test "SYS-012 later consumer cannot use erased representation" liveConsumerRejected
    , test "SYS-012 successor invariant carries live consequence" successorInvariantAccepted
    , test "SYS-012 later consumer must use exact successor invariant" successorInvariantMismatchRejected
    , test "SYS-012 discharge evidence belongs to exact semantic subject" wrongSubjectEvidenceRejected
    , test "SYS-012 source fact must be evidence for exact semantic subject" wrongSubjectFactRejected
    , test "SYS-012 no-later-consumer basis is explicit" emptyConsumerBasisRejected
    , test "SYS-012 erasure-stage identity is deterministic" deterministicIdentity
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

evidenceTransferRegression :: Either String ()
evidenceTransferRegression = do
  bundle <- steveCheckedCopyTransfer
  mapLeft show (verifyEvidenceTransferStageBundle bundle)

uploadMissingDischargeRejected :: Either String ()
uploadMissingDischargeRejected =
  case verifyEvidenceErasureStageBundle uploadErasureWithoutDischarge of
    Left (ErasureEmptyDischargeEvidence key)
      | key == uploadErasureKey -> Right ()
    other -> Left ("upload erasure without discharge was accepted: " <> show other)

steveMissingDischargeRejected :: Either String ()
steveMissingDischargeRejected = do
  bundle <- steveErasureWithoutDischarge
  case verifyEvidenceErasureStageBundle bundle of
    Left (ErasureEmptyDischargeEvidence key)
      | key == steveErasureKey -> Right ()
    other -> Left ("Steve erasure without discharge was accepted: " <> show other)

uploadDischargedErasureAccepted :: Either String ()
uploadDischargedErasureAccepted =
  mapLeft show (verifyEvidenceErasureStageBundle uploadErasureAfterDischarge)

steveDischargedErasureAccepted :: Either String ()
steveDischargedErasureAccepted = do
  bundle <- steveErasureAfterDischarge
  mapLeft show (verifyEvidenceErasureStageBundle bundle)

liveConsumerRejected :: Either String ()
liveConsumerRejected = do
  original <- steveErasureAfterDischarge
  let consumer = LaterSemanticConsumer
        { laterConsumerKey = SemanticUseKey "steve.install.needs-digest-proof-marker"
        , laterConsumerSubject = steveCandidateSubject
        , laterConsumerSourceFact = SourceFactKey "steve.digest.stable-subject"
        , laterConsumerBasis = ConsumerNeedsErasedRepresentation
        }
      mutated = makeEvidenceErasureStageBundle
        (evidenceErasureStageBase original)
        (evidenceErasureStageJustifications original)
        (Map.singleton (laterConsumerKey consumer) consumer)
  case verifyEvidenceErasureStageBundle mutated of
    Left (ErasureLiveConsumerStillNeedsRepresentation key consumerKey)
      | key == steveErasureKey && consumerKey == laterConsumerKey consumer -> Right ()
    other -> Left ("live erased-representation consumer was accepted: " <> show other)

successorInvariantAccepted :: Either String ()
successorInvariantAccepted = do
  original <- steveErasureAfterDischarge
  let successor = SuccessorInvariantRevision "invariant.steve.digest-established.v1"
      justification = steveErasureJustification
        { erasureSuccessorInvariant = Just successor }
      consumer = LaterSemanticConsumer
        { laterConsumerKey = SemanticUseKey "steve.install.uses-digest-invariant"
        , laterConsumerSubject = steveCandidateSubject
        , laterConsumerSourceFact = SourceFactKey "steve.digest.stable-subject"
        , laterConsumerBasis = ConsumerUsesSuccessorInvariant successor
        }
      mutated = makeEvidenceErasureStageBundle
        (evidenceErasureStageBase original)
        (Map.singleton steveErasureKey justification)
        (Map.singleton (laterConsumerKey consumer) consumer)
  mapLeft show (verifyEvidenceErasureStageBundle mutated)

successorInvariantMismatchRejected :: Either String ()
successorInvariantMismatchRejected = do
  original <- steveErasureAfterDischarge
  let expected = SuccessorInvariantRevision "invariant.steve.digest-established.v1"
      actual = SuccessorInvariantRevision "invariant.steve.digest-something-else.v1"
      justification = steveErasureJustification
        { erasureSuccessorInvariant = Just expected }
      consumer = LaterSemanticConsumer
        { laterConsumerKey = SemanticUseKey "steve.install.uses-wrong-digest-invariant"
        , laterConsumerSubject = steveCandidateSubject
        , laterConsumerSourceFact = SourceFactKey "steve.digest.stable-subject"
        , laterConsumerBasis = ConsumerUsesSuccessorInvariant actual
        }
      mutated = makeEvidenceErasureStageBundle
        (evidenceErasureStageBase original)
        (Map.singleton steveErasureKey justification)
        (Map.singleton (laterConsumerKey consumer) consumer)
  case verifyEvidenceErasureStageBundle mutated of
    Left (ErasureLiveConsumerSuccessorMismatch key consumerKey expected' actual')
      | key == steveErasureKey
          && consumerKey == laterConsumerKey consumer
          && expected' == expected
          && actual' == actual -> Right ()
    other -> Left ("successor-invariant mismatch was accepted: " <> show other)

wrongSubjectEvidenceRejected :: Either String ()
wrongSubjectEvidenceRejected = do
  original <- steveErasureAfterDischarge
  let justification = steveErasureJustification
        { erasureDischargeEvidenceRefs = Set.singleton "steve.provider.admission-lineage" }
      mutated = makeEvidenceErasureStageBundle
        (evidenceErasureStageBase original)
        (Map.singleton steveErasureKey justification)
        Map.empty
  case verifyEvidenceErasureStageBundle mutated of
    Left (ErasureDischargeEvidenceNotForSubject key subject evidenceRef)
      | key == steveErasureKey
          && subject == steveCandidateSubject
          && evidenceRef == "steve.provider.admission-lineage" -> Right ()
    other -> Left ("wrong-subject discharge evidence was accepted: " <> show other)

wrongSubjectFactRejected :: Either String ()
wrongSubjectFactRejected = do
  original <- steveErasureAfterDischarge
  let justification = steveErasureJustification
        { erasureSourceFact = SourceFactKey "steve.provider.admission-lineage" }
      mutated = makeEvidenceErasureStageBundle
        (evidenceErasureStageBase original)
        (Map.singleton steveErasureKey justification)
        Map.empty
  case verifyEvidenceErasureStageBundle mutated of
    Left (ErasureSourceFactNotEvidenceForSubject key subject fact)
      | key == steveErasureKey
          && subject == steveCandidateSubject
          && fact == SourceFactKey "steve.provider.admission-lineage" -> Right ()
    other -> Left ("wrong-subject source fact was accepted: " <> show other)

emptyConsumerBasisRejected :: Either String ()
emptyConsumerBasisRejected = do
  original <- steveErasureAfterDischarge
  let justification = steveErasureJustification
        { erasureNoLaterConsumerBasis = NoLaterConsumerRevision "" }
      mutated = makeEvidenceErasureStageBundle
        (evidenceErasureStageBase original)
        (Map.singleton steveErasureKey justification)
        Map.empty
  case verifyEvidenceErasureStageBundle mutated of
    Left (ErasureEmptyNoLaterConsumerBasis key)
      | key == steveErasureKey -> Right ()
    other -> Left ("empty no-later-consumer basis was accepted: " <> show other)

deterministicIdentity :: Either String ()
deterministicIdentity = do
  original <- steveErasureAfterDischarge
  let secondKey = ErasureJustificationKey "steve.blob.borrow-proof.erasure"
      secondJustification = steveErasureJustification
        { erasureJustificationKey = secondKey
        , erasureSourceFact = SourceFactKey "steve.blob.borrow-preservation"
        , erasureRepresentation = ErasedRepresentationKey
            "steve.blob.borrow-preservation-proof-marker"
        , erasureDischargeEvidenceRefs = Set.fromList
            [ "steve.blob.borrow-preservation"
            , "steve.digest.stable-subject"
            ]
        , erasureLastSemanticUse = SemanticUseKey
            "steve.put.install-borrow-semantic-use"
        , erasureNoLaterConsumerBasis = NoLaterConsumerRevision
            "consumer-closure.steve.blob.borrow-preservation.v1"
        }
      justifications = Map.fromList
        [ (steveErasureKey, steveErasureJustification)
        , (secondKey, secondJustification)
        ]
      forward = makeEvidenceErasureStageBundle
        (evidenceErasureStageBase original)
        justifications
        Map.empty
      reverseOrder = makeEvidenceErasureStageBundle
        (evidenceErasureStageBase original)
        (Map.fromList (reverse (Map.toAscList justifications)))
        Map.empty
  assert (evidenceErasureStageRevision forward == evidenceErasureStageRevision reverseOrder)
    "evidence-erasure revision changed with map enumeration order"
  mapLeft show (verifyEvidenceErasureStageBundle reverseOrder)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
