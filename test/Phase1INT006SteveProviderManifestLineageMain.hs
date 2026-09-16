{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text.IO as TextIO
import Phil.Assurance.Types
import Phil.Assurance.Verify
  ( ManifestError (..)
  , verifyManifest
  )
import Phil.Core.ProviderQualificationIdentity
import Phil.Examples.Steve.ProviderQualifications
import Phil.Test.Phase1.ManifestWitnesses
import System.Exit (exitFailure)

main :: IO ()
main = do
  putSource <- TextIO.readFile "examples/steve/put.phil"
  getSource <- TextIO.readFile "examples/steve/get.phil"
  let prepared = do
        fixture <- steveRealManifestFixture putSource getSource
        qualifications <- mapLeft show materializeSteveProviderQualifications
        pure (fixture, qualifications)
  results <- sequence
    [ test "AssuranceManifest carries exact Steve provider claim/evidence/admission lineage"
        (prepared >>= exactManifestLineage)
    , test "selected provider evidence binds the exact admitted lineage"
        (prepared >>= exactEvidenceLineage)
    , test "self-consistent stale BlobProvider manifest lineage fails closed"
        (prepared >>= staleBlobLineageFailsClosed)
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: INT-006 " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: INT-006 " <> label <> " -- " <> detail) >> pure False

exactManifestLineage
  :: (RealManifestFixture, SteveProviderQualifications)
  -> Either String ()
exactManifestLineage (fixture, qualifications) = do
  let manifest = realFixtureManifest fixture
      digestArtifact = steveDigestProviderQualification qualifications
      blobArtifact = steveBlobProviderQualification qualifications
      expected = Map.unions
        [ Map.singleton "witness" "Steve"
        , providerLineage "digest" digestArtifact
        , providerLineage "blob" blobArtifact
        ]
  assert
    (manifestValidityContext manifest == expected)
    "manifest validity context does not exactly name both admitted provider lineages"

exactEvidenceLineage
  :: (RealManifestFixture, SteveProviderQualifications)
  -> Either String ()
exactEvidenceLineage (fixture, qualifications) = do
  let manifest = realFixtureManifest fixture
      ledger = realFixtureLedger fixture
      artifacts =
        [ steveDigestProviderQualification qualifications
        , steveBlobProviderQualification qualifications
        ]
      expectedEvidence = Set.unions (map providerEvidenceIds artifacts)
  assert
    (manifestEvidenceEntries manifest == expectedEvidence)
    "manifest selected evidence differs from exact Steve provider obligation evidence"
  mapM_ (checkArtifactEvidence ledger) artifacts

staleBlobLineageFailsClosed
  :: (RealManifestFixture, SteveProviderQualifications)
  -> Either String ()
staleBlobLineageFailsClosed (fixture, _) = do
  let ledger = realFixtureLedger fixture
      manifest = realFixtureManifest fixture
      staleValidity = Map.insert
        "blob.admission"
        "phil.provider-qualification.admission.canonical.v1:stale"
        (manifestValidityContext manifest)
      provisional = manifest
        { manifestId = Digest ""
        , manifestValidityContext = staleValidity
        }
      resealed = provisional
        { manifestId = deriveManifestId ledger provisional }
  case verifyManifest (realFixtureContext fixture) ledger resealed of
    Left ValidityContextMismatch -> Right ()
    other -> Left ("stale provider lineage did not fail closed: " <> show other)

providerLineage
  :: Text
  -> SteveProviderQualificationArtifact
  -> Map.Map Text Text
providerLineage prefix artifact = Map.fromList
  [ (prefix <> ".claim",
      unQualificationClaimRevision
        (checkedQualificationAdmissionClaimRevision admission))
  , (prefix <> ".evidence",
      unQualificationEvidenceRevision
        (checkedQualificationAdmissionEvidenceRevision admission))
  , (prefix <> ".admission",
      unQualificationAdmissionRevision
        (checkedQualificationAdmissionRevision admission))
  ]
  where
    admission = steveProviderCheckedAdmission artifact

providerEvidenceIds
  :: SteveProviderQualificationArtifact
  -> Set.Set EvidenceEntryId
providerEvidenceIds artifact = Set.map evidenceId
  (steveProviderRequiredObligationKeys artifact)
  where
    occurrence = checkedQualificationAdmissionProviderOccurrence
      (steveProviderCheckedAdmission artifact)
    evidenceId key = EvidenceEntryId
      ("evidence:" <> occurrence <> ":" <> key)

checkArtifactEvidence
  :: AssuranceLedger
  -> SteveProviderQualificationArtifact
  -> Either String ()
checkArtifactEvidence ledger artifact =
  mapM_ checkKey (Set.toAscList (steveProviderRequiredObligationKeys artifact))
  where
    admission = steveProviderCheckedAdmission artifact
    occurrence = checkedQualificationAdmissionProviderOccurrence admission
    expectedInputs = map digestText
      [ unQualificationClaimRevision
          (checkedQualificationAdmissionClaimRevision admission)
      , unQualificationEvidenceRevision
          (checkedQualificationAdmissionEvidenceRevision admission)
      , unQualificationAdmissionRevision
          (checkedQualificationAdmissionRevision admission)
      ]
    checkKey key = do
      let entryId = EvidenceEntryId ("evidence:" <> occurrence <> ":" <> key)
      entry <- maybe
        (Left ("missing provider evidence entry: " <> show entryId))
        Right
        (Map.lookup entryId (ledgerEvidence ledger))
      assert
        (evidenceInputDigests entry == expectedInputs)
        ("provider evidence entry is not bound to exact admitted lineage: " <> show entryId)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
