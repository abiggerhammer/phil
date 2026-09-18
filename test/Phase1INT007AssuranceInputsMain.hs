{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Set as Set
import qualified Data.Text.IO as TextIO
import Phil.Assurance.Types
import Phil.Handoff.Phase1AssuranceInputs
import Phil.Handoff.Phase1WitnessSourceBundle
import Phil.Surface.Lineage (PortableSourceBundle)
import Phil.Test.Phase1.ManifestWitnesses
  ( AssuranceInputFixture (..)
  , steveAssuranceInputFixture
  , steveVerificationBundleFromBundle
  , uploadAssuranceInputFixture
  , uploadVerificationBundleFromBundle
  )
import Phil.Verification
  ( ApplicationAssurancePolicy (..)
  , AssurancePolicyRevision (..)
  , VerificationDisposition (..)
  )
import Phil.Verification.ManifestClosure (ManifestClosureSelection (..))
import Phil.Verification.Bundle
  ( AcceptedEvidenceReference (..)
  , VerificationBundle (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  uploadBundle <- loadSourceBundle
    "handoff/phase1/witnesses/upload-source-bundle-v1.tsv"
  steveBundle <- loadSourceBundle
    "handoff/phase1/witnesses/steve-source-bundle-v1.tsv"

  uploadResult <- checkWitness
    "Upload"
    "handoff/phase1/witnesses/upload-assurance-inputs-v1.tsv"
    uploadAssuranceInputFixture
    (uploadVerificationBundleFromBundle uploadBundle)
  steveResult <- checkWitness
    "Steve"
    "handoff/phase1/witnesses/steve-assurance-inputs-v1.tsv"
    steveAssuranceInputFixture
    (steveVerificationBundleFromBundle steveBundle)

  negativeResults <- sequence
    [ test "INT-007 assurance-input evidence digest drift fails closed"
        evidenceDigestDriftRejects
    , test "INT-007 assurance-input required disposition must be permitted"
        unpermittedDispositionRejects
    , test "INT-007 assurance-input malformed hex fails closed"
        malformedHexRejects
    ]

  if uploadResult && steveResult && and negativeResults
    then pure ()
    else exitFailure

loadSourceBundle :: FilePath -> IO PortableSourceBundle
loadSourceBundle path = do
  source <- TextIO.readFile path
  descriptor <- case decodePhase1WitnessSourceBundleDescriptor source of
    Left errorValue -> do
      putStrLn ("FAIL: decode " <> path <> " -- " <> show errorValue)
      exitFailure
    Right value -> pure value
  materialized <- materializePhase1WitnessSourceBundle "." descriptor
  case materialized of
    Left errorValue -> do
      putStrLn ("FAIL: materialize " <> path <> " -- " <> show errorValue)
      exitFailure
    Right value -> pure value

checkWitness
  :: String
  -> FilePath
  -> Either String AssuranceInputFixture
  -> Either String VerificationBundle
  -> IO Bool
checkWitness label summaryPath fixtureResult bundleResult =
  case (fixtureResult, bundleResult) of
    (Left detail, _) -> failWith ("fixture -- " <> detail)
    (_, Left detail) -> failWith ("VerificationBundle -- " <> detail)
    (Right fixture, Right bundle) -> do
      expectedSource <- TextIO.readFile summaryPath
      case decodePhase1AssuranceInputs expectedSource of
        Left errorValue -> failWith ("summary decode -- " <> show errorValue)
        Right expected ->
          case derivePhase1AssuranceInputs
              (assuranceInputFixturePolicy fixture)
              (assuranceInputFixtureLedger fixture)
              (assuranceInputFixtureSelection fixture) of
            Left errorValue -> failWith ("summary derivation -- " <> show errorValue)
            Right actual
              | applicationAssurancePolicyRevision
                    (phase1AssurancePolicy actual)
                    /= verificationBundlePolicyRevision bundle ->
                  failWith "policy revision does not match VerificationBundle"
              | not (bundleEvidenceMatches actual bundle) ->
                  failWith "selected evidence does not exactly match VerificationBundle references"
              | actual /= expected -> do
                  putStrLn ("FAIL: INT-007 " <> label <> " assurance-input summary drift")
                  putStrLn ("ACTUAL " <> label <> " ASSURANCE INPUTS BEGIN")
                  TextIO.putStr (renderPhase1AssuranceInputs actual)
                  putStrLn ("ACTUAL " <> label <> " ASSURANCE INPUTS END")
                  pure False
              | otherwise -> do
                  putStrLn ("PASS: INT-007 " <> label
                    <> " accepted assurance inputs reconstruct exactly")
                  pure True
  where
    failWith detail = do
      putStrLn ("FAIL: INT-007 " <> label <> " " <> detail)
      pure False

bundleEvidenceMatches :: Phase1AssuranceInputs -> VerificationBundle -> Bool
bundleEvidenceMatches inputs bundle =
  Map.keysSet evidence == Map.keysSet references
    && all matches (Map.toAscList references)
  where
    evidence = ledgerEvidence (phase1AssuranceLedger inputs)
    references = verificationBundleAcceptedEvidence bundle
    matches (entryId, reference) = case Map.lookup entryId evidence of
      Nothing -> False
      Just entry ->
        acceptedEvidenceEntryId reference == evidenceEntryId entry
          && acceptedEvidenceDigest reference == evidenceEntryDigest entry
          && acceptedEvidenceObligationRevision reference
              == evidenceObligationRevision entry

evidenceDigestDriftRejects :: Either String ()
evidenceDigestDriftRejects =
  expectDecodeFailure
    (Text.replace validDigestToken zeroDigestToken validSampleFile)

unpermittedDispositionRejects :: Either String ()
unpermittedDispositionRejects =
  expectDecodeFailure
    (Text.replace "permit\tstatic\n" "" validSampleFile)

malformedHexRejects :: Either String ()
malformedHexRejects =
  expectDecodeFailure $ Text.unlines
    [ phase1AssuranceInputsFormatV1
    , "policy\tzz"
    ]

validSampleFile :: Text.Text
validSampleFile =
  case derivePhase1AssuranceInputs samplePolicy sampleLedger sampleSelection of
    Left errorValue -> error ("invalid assurance-input test fixture: " <> show errorValue)
    Right value -> renderPhase1AssuranceInputs value

samplePolicy :: ApplicationAssurancePolicy
samplePolicy = ApplicationAssurancePolicy
  { applicationAssurancePolicyRevision = AssurancePolicyRevision "policy.test"
  , applicationAssurancePolicyPermittedDispositions =
      Set.singleton StaticallyDischarged
  }

sampleLedger :: AssuranceLedger
sampleLedger = emptyLedger
  { ledgerEvidence = Map.singleton sampleEvidenceId sampleEvidence
  }

sampleSelection :: ManifestClosureSelection
sampleSelection = ManifestClosureSelection
  { manifestClosureEvidence = Set.singleton sampleEvidenceId
  , manifestClosureAssumptions = Set.empty
  , manifestClosureExports = Map.empty
  , manifestClosureUses = Set.empty
  }

sampleEvidenceId :: EvidenceEntryId
sampleEvidenceId = EvidenceEntryId "evidence.test"

sampleEvidence :: EvidenceEntry
sampleEvidence = provisional
  { evidenceEntryDigest = deriveEvidenceEntryDigest provisional }
  where
    provisional = EvidenceEntry
      { evidenceEntryId = sampleEvidenceId
      , evidenceEntryDigest = Digest ""
      , evidenceObligationRevision = RevisionId "rev.test"
      , evidenceAssuranceKind = KernelChecked
      , evidenceRole = EvidenceRole "establishes"
      , evidenceProducer = "producer"
      , evidenceChecker = "checker"
      , evidenceArtifact = Nothing
      , evidenceInputDigests = []
      , evidenceAssumptions = []
      , evidenceDependsOn = []
      , evidenceValidityScope = ValidityScope Map.empty
      , evidenceResult = EvidenceAccepted
      , evidenceJustifies = []
      , evidenceRuntimeMechanism = Nothing
      , evidenceRuntimeResidue = []
      , evidenceCostRefs = []
      }

validDigestToken :: Text.Text
validDigestToken = "sha256:" <> unDigest (evidenceEntryDigest sampleEvidence)

zeroDigestToken :: Text.Text
zeroDigestToken = "sha256:" <> Text.replicate 64 "0"

expectDecodeFailure :: Text.Text -> Either String ()
expectDecodeFailure source = case decodePhase1AssuranceInputs source of
  Left _ -> Right ()
  Right value -> Left ("expected assurance-input rejection, decoded: " <> show value)

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False
