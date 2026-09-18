{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
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
  )
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
  expectDecodeFailure $ sampleEvidenceFile
    "sha256:0000000000000000000000000000000000000000000000000000000000000000"
    ["static"]

unpermittedDispositionRejects :: Either String ()
unpermittedDispositionRejects =
  expectDecodeFailure $ sampleEvidenceFile validEvidenceDigest []

malformedHexRejects :: Either String ()
malformedHexRejects =
  expectDecodeFailure $ TextIOErrorPlaceholder

sampleEvidenceFile :: String -> [String] -> Text.Text
sampleEvidenceFile digest permits = Text.unlines $
  [ phase1AssuranceInputsFormatV1
  , "policy\t706f6c6963792e74657374"
  ]
  <> map (Text.pack . ("permit\t" <>)) permits
  <> [ "require\tstatic"
     , Text.intercalate "\t"
        [ "evidence"
        , "65766964656e63652e74657374"
        , Text.pack digest
        , "7265762e74657374"
        , "kernel"
        , "65737461626c6973686573"
        , "70726f6475636572"
        , "636865636b6572"
        ]
     ]

validEvidenceDigest :: String
validEvidenceDigest =
  "sha256:4e0911b54b7246253e09e6633cf4baf81410315c49d286118fd9a39498d6bd07"

expectDecodeFailure :: Text.Text -> Either String ()
expectDecodeFailure source = case decodePhase1AssuranceInputs source of
  Left _ -> Right ()
  Right value -> Left ("expected assurance-input rejection, decoded: " <> show value)

TextIOErrorPlaceholder :: Text.Text
TextIOErrorPlaceholder = Text.unlines
  [ phase1AssuranceInputsFormatV1
  , "policy\tzz"
  ]

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False
