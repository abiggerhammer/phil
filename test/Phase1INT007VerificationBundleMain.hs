{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Handoff.Phase1VerificationBundle
import Phil.Handoff.Phase1WitnessSourceBundle
import Phil.Surface.Lineage (PortableSourceBundle)
import Phil.Test.Phase1.ManifestWitnesses
  ( steveVerificationBundleFromBundle
  , uploadVerificationBundleFromBundle
  )
import Phil.Verification.Bundle (VerificationBundle)
import System.Exit (exitFailure)

uploadBundlePath, steveBundlePath :: FilePath
uploadBundlePath = "handoff/phase1/witnesses/upload-source-bundle-v1.tsv"
steveBundlePath = "handoff/phase1/witnesses/steve-source-bundle-v1.tsv"

uploadSummaryPath, steveSummaryPath :: FilePath
uploadSummaryPath = "handoff/phase1/witnesses/upload-verification-bundle-v1.tsv"
steveSummaryPath = "handoff/phase1/witnesses/steve-verification-bundle-v1.tsv"

main :: IO ()
main = do
  uploadSourceBundle <- loadSourceBundle uploadBundlePath
  steveSourceBundle <- loadSourceBundle steveBundlePath

  uploadResult <- checkWitness
    "Upload"
    uploadSummaryPath
    (uploadVerificationBundleFromBundle uploadSourceBundle)
  steveResult <- checkWitness
    "Steve"
    steveSummaryPath
    (steveVerificationBundleFromBundle steveSourceBundle)

  negativeResults <- sequence
    [ test "INT-007 verification summary malformed digest fails closed"
        malformedDigestRejects
    , test "INT-007 verification summary duplicate node fails closed"
        duplicateNodeRejects
    , test "INT-007 verification summary edge endpoint must be enumerated"
        unknownEdgeRejects
    , test "INT-007 verification summary evidence target must be enumerated"
        unknownEvidenceTargetRejects
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
  -> Either String VerificationBundle
  -> IO Bool
checkWitness label summaryPath bundleResult =
  case bundleResult of
    Left detail -> do
      putStrLn ("FAIL: INT-007 " <> label <> " VerificationBundle -- " <> detail)
      pure False
    Right bundle -> do
      expectedSource <- TextIO.readFile summaryPath
      case decodePhase1VerificationBundleSummary expectedSource of
        Left errorValue -> do
          putStrLn ("FAIL: INT-007 " <> label <> " summary decode -- " <> show errorValue)
          pure False
        Right expected -> do
          let actual = derivePhase1VerificationBundleSummary bundle
          if actual == expected
            then do
              putStrLn ("PASS: INT-007 " <> label
                <> " VerificationBundle and obligation graph reconstruct exactly")
              pure True
            else do
              putStrLn ("FAIL: INT-007 " <> label <> " verification summary drift")
              putStrLn ("ACTUAL " <> label <> " VERIFICATION SUMMARY BEGIN")
              TextIO.putStr (renderPhase1VerificationBundleSummary actual)
              putStrLn ("ACTUAL " <> label <> " VERIFICATION SUMMARY END")
              pure False

malformedDigestRejects :: Either String ()
malformedDigestRejects =
  expectError isMalformed $ Text.unlines
    [ phase1VerificationBundleFormatV1
    , Text.intercalate "\t"
        [ "bundle"
        , "sha256:ABC"
        , zeroDigest
        , zeroDigest
        , zeroDigest
        , "policy:test"
        , "accepted"
        ]
    ]
  where
    isMalformed VerificationSummaryMalformedDigest {} = True
    isMalformed _ = False

duplicateNodeRejects :: Either String ()
duplicateNodeRejects =
  expectError isDuplicate $ Text.unlines
    [ phase1VerificationBundleFormatV1
    , bundleLine
    , nodeLine "rev.same"
    , nodeLine "rev.same"
    ]
  where
    isDuplicate VerificationSummaryDuplicateNode {} = True
    isDuplicate _ = False

unknownEdgeRejects :: Either String ()
unknownEdgeRejects =
  expectError isUnknown $ Text.unlines
    [ phase1VerificationBundleFormatV1
    , bundleLine
    , nodeLine "rev.known"
    , "edge\trev.known\trev.missing"
    ]
  where
    isUnknown (VerificationSummaryUnknownEdgeEndpoint revision) =
      revision == revisionId "rev.missing"
    isUnknown _ = False

unknownEvidenceTargetRejects :: Either String ()
unknownEvidenceTargetRejects =
  expectError isUnknown $ Text.unlines
    [ phase1VerificationBundleFormatV1
    , bundleLine
    , nodeLine "rev.known"
    , Text.intercalate "\t"
        [ "evidence", "evidence.test", zeroDigest, "rev.missing" ]
    ]
  where
    isUnknown (VerificationSummaryUnknownEvidenceRevision revision) =
      revision == revisionId "rev.missing"
    isUnknown _ = False

revisionId :: Text -> Phil.Assurance.Types.RevisionId
revisionId = Phil.Assurance.Types.RevisionId

bundleLine :: Text
bundleLine = Text.intercalate "\t"
  [ "bundle"
  , zeroDigest
  , zeroDigest
  , zeroDigest
  , zeroDigest
  , "policy:test"
  , "accepted"
  ]

nodeLine :: Text -> Text
nodeLine revision =
  Text.intercalate "\t" ["node", revision, zeroDigest]

expectError
  :: (Phase1VerificationBundleSummaryError -> Bool)
  -> Text
  -> Either String ()
expectError predicate source =
  case decodePhase1VerificationBundleSummary source of
    Left errorValue
      | predicate errorValue -> Right ()
      | otherwise -> Left ("unexpected verification summary rejection: " <> show errorValue)
    Right value -> Left ("expected verification summary rejection, decoded: " <> show value)

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

zeroDigest :: Text
zeroDigest = "sha256:" <> Text.replicate 64 "0"
