{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Handoff.Phase1CheckedArchitecture
import Phil.Handoff.Phase1WitnessSourceBundle
import Phil.Surface.Lineage (PortableSourceBundle)
import Phil.Test.Phase1.ManifestWitnesses
  ( checkedSteveArchitectureFromBundle
  , checkedUploadArchitectureFromBundle
  )
import System.Exit (exitFailure)

uploadBundlePath, steveBundlePath :: FilePath
uploadBundlePath = "handoff/phase1/witnesses/upload-source-bundle-v1.tsv"
steveBundlePath = "handoff/phase1/witnesses/steve-source-bundle-v1.tsv"

uploadSummaryPath, steveSummaryPath :: FilePath
uploadSummaryPath = "handoff/phase1/witnesses/upload-checked-architecture-v1.tsv"
steveSummaryPath = "handoff/phase1/witnesses/steve-checked-architecture-v1.tsv"

main :: IO ()
main = do
  uploadBundle <- loadBundle uploadBundlePath
  steveBundle <- loadBundle steveBundlePath

  uploadResult <- checkWitness
    "Upload"
    uploadSummaryPath
    (checkedUploadArchitectureFromBundle uploadBundle)
  steveResult <- checkWitness
    "Steve"
    steveSummaryPath
    (checkedSteveArchitectureFromBundle steveBundle)

  negativeResults <- sequence
    [ test "INT-007 checked-architecture malformed digest fails closed"
        malformedDigestRejects
    , test "INT-007 checked-architecture duplicate declaration fails closed"
        duplicateDeclarationRejects
    , test "INT-007 checked-architecture root declaration must be enumerated"
        missingRootDeclarationRejects
    ]

  if uploadResult && steveResult && and negativeResults
    then pure ()
    else exitFailure

loadBundle :: FilePath -> IO PortableSourceBundle
loadBundle path = do
  source <- TextIO.readFile path
  descriptor <- case decodePhase1WitnessSourceBundleDescriptor source of
    Left errorValue -> do
      putStrLn ("FAIL: decode " <> path <> " -- " <> show errorValue)
      exitFailure
    Right value -> pure value
  result <- materializePhase1WitnessSourceBundle "." descriptor
  case result of
    Left errorValue -> do
      putStrLn ("FAIL: materialize " <> path <> " -- " <> show errorValue)
      exitFailure
    Right value -> pure value

checkWitness
  :: String
  -> FilePath
  -> Either String a
  -> IO Bool
checkWitness label summaryPath architectureResult =
  case architectureResult of
    Left detail -> do
      putStrLn ("FAIL: INT-007 " <> label <> " ordinary checked architecture -- " <> detail)
      pure False
    Right architecture -> do
      expectedSource <- TextIO.readFile summaryPath
      case decodePhase1CheckedArchitectureSummary expectedSource of
        Left errorValue -> do
          putStrLn ("FAIL: INT-007 " <> label <> " summary decode -- " <> show errorValue)
          pure False
        Right expected -> do
          let actual = derivePhase1CheckedArchitectureSummary architecture
          if actual == expected
            then do
              putStrLn ("PASS: INT-007 " <> label
                <> " checked semantics and ArchitectureInstance reconstruct exactly")
              pure True
            else do
              putStrLn ("FAIL: INT-007 " <> label <> " checked architecture summary drift")
              putStrLn ("ACTUAL " <> label <> " SUMMARY BEGIN")
              TextIO.putStr (renderPhase1CheckedArchitectureSummary actual)
              putStrLn ("ACTUAL " <> label <> " SUMMARY END")
              pure False

malformedDigestRejects :: Either String ()
malformedDigestRejects =
  expectError isMalformed $ Text.unlines
    [ phase1CheckedArchitectureFormatV1
    , "root\tprogram:test\tdecl:test"
    , "declaration\tdecl:test\tsha256:ABC\t" <> zeroDigest
        <> "\t" <> zeroDigest <> "\t" <> zeroDigest
    , "instance\tinst:test\t" <> zeroDigest
    ]
  where
    isMalformed CheckedArchitectureSummaryMalformedDigest {} = True
    isMalformed _ = False

duplicateDeclarationRejects :: Either String ()
duplicateDeclarationRejects =
  expectError isDuplicate $ Text.unlines
    [ phase1CheckedArchitectureFormatV1
    , "root\tprogram:test\tdecl:test"
    , declarationLine "decl:test"
    , declarationLine "decl:test"
    , "instance\tinst:test\t" <> zeroDigest
    ]
  where
    isDuplicate CheckedArchitectureSummaryDuplicateDeclaration {} = True
    isDuplicate _ = False

missingRootDeclarationRejects :: Either String ()
missingRootDeclarationRejects =
  expectError isMissing $ Text.unlines
    [ phase1CheckedArchitectureFormatV1
    , "root\tprogram:test\tdecl:missing"
    , declarationLine "decl:other"
    , "instance\tinst:test\t" <> zeroDigest
    ]
  where
    isMissing CheckedArchitectureSummaryRootDeclarationMissing {} = True
    isMissing _ = False

declarationLine :: Text -> Text
declarationLine key = Text.intercalate "\t"
  [ "declaration", key, zeroDigest, zeroDigest, zeroDigest, zeroDigest ]

expectError
  :: (Phase1CheckedArchitectureSummaryError -> Bool)
  -> Text
  -> Either String ()
expectError predicate source =
  case decodePhase1CheckedArchitectureSummary source of
    Left errorValue
      | predicate errorValue -> Right ()
      | otherwise -> Left ("unexpected summary rejection: " <> show errorValue)
    Right value -> Left ("expected summary rejection, decoded: " <> show value)

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

zeroDigest :: Text
zeroDigest = "sha256:" <> Text.replicate 64 "0"
