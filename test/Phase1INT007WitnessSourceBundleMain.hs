{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Core.Static (DeclarationKey (..), InstanceKey (..))
import Phil.Handoff.Phase1WitnessSourceBundle
import Phil.Surface.Lineage
import System.Exit (exitFailure)

uploadDescriptorPath, steveDescriptorPath :: FilePath
uploadDescriptorPath = "handoff/phase1/witnesses/upload-source-bundle-v1.tsv"
steveDescriptorPath = "handoff/phase1/witnesses/steve-source-bundle-v1.tsv"

main :: IO ()
main = do
  upload <- loadBundle uploadDescriptorPath
  steve <- loadBundle steveDescriptorPath
  results <- sequence
    [ test "INT-007 Upload handoff reconstructs exact persisted source lineage"
        (checkUpload upload)
    , test "INT-007 Steve handoff reconstructs exact persisted source lineage"
        (checkSteve steve)
    , testIO "INT-007 source digest drift fails before reconstruction"
        sourceDigestDriftRejects
    , test "INT-007 source traversal path fails closed"
        traversalPathRejects
    , test "INT-007 incompatible grammar revision fails closed"
        incompatibleGrammarRejects
    , test "INT-007 duplicate source-unit identity fails closed"
        duplicateUnitRejects
    ]
  if and results then pure () else exitFailure

loadBundle :: FilePath -> IO PortableSourceBundle
loadBundle path = do
  descriptorSource <- TextIO.readFile path
  descriptor <- case decodePhase1WitnessSourceBundleDescriptor descriptorSource of
    Left errorValue ->
      putStrLn ("FAIL: INT-007 descriptor " <> path <> " -- " <> show errorValue)
        >> exitFailure
    Right value -> pure value
  materialized <- materializePhase1WitnessSourceBundle "." descriptor
  case materialized of
    Left errorValue ->
      putStrLn ("FAIL: INT-007 source materialization " <> path <> " -- " <> show errorValue)
        >> exitFailure
    Right value -> pure value

checkUpload :: PortableSourceBundle -> Either String ()
checkUpload bundle = do
  assert (portableGrammarRevision bundle == canonicalGrammarRevisionV1)
    "Upload grammar revision drifted"
  assert (portableSelectedProgramRoot bundle == "program:upload")
    "Upload selected root drifted"
  assert (length (portableSourceUnits bundle) == 2)
    "Upload did not reconstruct exactly two source units"
  resolved <- mapLeft show (resolveSourceBundleLineage bundle)
  expectDeclaration "site.upload.client" "decl:upload.client" resolved
  expectDeclaration "site.upload.server" "decl:upload.server" resolved
  expectInstance "instance.upload" "inst:phase1.upload" resolved
  assert (Map.null (resolvedProcessKeys resolved))
    "Upload handoff invented process lineage"

checkSteve :: PortableSourceBundle -> Either String ()
checkSteve bundle = do
  assert (portableGrammarRevision bundle == canonicalGrammarRevisionV1)
    "Steve grammar revision drifted"
  assert (portableSelectedProgramRoot bundle == "program:steve")
    "Steve selected root drifted"
  assert (length (portableSourceUnits bundle) == 2)
    "Steve did not reconstruct exactly two source units"
  resolved <- mapLeft show (resolveSourceBundleLineage bundle)
  expectDeclaration "site.steve.put" "decl:steve.put" resolved
  expectDeclaration "site.steve.get" "decl:steve.get" resolved
  expectInstance "instance.steve" "inst:phase1.steve" resolved
  assert (Map.null (resolvedProcessKeys resolved))
    "Steve handoff invented process lineage"

expectDeclaration
  :: Text
  -> Text
  -> ResolvedSourceBundleLineage
  -> Either String ()
expectDeclaration site expected resolved =
  assert
    (Map.lookup (DeclarationSiteId site) (resolvedDeclarationKeys resolved)
      == Just (DeclarationKey expected))
    ("declaration lineage mismatch at " <> Text.unpack site)

expectInstance
  :: Text
  -> Text
  -> ResolvedSourceBundleLineage
  -> Either String ()
expectInstance site expected resolved =
  assert
    (Map.lookup (InstanceLineageSiteId site) (resolvedInstanceKeys resolved)
      == Just (InstanceKey expected))
    ("instance lineage mismatch at " <> Text.unpack site)

sourceDigestDriftRejects :: IO (Either String ())
sourceDigestDriftRejects = do
  descriptor <- case decodePhase1WitnessSourceBundleDescriptor $ descriptorText
      [ "grammar\t" <> unGrammarRevision canonicalGrammarRevisionV1
      , "root\tprogram:test"
      , Text.intercalate "\t"
          [ "unit"
          , "unit.test"
          , "site.test"
          , "decl:test"
          , "examples/steve/put.phil"
          , zeroDigest
          ]
      ] of
    Left errorValue -> pure (Left ("unexpected descriptor rejection: " <> show errorValue))
    Right value -> pure (Right value)
  case descriptor of
    Left detail -> pure (Left detail)
    Right value -> do
      result <- materializePhase1WitnessSourceBundle "." value
      pure $ case result of
        Left WitnessSourceBundleSourceDigestMismatch {} -> Right ()
        other -> Left ("digest drift did not reject exactly: " <> show other)

traversalPathRejects :: Either String ()
traversalPathRejects =
  expectDecodeError isTraversal $ descriptorText
    [ "grammar\t" <> unGrammarRevision canonicalGrammarRevisionV1
    , "root\tprogram:test"
    , Text.intercalate "\t"
        [ "unit", "unit.test", "site.test", "decl:test", "../put.phil", zeroDigest ]
    ]
  where
    isTraversal WitnessSourceBundleMalformedPath {} = True
    isTraversal _ = False

incompatibleGrammarRejects :: Either String ()
incompatibleGrammarRejects =
  expectDecodeError isIncompatible $ descriptorText
    [ "grammar\tsha256:" <> Text.replicate 64 "0"
    , "root\tprogram:test"
    , Text.intercalate "\t"
        [ "unit", "unit.test", "site.test", "decl:test"
        , "examples/steve/put.phil", zeroDigest
        ]
    ]
  where
    isIncompatible WitnessSourceBundleIncompatibleGrammar {} = True
    isIncompatible _ = False

duplicateUnitRejects :: Either String ()
duplicateUnitRejects =
  expectDecodeError isDuplicate $ descriptorText
    [ "grammar\t" <> unGrammarRevision canonicalGrammarRevisionV1
    , "root\tprogram:test"
    , Text.intercalate "\t"
        [ "unit", "unit.same", "site.one", "decl:one"
        , "examples/steve/put.phil", zeroDigest
        ]
    , Text.intercalate "\t"
        [ "unit", "unit.same", "site.two", "decl:two"
        , "examples/steve/get.phil", zeroDigest
        ]
    ]
  where
    isDuplicate WitnessSourceBundleDuplicateUnit {} = True
    isDuplicate _ = False

expectDecodeError
  :: (Phase1WitnessSourceBundleError -> Bool)
  -> Text
  -> Either String ()
expectDecodeError predicate source =
  case decodePhase1WitnessSourceBundleDescriptor source of
    Left errorValue
      | predicate errorValue -> Right ()
      | otherwise -> Left ("unexpected descriptor rejection: " <> show errorValue)
    Right value -> Left ("expected descriptor rejection, decoded: " <> show value)

descriptorText :: [Text] -> Text
descriptorText records =
  Text.unlines (phase1WitnessSourceBundleFormatV1 : records)

zeroDigest :: Text
zeroDigest = "sha256:" <> Text.replicate 64 "0"

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

testIO :: String -> IO (Either String ()) -> IO Bool
testIO label action = action >>= test label

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
