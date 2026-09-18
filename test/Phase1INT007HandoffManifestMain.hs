{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Text as Text
import Data.Text (Text)
import qualified Data.Text.IO as TextIO
import Phil.Handoff.Phase1Manifest
import System.Exit (exitFailure)

manifestPath :: FilePath
manifestPath = "handoff/phase1/manifest-v1.tsv"

main :: IO ()
main = do
  source <- TextIO.readFile manifestPath
  manifest <- case decodePhase1HandoffManifest source of
    Left errorValue -> do
      putStrLn ("FAIL: INT-007 handoff manifest parse -- " <> show errorValue)
      exitFailure
    Right value -> pure value

  pureResults <- sequence
    [ test "INT-007 manifest spine has the exact admitted current inventory"
        (spineCoverage manifest)
    , test "INT-007 duplicate artifact identity rejects"
        duplicateArtifactIdRejects
    , test "INT-007 duplicate repository path rejects"
        duplicatePathRejects
    , test "INT-007 traversal path rejects"
        traversalPathRejects
    , test "INT-007 malformed digest rejects"
        malformedDigestRejects
    , test "INT-007 unknown artifact kind rejects"
        unknownKindRejects
    , test "INT-007 duplicate governing authority rejects"
        duplicateAuthorityRejects
    ]

  fileErrors <- checkPhase1HandoffManifestFiles "." manifest
  fileResult <- case fileErrors of
    [] -> do
      putStrLn "PASS: INT-007 every admitted artifact matches its exact SHA-256"
      pure True
    errors -> do
      mapM_ (putStrLn . ("FAIL: INT-007 artifact integrity -- " <>) . show) errors
      pure False

  if and pureResults && fileResult
    then pure ()
    else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

spineCoverage :: Phase1HandoffManifest -> Either String ()
spineCoverage manifest =
  assert (actual == expected)
    ("initial manifest inventory mismatch: " <> show actual)
  where
    actual :: Map HandoffArtifactId (HandoffArtifactKind, FilePath, [HandoffAuthorityRef])
    actual = Map.fromList
      [ ( handoffArtifactId artifact
        , ( handoffArtifactKind artifact
          , handoffArtifactPath artifact
          , handoffArtifactAuthorities artifact
          )
        )
      | artifact <- handoffArtifacts manifest
      ]

    expected = Map.fromList
      [ ( HandoffArtifactId "grammar.phase1.v1"
        , ( HandoffGrammar
          , "grammar/phase1-surface.ebnf"
          , [HandoffMatrixAuthority "SURF-006"]
          )
        )
      , ( HandoffArtifactId "corpus.surface.v1"
        , ( HandoffParserCorpus
          , "test/fixtures/phase1-surface/manifest.json"
          , [HandoffMatrixAuthority "SURF-002"]
          )
        )
      , ( HandoffArtifactId "bundle.lineage.inline.v1"
        , ( HandoffSourceBundle
          , "test/fixtures/phase1/surf010-inline.bundle"
          , [HandoffMatrixAuthority "SURF-010"]
          )
        )
      , ( HandoffArtifactId "bundle.lineage.metadata.v1"
        , ( HandoffSourceBundle
          , "test/fixtures/phase1/surf010-metadata.bundle"
          , [HandoffMatrixAuthority "SURF-010"]
          )
        )
      , ( HandoffArtifactId "bundle.upload.source.v1"
        , ( HandoffSourceBundle
          , "handoff/phase1/witnesses/upload-source-bundle-v1.tsv"
          , [ HandoffMatrixAuthority "INT-001"
            , HandoffMatrixAuthority "SURF-010"
            ]
          )
        )
      , ( HandoffArtifactId "bundle.steve.source.v1"
        , ( HandoffSourceBundle
          , "handoff/phase1/witnesses/steve-source-bundle-v1.tsv"
          , [ HandoffMatrixAuthority "INT-001"
            , HandoffMatrixAuthority "SURF-010"
            ]
          )
        )
      , ( HandoffArtifactId "checked.upload.architecture.v1"
        , ( HandoffCheckedSemantics
          , "handoff/phase1/witnesses/upload-checked-architecture-v1.tsv"
          , [ HandoffMatrixAuthority "INT-001"
            , HandoffCertifiedAuthority "PHIL-ARCH-ID-001"
            , HandoffCertifiedAuthority "PHIL-ARCH-INST-001"
            ]
          )
        )
      , ( HandoffArtifactId "checked.steve.architecture.v1"
        , ( HandoffCheckedSemantics
          , "handoff/phase1/witnesses/steve-checked-architecture-v1.tsv"
          , [ HandoffMatrixAuthority "INT-001"
            , HandoffCertifiedAuthority "PHIL-ARCH-ID-001"
            , HandoffCertifiedAuthority "PHIL-ARCH-INST-001"
            ]
          )
        )
      , ( HandoffArtifactId "verification.upload.bundle.v1"
        , ( HandoffVerificationBundle
          , "handoff/phase1/witnesses/upload-verification-bundle-v1.tsv"
          , [ HandoffMatrixAuthority "INT-002"
            , HandoffMatrixAuthority "VER-012"
            ]
          )
        )
      , ( HandoffArtifactId "verification.steve.bundle.v1"
        , ( HandoffVerificationBundle
          , "handoff/phase1/witnesses/steve-verification-bundle-v1.tsv"
          , [ HandoffMatrixAuthority "INT-002"
            , HandoffMatrixAuthority "VER-012"
            ]
          )
        )
      , ( HandoffArtifactId "corpus.negative.v1"
        , ( HandoffConformanceManifest
          , "test/fixtures/phase1-negative/manifest.tsv"
          , [HandoffMatrixAuthority "INT-004"]
          )
        )
      ]

duplicateArtifactIdRejects :: Either String ()
duplicateArtifactIdRejects =
  expectError isDuplicate $ manifestText
    [ row "same" "grammar" "a" validDigest "matrix:SURF-006"
    , row "same" "source-bundle" "b" validDigest "matrix:SURF-010"
    ]
  where
    isDuplicate HandoffManifestDuplicateArtifactId {} = True
    isDuplicate _ = False

duplicatePathRejects :: Either String ()
duplicatePathRejects =
  expectError isDuplicate $ manifestText
    [ row "one" "grammar" "same" validDigest "matrix:SURF-006"
    , row "two" "source-bundle" "same" validDigest "matrix:SURF-010"
    ]
  where
    isDuplicate HandoffManifestDuplicatePath {} = True
    isDuplicate _ = False

traversalPathRejects :: Either String ()
traversalPathRejects =
  expectError isMalformed $ manifestText
    [row "one" "grammar" "../escape" validDigest "matrix:SURF-006"]
  where
    isMalformed HandoffManifestMalformedPath {} = True
    isMalformed _ = False

malformedDigestRejects :: Either String ()
malformedDigestRejects =
  expectError isMalformed $ manifestText
    [row "one" "grammar" "grammar" "sha256:ABC" "matrix:SURF-006"]
  where
    isMalformed HandoffManifestMalformedDigest {} = True
    isMalformed _ = False

unknownKindRejects :: Either String ()
unknownKindRejects =
  expectError isUnknown $ manifestText
    [row "one" "haskell-object" "object" validDigest "matrix:INT-007"]
  where
    isUnknown HandoffManifestUnknownKind {} = True
    isUnknown _ = False

duplicateAuthorityRejects :: Either String ()
duplicateAuthorityRejects =
  expectError isDuplicate $ manifestText
    [ row "one" "grammar" "grammar" validDigest
        "matrix:SURF-006;matrix:SURF-006"
    ]
  where
    isDuplicate HandoffManifestDuplicateAuthority {} = True
    isDuplicate _ = False

expectError
  :: (Phase1HandoffManifestError -> Bool)
  -> Text
  -> Either String ()
expectError predicate source =
  case decodePhase1HandoffManifest source of
    Left errorValue
      | predicate errorValue -> Right ()
      | otherwise -> Left ("unexpected manifest rejection: " <> show errorValue)
    Right value -> Left ("expected manifest rejection, decoded: " <> show value)

manifestText :: [Text] -> Text
manifestText rows = Text.unlines
  ([ phase1HandoffFormatV1
   , Text.intercalate "\t"
      [ "artifact_id"
      , "artifact_kind"
      , "repository_path"
      , "sha256"
      , "governing_authority"
      ]
   ] <> rows)

row :: Text -> Text -> Text -> Text -> Text -> Text
row artifactId kind path digest authority =
  Text.intercalate "\t" [artifactId, kind, path, digest, authority]

validDigest :: Text
validDigest = "sha256:" <> Text.replicate 64 "0"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail
