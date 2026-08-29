{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Core.Process (ProcessKey)
import Phil.Core.Static
  ( DeclarationDescriptor (..)
  , DeclarationKey
  , DeclarationPresentation (..)
  , InstanceKey
  , SemanticForm (..)
  , deriveDeclarationIdentity
  )
import Phil.Surface.Lineage
import System.Exit (exitFailure)

main :: IO ()
main = do
  inlineFixture <- TextIO.readFile "test/fixtures/phase1/surf010-inline.bundle"
  metadataFixture <- TextIO.readFile "test/fixtures/phase1/surf010-metadata.bundle"
  results <- sequence
    [ test "SURF-010 inline and metadata carriers resolve the same DeclarationKey"
        (inlineMetadataIdentity inlineFixture metadataFixture)
    , test "SURF-010 declaration presentation cannot recompute semantic identity"
        (presentationDoesNotRekey inlineFixture)
    , test "SURF-010 InstanceKey and ProcessKey remain metadata-only lineage"
        (occurrenceLineageIsMetadataOnly inlineFixture metadataFixture)
    , test "SURF-010 semantic attribute namespace is closed"
        attributeOverreachRejects
    , test "SURF-010 duplicate key attribute rejects"
        duplicateKeyAttributeRejects
    , test "SURF-010 conflicting inline and metadata lineage rejects"
        conflictingCarriersReject
    , test "SURF-010 malformed portable lineage key rejects"
        malformedKeyRejects
    , test "SURF-010 missing lineage never falls back to name or source position"
        missingLineageDoesNotRecompute
    , test "SURF-010 copied source cannot silently reuse lineage"
        copiedSourceNeedsFreshLineage
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

inlineMetadataIdentity :: Text -> Text -> Either String ()
inlineMetadataIdentity inlineFixture metadataFixture = do
  inlineResolved <- resolveFixture inlineFixture
  metadataResolved <- resolveFixture metadataFixture
  inlineKey <- declarationAt "site.upload-id" inlineResolved
  metadataKey <- declarationAt "site.upload-id" metadataResolved
  assert (inlineKey == metadataKey)
    "inline @key and persisted metadata produced different DeclarationKeys"

presentationDoesNotRekey :: Text -> Either String ()
presentationDoesNotRekey inlineFixture = do
  resolved <- resolveFixture inlineFixture
  key <- declarationAt "site.upload-id" resolved
  let interfaceSemantics = SemanticRecord (Map.fromList
        [ ("kind", SemanticAtom "record")
        , ("field", SemanticAtom "content-id")
        ])
      definitionSemantics = SemanticAtom "ordinary-definition"
      original = DeclarationDescriptor
        { declarationPresentation = DeclarationPresentation
            "UploadId"
            ["upload", "identity"]
        , declarationKey = key
        , declarationInterfaceSemantics = interfaceSemantics
        , declarationDefinitionSemantics = definitionSemantics
        }
      moved = DeclarationDescriptor
        { declarationPresentation = DeclarationPresentation
            "RenamedUploadId"
            ["moved", "module"]
        , declarationKey = key
        , declarationInterfaceSemantics = interfaceSemantics
        , declarationDefinitionSemantics = definitionSemantics
        }
  assert (deriveDeclarationIdentity original == deriveDeclarationIdentity moved)
    "display name/module path changed declaration identity despite persisted key"

occurrenceLineageIsMetadataOnly :: Text -> Text -> Either String ()
occurrenceLineageIsMetadataOnly inlineFixture metadataFixture = do
  inlineResolved <- resolveFixture inlineFixture
  metadataResolved <- resolveFixture metadataFixture
  inlineInstance <- instanceAt "instance.site.primary" inlineResolved
  metadataInstance <- instanceAt "instance.site.primary" metadataResolved
  inlineProcess <- processAt "process.site.worker" inlineResolved
  metadataProcess <- processAt "process.site.worker" metadataResolved
  assert (inlineInstance == metadataInstance)
    "instance lineage changed with declaration carrier form"
  assert (inlineProcess == metadataProcess)
    "process lineage changed with declaration carrier form"

attributeOverreachRejects :: Either String ()
attributeOverreachRejects =
  mapM_ rejectUnknown
    [ "authorityCarrier"
    , "evidenceCarrier"
    , "qualificationCarrier"
    , "assumptionCarrier"
    , "effectsCarrier"
    , "providerCarrier"
    , "realizationCarrier"
    , "instanceKeyCarrier"
    , "processKeyCarrier"
    ]
  where
    rejectUnknown name =
      expectLineageError
        (\errorValue -> case errorValue of
          UnknownSemanticAttribute _ actual -> actual == name
          _ -> False)
        (singleUnitBundle
          "-"
          ("@" <> name <> "(\"decl:forged\") record Forged {}"))

duplicateKeyAttributeRejects :: Either String ()
duplicateKeyAttributeRejects =
  expectLineageError
    (\errorValue -> case errorValue of
      DuplicateDeclarationKeyAttribute _ -> True
      _ -> False)
    (singleUnitBundle
      "-"
      "@key(\"decl:duplicate\") @key(\"decl:duplicate\") record Duplicate {}")

conflictingCarriersReject :: Either String ()
conflictingCarriersReject =
  expectLineageError
    (\errorValue -> case errorValue of
      ConflictingDeclarationLineage {} -> True
      _ -> False)
    (singleUnitBundle
      "decl:metadata"
      "@key(\"decl:inline\") record Conflict {}")

malformedKeyRejects :: Either String ()
malformedKeyRejects =
  expectLineageError
    (\errorValue -> case errorValue of
      MalformedDeclarationKey {} -> True
      _ -> False)
    (singleUnitBundle
      "-"
      "@key(\"decl:bad key\") record Malformed {}")

missingLineageDoesNotRecompute :: Either String ()
missingLineageDoesNotRecompute =
  expectLineageError
    (\errorValue -> case errorValue of
      MissingDeclarationLineage (DeclarationSiteId site) ->
        site == "UploadId@12:3"
      _ -> False)
    (bundleWithUnits
      [ ("upload.phil", "UploadId@12:3", "-", "record UploadId {}") ])

copiedSourceNeedsFreshLineage :: Either String ()
copiedSourceNeedsFreshLineage = do
  expectLineageError
    (\errorValue -> case errorValue of
      DuplicateDeclarationKey {} -> True
      _ -> False)
    (bundleWithUnits
      [ ("unit.original", "site.original", "decl:copy", "record Same {}")
      , ("unit.copy", "site.copy", "decl:copy", "record Same {}")
      ])
  resolved <- resolveFixture $ bundleWithUnits
    [ ("unit.original", "site.original", "decl:copy-a", "record Same {}")
    , ("unit.copy", "site.copy", "decl:copy-b", "record Same {}")
    ]
  originalKey <- declarationAt "site.original" resolved
  copyKey <- declarationAt "site.copy" resolved
  assert (originalKey /= copyKey)
    "copied source did not receive distinct persisted lineage"

resolveFixture :: Text -> Either String ResolvedSourceBundleLineage
resolveFixture source =
  mapLeft show (decodePortableSourceBundle source >>= resolveSourceBundleLineage)

expectLineageError :: (LineageError -> Bool) -> Text -> Either String ()
expectLineageError predicate source =
  case decodePortableSourceBundle source >>= resolveSourceBundleLineage of
    Left errorValue
      | predicate errorValue -> Right ()
      | otherwise -> Left ("unexpected lineage rejection: " <> show errorValue)
    Right resolved -> Left ("expected lineage rejection, got: " <> show resolved)

declarationAt
  :: Text
  -> ResolvedSourceBundleLineage
  -> Either String DeclarationKey
declarationAt site resolved =
  maybe
    (Left ("missing declaration site: " <> Text.unpack site))
    Right
    (Map.lookup (DeclarationSiteId site) (resolvedDeclarationKeys resolved))

instanceAt
  :: Text
  -> ResolvedSourceBundleLineage
  -> Either String InstanceKey
instanceAt site resolved =
  maybe
    (Left ("missing instance lineage site: " <> Text.unpack site))
    Right
    (Map.lookup (InstanceLineageSiteId site) (resolvedInstanceKeys resolved))

processAt
  :: Text
  -> ResolvedSourceBundleLineage
  -> Either String ProcessKey
processAt site resolved =
  maybe
    (Left ("missing process lineage site: " <> Text.unpack site))
    Right
    (Map.lookup (ProcessLineageSiteId site) (resolvedProcessKeys resolved))

singleUnitBundle :: Text -> Text -> Text
singleUnitBundle metadataKey source =
  bundleWithUnits [("unit.test", "site.test", metadataKey, source)]

bundleWithUnits :: [(Text, Text, Text, Text)] -> Text
bundleWithUnits units = Text.unlines $
  [ "PHIL-SOURCE-BUNDLE-LINEAGE-V1"
  , "root\tprogram:test"
  ]
  ++ map renderUnit units
  where
    renderUnit (unitId, siteId, metadataKey, source) =
      Text.intercalate "\t" ["unit", unitId, siteId, metadataKey, source]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
