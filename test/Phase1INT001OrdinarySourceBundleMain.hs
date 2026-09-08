{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Compiler.SourceBundle
import Phil.Core.Static (DeclarationKey (..), emptyStaticContext)
import Phil.Core.Syntax (Ty (TyUnit))
import Phil.Surface.Check
  ( SurfaceEnvironment (..)
  , emptySurfaceEnvironment
  )
import Phil.Surface.Lineage
  ( DeclarationSiteId (..)
  , LineageError (MissingDeclarationLineage)
  , PortableSourceBundle (..)
  , PortableSourceUnit (..)
  , SourceUnitId (..)
  , canonicalGrammarRevisionV1
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "INT-001 two unrelated ordinary programs use one SourceBundle checker"
        unrelatedProgramsSharePath
    , test "INT-001 presentation rename does not select compiler behavior"
        presentationRenameNeutral
    , test "INT-001 source carrier identity does not select checking environment"
        carrierIdentityNeutral
    , test "INT-001 missing exact declaration-key environment rejects"
        missingEnvironmentRejects
    , test "INT-001 malformed ordinary source rejects at parser"
        malformedSourceRejects
    , test "INT-001 one lineage declaration cannot hide multiple components"
        multiComponentCarrierRejects
    , test "INT-001 selected root must name a declaration present in bundle"
        foreignRootRejects
    , test "INT-001 missing persisted declaration lineage rejects before parsing"
        missingLineageRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

unrelatedProgramsSharePath :: Either String ()
unrelatedProgramsSharePath = do
  alpha <- mapLeft show $ checkPortableSourceBundle roots environments alphaBundle
  beta <- mapLeft show $ checkPortableSourceBundle roots environments betaBundle
  assert
    ( checkedSourceSelectedRootKey alpha == alphaKey
      && checkedSourceSelectedRootKey beta == betaKey
      && map checkedSourceDeclarationKey (checkedSourceUnits alpha) == [alphaKey]
      && map checkedSourceDeclarationKey (checkedSourceUnits beta) == [betaKey] )
    "shared SourceBundle checker lost exact declaration/root identity"

presentationRenameNeutral :: Either String ()
presentationRenameNeutral = do
  original <- mapLeft show $ checkPortableSourceBundle roots environments alphaBundle
  renamed <- mapLeft show $ checkPortableSourceBundle roots environments alphaRenamedBundle
  assert
    ( checkedSourceSelectedRootKey original == checkedSourceSelectedRootKey renamed
      && map checkedSourceDeclarationKey (checkedSourceUnits original)
          == map checkedSourceDeclarationKey (checkedSourceUnits renamed) )
    "component presentation rename changed semantic SourceBundle selection"

carrierIdentityNeutral :: Either String ()
carrierIdentityNeutral = do
  checked <- mapLeft show $ checkPortableSourceBundle roots environments alphaOddCarrierBundle
  assert
    (map checkedSourceDeclarationKey (checkedSourceUnits checked) == [alphaKey])
    "source-unit carrier identity influenced environment selection"

missingEnvironmentRejects :: Either String ()
missingEnvironmentRejects =
  case checkPortableSourceBundle roots (Map.delete alphaKey environments) alphaBundle of
    Left (SourceBundleEnvironmentMissing actual) ->
      assert (actual == alphaKey) "missing-environment rejection lost exact DeclarationKey"
    other -> Left ("missing declaration-key environment did not reject: " <> show other)

malformedSourceRejects :: Either String ()
malformedSourceRejects =
  case checkPortableSourceBundle roots environments
      (singleUnitBundle "program:alpha" "carrier.alpha" "site.alpha" alphaKeyText
        "component Alpha provides Unit { return") of
    Left (SourceBundleParseError actual _) ->
      assert (actual == SourceUnitId "carrier.alpha") "parse error lost exact SourceUnitId"
    other -> Left ("malformed source did not reject at parser: " <> show other)

multiComponentCarrierRejects :: Either String ()
multiComponentCarrierRejects =
  case checkPortableSourceBundle roots environments
      (singleUnitBundle "program:alpha" "carrier.alpha" "site.alpha" alphaKeyText
        (unitComponent "Alpha" <> "\n" <> unitComponent "Hidden")) of
    Left (SourceBundleDeclarationCountMismatch actual 2) ->
      assert (actual == SourceUnitId "carrier.alpha")
        "multi-component rejection lost exact SourceUnitId"
    other -> Left ("one lineage declaration admitted multiple components: " <> show other)

foreignRootRejects :: Either String ()
foreignRootRejects =
  let foreignKey = DeclarationKey "decl:foreign"
      foreignRoots = Map.insert "program:alpha" foreignKey roots
  in case checkPortableSourceBundle foreignRoots environments alphaBundle of
    Left (SourceBundleSelectedRootNotInBundle root actual) ->
      assert (root == "program:alpha" && actual == foreignKey)
        "foreign-root rejection lost exact selected root/key"
    other -> Left ("foreign selected root entered checked bundle: " <> show other)

missingLineageRejects :: Either String ()
missingLineageRejects =
  let bundle = PortableSourceBundle
        { portableGrammarRevision = canonicalGrammarRevisionV1
        , portableSelectedProgramRoot = "program:alpha"
        , portableSourceUnits =
            [ PortableSourceUnit
                { portableSourceUnitId = SourceUnitId "carrier.alpha"
                , portableDeclarationSiteId = DeclarationSiteId "site.alpha"
                , portableDeclarationMetadataKey = Nothing
                , portableSourceText = unitComponent "Alpha"
                }
            ]
        , portableInstanceLineage = []
        , portableProcessLineage = []
        }
  in case checkPortableSourceBundle roots environments bundle of
    Left (SourceBundleLineageError (MissingDeclarationLineage actual)) ->
      assert (actual == DeclarationSiteId "site.alpha")
        "missing-lineage rejection lost exact DeclarationSiteId"
    other -> Left ("missing declaration lineage reached parser/checker: " <> show other)

alphaBundle, alphaRenamedBundle, alphaOddCarrierBundle, betaBundle :: PortableSourceBundle
alphaBundle = singleUnitBundle
  "program:alpha" "carrier.alpha" "site.alpha" alphaKeyText (unitComponent "Alpha")

alphaRenamedBundle = singleUnitBundle
  "program:alpha" "carrier.alpha" "site.alpha" alphaKeyText (unitComponent "CompletelyDifferentName")

alphaOddCarrierBundle = singleUnitBundle
  "program:alpha" "this-is-not-alpha.phil" "site.alpha" alphaKeyText (unitComponent "Alpha")

betaBundle = singleUnitBundle
  "program:beta" "carrier.beta" "site.beta" betaKeyText (unitComponent "Beta")

singleUnitBundle :: Text -> Text -> Text -> Text -> Text -> PortableSourceBundle
singleUnitBundle root unitId siteId metadataKey source = PortableSourceBundle
  { portableGrammarRevision = canonicalGrammarRevisionV1
  , portableSelectedProgramRoot = root
  , portableSourceUnits =
      [ PortableSourceUnit
          { portableSourceUnitId = SourceUnitId unitId
          , portableDeclarationSiteId = DeclarationSiteId siteId
          , portableDeclarationMetadataKey = Just metadataKey
          , portableSourceText = source
          }
      ]
  , portableInstanceLineage = []
  , portableProcessLineage = []
  }

unitComponent :: Text -> Text
unitComponent name = "component " <> name <> " provides Unit { return unit }"

unitEnvironment :: SurfaceEnvironment
unitEnvironment = (emptySurfaceEnvironment emptyStaticContext)
  { surfaceExpectedProvides = Just TyUnit }

alphaKey, betaKey :: DeclarationKey
alphaKey = DeclarationKey alphaKeyText
betaKey = DeclarationKey betaKeyText

alphaKeyText, betaKeyText :: Text
alphaKeyText = "decl:alpha"
betaKeyText = "decl:beta"

roots :: SourceRootMap
roots = Map.fromList
  [ ("program:alpha", alphaKey)
  , ("program:beta", betaKey)
  ]

environments :: SourceEnvironmentMap
environments = Map.fromList
  [ (alphaKey, unitEnvironment)
  , (betaKey, unitEnvironment)
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
