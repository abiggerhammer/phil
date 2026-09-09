{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (forM, unless, when)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Text as Text
import Data.Text (Text)
import qualified Data.Text.IO as TextIO
import Phil.Core.Generic
import Phil.Core.Syntax (Mode (..))
import System.Directory (doesFileExist)
import System.Exit (exitFailure)

data GenericNegativeCase = GenericNegativeCase
  { caseId :: Text
  , caseCheckKind :: Text
  , caseExpected :: Text
  , caseLayer :: Text
  , caseAuthority :: Text
  , caseExpectedParameter :: Text
  , caseExpectedPermission :: Text
  , caseExpectedMode :: Text
  }
  deriving (Eq, Show)

data PortableAuthority = PortableAuthority
  { authorityRef :: Text
  , authorityKind :: Text
  , authorityId :: Text
  , authoritySource :: Text
  }
  deriving (Eq, Show)

data PortableUse = PortableUse
  { useFixtureId :: Text
  , useKind :: Text
  , useParameter :: Text
  }
  deriving (Eq, Show)

data PortableActual = PortableActual
  { actualFixtureId :: Text
  , actualParameter :: Text
  , actualMode :: Text
  }
  deriving (Eq, Show)

data PortablePublished = PortablePublished
  { publishedFixtureId :: Text
  , publishedParameter :: Text
  , publishedPermissions :: Text
  }
  deriving (Eq, Show)

root :: FilePath
root = "test/fixtures/phase1-negative/generic-v1"

manifestPath, authorityPath, parametersPath, usesPath, actualsPath, publishedPath :: FilePath
manifestPath = root <> "/manifest.tsv"
authorityPath = root <> "/authority-registry-v1.tsv"
parametersPath = root <> "/parameters-v1.tsv"
usesPath = root <> "/uses-v1.tsv"
actualsPath = root <> "/actuals-v1.tsv"
publishedPath = root <> "/published-v1.tsv"

seedFixtureIds :: Set Text
seedFixtureIds = Set.fromList
  [ "P1-NEG-GEN-002-001"
  , "P1-NEG-GEN-002-002"
  , "P1-NEG-GEN-003-001"
  , "P1-NEG-GEN-006-001"
  , "P1-NEG-GEN-006-002"
  ]

main :: IO ()
main = do
  cases <- readParsed manifestPath parseManifest "manifest"
  authorities <- readParsed authorityPath parseAuthorityRegistry "authority registry"
  parameters <- readParsed parametersPath parseParameters "parameters"
  uses <- readParsed usesPath parseUses "uses"
  actuals <- readParsed actualsPath parseActuals "actuals"
  published <- readParsed publishedPath parsePublished "published requirements"
  integrityOk <- checkIntegrity authorities parameters uses actuals published cases
  results <- forM cases (replayCase parameters uses actuals published)
  unless (integrityOk && and results) exitFailure
  putStrLn ("PASS: INT-004 portable generic negative corpus (" <> show (length cases) <> " fixtures)")

readParsed :: FilePath -> (Text -> Either String a) -> String -> IO a
readParsed path parser label = do
  input <- TextIO.readFile path
  case parser input of
    Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> exitFailure
    Right value -> pure value

parseManifest :: Text -> Either String [GenericNegativeCase]
parseManifest input = parseRows input expected parseRow
  where
    expected =
      [ "fixture_id", "check_kind", "expect", "competent_layer"
      , "governing_authority", "expected_parameter", "expected_permission"
      , "expected_mode"
      ]
    parseRow row = case row of
      [fixtureId, checkKind, expectedResult, layer, authority, parameter, permission, mode]
        | any Text.null row -> Left "empty manifest field"
        | otherwise -> Right GenericNegativeCase
            { caseId = fixtureId
            , caseCheckKind = checkKind
            , caseExpected = expectedResult
            , caseLayer = layer
            , caseAuthority = authority
            , caseExpectedParameter = parameter
            , caseExpectedPermission = permission
            , caseExpectedMode = mode
            }
      _ -> Left "invalid manifest row width"

parseAuthorityRegistry :: Text -> Either String (Map Text PortableAuthority)
parseAuthorityRegistry input = do
  rows <- parseRows input
    ["authority_ref", "authority_kind", "canonical_id", "canonical_source"]
    parseRow
  let result = Map.fromList [(authorityRef row, row) | row <- rows]
      ids = map authorityId rows
  if Map.size result /= length rows
    then Left "duplicate authority_ref"
    else if Set.size (Set.fromList ids) /= length ids
      then Left "duplicate canonical authority id"
      else Right result
  where
    parseRow row = case row of
      [ref, kind, canonicalId, source]
        | any Text.null row -> Left "empty authority field"
        | kind `notElem` ["matrix", "certified"] -> Left "unsupported authority kind"
        | ref /= kind <> ":" <> canonicalId -> Left "authority ref/kind/id mismatch"
        | canonicalId == "INT-004" -> Left "INT-004 is not fixture semantic authority"
        | otherwise -> Right PortableAuthority
            { authorityRef = ref
            , authorityKind = kind
            , authorityId = canonicalId
            , authoritySource = source
            }
      _ -> Left "invalid authority row width"

parseParameters :: Text -> Either String (Map Text [Text])
parseParameters input = do
  rows <- parseRows input ["fixture_id", "parameter_name"] parseRow
  pure (collect [(fixtureId, parameter) | (fixtureId, parameter) <- rows])
  where
    parseRow row = case row of
      [fixtureId, parameter]
        | Text.null fixtureId || Text.null parameter -> Left "empty parameter field"
        | otherwise -> Right (fixtureId, parameter)
      _ -> Left "invalid parameter row width"

parseUses :: Text -> Either String (Map Text [PortableUse])
parseUses input = do
  rows <- parseRows input ["fixture_id", "use_kind", "parameter_name"] parseRow
  pure (collect [(useFixtureId row, row) | row <- rows])
  where
    parseRow row = case row of
      [fixtureId, kind, parameter]
        | any Text.null row -> Left "empty use field"
        | kind `notElem` ["transfer", "discard", "duplicate"] ->
            Left ("unsupported portable use kind: " <> Text.unpack kind)
        | otherwise -> Right PortableUse
            { useFixtureId = fixtureId
            , useKind = kind
            , useParameter = parameter
            }
      _ -> Left "invalid use row width"

parseActuals :: Text -> Either String (Map Text [PortableActual])
parseActuals input = do
  rows <- parseRows input ["fixture_id", "parameter_name", "actual_mode"] parseRow
  pure (collect [(actualFixtureId row, row) | row <- rows])
  where
    parseRow row = case row of
      [fixtureId, parameter, mode]
        | any Text.null row -> Left "empty actual field"
        | mode `notElem` ["unrestricted", "affine", "linear"] ->
            Left ("unsupported portable actual mode: " <> Text.unpack mode)
        | otherwise -> Right PortableActual
            { actualFixtureId = fixtureId
            , actualParameter = parameter
            , actualMode = mode
            }
      _ -> Left "invalid actual row width"

parsePublished :: Text -> Either String (Map Text [PortablePublished])
parsePublished input = do
  rows <- parseRows input ["fixture_id", "parameter_name", "permissions"] parseRow
  pure (collect [(publishedFixtureId row, row) | row <- rows])
  where
    parseRow row = case row of
      [fixtureId, parameter, permissions]
        | any Text.null row -> Left "empty published field"
        | otherwise -> do
            _ <- parsePermissions permissions
            Right PortablePublished
              { publishedFixtureId = fixtureId
              , publishedParameter = parameter
              , publishedPermissions = permissions
              }
      _ -> Left "invalid published row width"

parseRows
  :: Text
  -> [Text]
  -> ([Text] -> Either String a)
  -> Either String [a]
parseRows input expectedHeader parseRow = case Text.lines input of
  [] -> Left "empty TSV"
  header : rows
    | Text.splitOn "\t" header /= expectedHeader ->
        Left ("unexpected header: " <> Text.unpack header)
    | otherwise -> traverse (parseRow . Text.splitOn "\t") (filter (not . Text.null) rows)

collect :: Ord k => [(k, v)] -> Map k [v]
collect = Map.fromListWith (++) . map (\(key, value) -> (key, [value]))

parseMode :: Text -> Either String Mode
parseMode value = case value of
  "unrestricted" -> Right Unrestricted
  "affine" -> Right Affine
  "linear" -> Right Linear
  other -> Left ("unsupported portable mode: " <> Text.unpack other)

parsePermission :: Text -> Either String StructuralPermission
parsePermission value = case value of
  "weakening" -> Right WeakeningPermission
  "contraction" -> Right ContractionPermission
  other -> Left ("unsupported portable structural permission: " <> Text.unpack other)

parsePermissions :: Text -> Either String (Set StructuralPermission)
parsePermissions value = do
  let parts = Text.splitOn ";" value
  when (null parts || any Text.null parts) (Left "empty structural permission")
  permissions <- traverse parsePermission parts
  if Set.size (Set.fromList permissions) /= length permissions
    then Left "duplicate structural permission"
    else Right (Set.fromList permissions)

materializeUse :: PortableUse -> Either String GenericStructuralUse
materializeUse row =
  let key = GenericValueParameterKey (useParameter row)
  in case useKind row of
    "transfer" -> Right (TransferGenericValue key)
    "discard" -> Right (DiscardGenericValue key)
    "duplicate" -> Right (DuplicateGenericValue key)
    other -> Left ("unsupported portable use kind: " <> Text.unpack other)

caseAuthorityRefs :: GenericNegativeCase -> Either String [Text]
caseAuthorityRefs negativeCase = do
  let refs = Text.splitOn ";" (caseAuthority negativeCase)
  when (null refs || any Text.null refs) (Left "empty governing authority reference")
  when (Set.size (Set.fromList refs) /= length refs) (Left "duplicate governing authority reference")
  traverse checkRef refs
  where
    checkRef ref = case Text.breakOn ":" ref of
      (kind, rest) -> case Text.stripPrefix ":" rest of
        Nothing -> Left "untyped governing authority reference"
        Just canonicalId
          | kind `notElem` ["matrix", "certified"] -> Left "unknown governing authority kind"
          | Text.null canonicalId -> Left "empty governing authority id"
          | canonicalId == "INT-004" -> Left "INT-004 is not fixture semantic authority"
          | otherwise -> Right ref

checkIntegrity
  :: Map Text PortableAuthority
  -> Map Text [Text]
  -> Map Text [PortableUse]
  -> Map Text [PortableActual]
  -> Map Text [PortablePublished]
  -> [GenericNegativeCase]
  -> IO Bool
checkIntegrity authorities parameters uses actuals published cases = do
  let ids = map caseId cases
      fixtureDomainExact = Set.fromList ids == seedFixtureIds && length ids == 5
      uniqueIds = Set.size (Set.fromList ids) == length ids
      parameterDomainExact = Map.keysSet parameters == seedFixtureIds
      useDomainExact = Map.keysSet uses == seedFixtureIds
      otherDomainsDeclared =
        Map.keysSet actuals `Set.isSubsetOf` seedFixtureIds
          && Map.keysSet published `Set.isSubsetOf` seedFixtureIds
      uniqueParameters = all uniqueTextRows (Map.elems parameters)
      usesDeclared = and
        [ useParameter row `elem` Map.findWithDefault [] fixtureId parameters
        | (fixtureId, rows) <- Map.toList uses
        , row <- rows
        ]
      actualsDeclared = and
        [ actualParameter row `elem` Map.findWithDefault [] fixtureId parameters
        | (fixtureId, rows) <- Map.toList actuals
        , row <- rows
        ]
      publishedDeclared = and
        [ publishedParameter row `elem` Map.findWithDefault [] fixtureId parameters
        | (fixtureId, rows) <- Map.toList published
        , row <- rows
        ]
      uniqueActualParameters = all
        (uniqueTextRows . map actualParameter)
        (Map.elems actuals)
      uniquePublishedParameters = all
        (uniqueTextRows . map publishedParameter)
        (Map.elems published)
      shapesValid = all (caseShapeValid actuals published) cases
      parsedAuthorities = traverse caseAuthorityRefs cases
      authoritySyntaxValid = either (const False) (const True) parsedAuthorities
      usedAuthorityRefs = case parsedAuthorities of
        Left _ -> Set.empty
        Right rows -> Set.fromList (concat rows)
      authorityDomainExact = authoritySyntaxValid && usedAuthorityRefs == Map.keysSet authorities
      matrixSourcesExact = all
        (\authority -> authorityKind authority /= "matrix"
          || authoritySource authority == "Phil Phase 1 Conformance Matrix")
        (Map.elems authorities)
      certifiedSourcesPortable = all
        (\authority -> authorityKind authority /= "certified"
          || ("proof/" `Text.isPrefixOf` authoritySource authority
            && ".v" `Text.isSuffixOf` authoritySource authority))
        (Map.elems authorities)
      certifiedPaths =
        [ Text.unpack (authoritySource authority)
        | authority <- Map.elems authorities
        , authorityKind authority == "certified"
        ]
  certifiedSourcesPresent <- and <$> mapM doesFileExist certifiedPaths
  report "generic fixture domain is exact and stable" fixtureDomainExact
  report "generic fixture IDs are unique" uniqueIds
  report "every fixture has declared portable parameters" parameterDomainExact
  report "every fixture has body-directed portable uses" useDomainExact
  report "actual/publication tables only name declared fixtures" otherDomainsDeclared
  report "parameter declarations are unique per fixture" uniqueParameters
  report "portable uses name declared parameters" usesDeclared
  report "portable actuals name declared parameters" actualsDeclared
  report "portable published requirements name declared parameters" publishedDeclared
  report "actual modes are unique per parameter" uniqueActualParameters
  report "published permissions are unique per parameter" uniquePublishedParameters
  report "checker/layer/input shape is competent and exact" shapesValid
  report "every fixture has typed non-meta authority references" authoritySyntaxValid
  report "manifest authority domain resolves exactly to registry" authorityDomainExact
  report "Matrix authority rows name the canonical Matrix source" matrixSourcesExact
  report "Certified authority rows name portable proof artifacts" certifiedSourcesPortable
  report "every Certified authority proof artifact exists" certifiedSourcesPresent
  pure (and
    [ fixtureDomainExact, uniqueIds, parameterDomainExact, useDomainExact
    , otherDomainsDeclared, uniqueParameters, usesDeclared, actualsDeclared
    , publishedDeclared, uniqueActualParameters, uniquePublishedParameters
    , shapesValid, authoritySyntaxValid, authorityDomainExact, matrixSourcesExact
    , certifiedSourcesPortable, certifiedSourcesPresent
    ])

uniqueTextRows :: [Text] -> Bool
uniqueTextRows rows = Set.size (Set.fromList rows) == length rows

caseShapeValid
  :: Map Text [PortableActual]
  -> Map Text [PortablePublished]
  -> GenericNegativeCase
  -> Bool
caseShapeValid actuals published negativeCase = case caseCheckKind negativeCase of
  "structural-actual" ->
    caseLayer negativeCase == "generic-structural"
      && caseExpected negativeCase == "missing-structural-permission"
      && length (Map.findWithDefault [] (caseId negativeCase) actuals) == 1
      && null (Map.findWithDefault [] (caseId negativeCase) published)
      && caseExpectedMode negativeCase `elem` ["unrestricted", "affine", "linear"]
  "structural-interface" ->
    caseLayer negativeCase == "generic-requirements"
      && caseExpected negativeCase == "published-structural-requirement-too-weak"
      && null (Map.findWithDefault [] (caseId negativeCase) actuals)
      && caseExpectedMode negativeCase == "-"
  _ -> False

replayCase
  :: Map Text [Text]
  -> Map Text [PortableUse]
  -> Map Text [PortableActual]
  -> Map Text [PortablePublished]
  -> GenericNegativeCase
  -> IO Bool
replayCase parameters uses actuals published negativeCase = do
  let fixtureId = caseId negativeCase
      parameterKeys = map GenericValueParameterKey (Map.findWithDefault [] fixtureId parameters)
      portableUses = Map.findWithDefault [] fixtureId uses
  result <- case traverse materializeUse portableUses of
    Left detail -> pure (Left ("portable use materialization failed: " <> detail))
    Right materializedUses -> case caseCheckKind negativeCase of
      "structural-actual" -> pure $
        replayStructuralActual negativeCase parameterKeys materializedUses
          (Map.findWithDefault [] fixtureId actuals)
      "structural-interface" -> pure $
        replayStructuralInterface negativeCase parameterKeys materializedUses
          (Map.findWithDefault [] fixtureId published)
      other -> pure (Left ("unknown portable generic check kind: " <> Text.unpack other))
  case result of
    Right () -> putStrLn ("PASS: " <> Text.unpack fixtureId) >> pure True
    Left detail -> putStrLn ("FAIL: " <> Text.unpack fixtureId <> " -- " <> detail) >> pure False

replayStructuralActual
  :: GenericNegativeCase
  -> [GenericValueParameterKey]
  -> [GenericStructuralUse]
  -> [PortableActual]
  -> Either String ()
replayStructuralActual negativeCase parameterKeys uses rows = do
  actual <- case rows of
    [row] -> Right row
    _ -> Left "structural-actual fixture does not have exactly one actual"
  mode <- parseMode (actualMode actual)
  inferred <- mapLeft show (inferGenericStructuralRequirements parameterKeys uses)
  let key = GenericValueParameterKey (actualParameter actual)
  requirements <- maybe
    (Left "actual parameter has no inferred structural requirements")
    Right
    (Map.lookup key inferred)
  expectedPermission <- parsePermission (caseExpectedPermission negativeCase)
  expectedMode <- parseMode (caseExpectedMode negativeCase)
  case checkGenericStructuralActual key mode requirements of
    Left (MissingStructuralPermission actualKey actualPermission rejectedMode)
      | actualKey == GenericValueParameterKey (caseExpectedParameter negativeCase)
          && actualPermission == expectedPermission
          && rejectedMode == expectedMode
          && mode == expectedMode -> Right ()
      | otherwise -> Left "structural rejection did not preserve expected parameter/permission/mode"
    Left other -> Left ("wrong competent rejection: " <> show other)
    Right () -> Left "portable negative unexpectedly accepted"

replayStructuralInterface
  :: GenericNegativeCase
  -> [GenericValueParameterKey]
  -> [GenericStructuralUse]
  -> [PortablePublished]
  -> Either String ()
replayStructuralInterface negativeCase parameterKeys uses publishedRows = do
  publishedRequirements <- traverse materializePublished publishedRows
  expectedPermission <- parsePermission (caseExpectedPermission negativeCase)
  case checkGenericStructuralInterface parameterKeys uses (Just publishedRequirements) of
    Left (PublishedStructuralRequirementTooWeak actualKey actualPermission)
      | actualKey == GenericValueParameterKey (caseExpectedParameter negativeCase)
          && actualPermission == expectedPermission -> Right ()
      | otherwise -> Left "interface rejection did not preserve expected parameter/permission"
    Left other -> Left ("wrong competent rejection: " <> show other)
    Right _ -> Left "portable negative unexpectedly accepted"

materializePublished
  :: PortablePublished
  -> Either String (GenericValueParameterKey, GenericStructuralRequirements)
materializePublished row = do
  permissions <- parsePermissions (publishedPermissions row)
  Right
    ( GenericValueParameterKey (publishedParameter row)
    , GenericStructuralRequirements permissions
    )

report :: String -> Bool -> IO ()
report label condition = putStrLn ((if condition then "PASS: " else "FAIL: ") <> label)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
