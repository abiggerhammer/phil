{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (forM, unless)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import qualified Data.Text as Text
import Data.Text (Text)
import qualified Data.Text.IO as TextIO
import Phil.Core.Generic
import Phil.Core.Static (InterfaceRevision (..))
import Phil.Core.Syntax (Proposition (..))
import System.Directory (doesFileExist)
import System.Exit (exitFailure)

data PortableCase = PortableCase
  { caseId :: Text
  , caseExpected :: Text
  , caseLayer :: Text
  , caseAuthorities :: Text
  , caseExpectedA :: Text
  , caseExpectedB :: Text
  , caseExpectedC :: Text
  , caseExpectedD :: Text
  }
  deriving (Eq, Show)

data PortableRequirement = PortableRequirement
  { requirementFixtureId :: Text
  , requirementId :: Text
  , requirementKind :: Text
  , requirementParameter :: Text
  , requirementValue :: Text
  }
  deriving (Eq, Show)

data PortableDisposition = PortableDisposition
  { dispositionFixtureId :: Text
  , dispositionRequirementId :: Text
  , dispositionKind :: Text
  , dispositionValue1 :: Text
  , dispositionValue2 :: Text
  , dispositionValue3 :: Text
  }
  deriving (Eq, Show)

data PortablePolicy = PortablePolicy
  { policyFixtureId :: Text
  , policyAllowsAssumptions :: Text
  , policyAllowsExports :: Text
  }
  deriving (Eq, Show)

data PortableAuthority = PortableAuthority
  { authorityRef :: Text
  , authorityKind :: Text
  , authorityCanonicalId :: Text
  , authorityCanonicalSource :: Text
  }
  deriving (Eq, Show)

root :: FilePath
root = "test/fixtures/phase1-negative/generic-instantiation-v1"

manifestPath, requirementsPath, dispositionsPath, policiesPath, authoritiesPath :: FilePath
manifestPath = root <> "/manifest.tsv"
requirementsPath = root <> "/requirements-v1.tsv"
dispositionsPath = root <> "/dispositions-v1.tsv"
policiesPath = root <> "/policies-v1.tsv"
authoritiesPath = root <> "/authority-registry-v1.tsv"

main :: IO ()
main = do
  cases <- readParsed manifestPath parseManifest "manifest"
  requirements <- readParsed requirementsPath parseRequirements "requirements"
  dispositions <- readParsed dispositionsPath parseDispositions "dispositions"
  policies <- readParsed policiesPath parsePolicies "policies"
  authorities <- readParsed authoritiesPath parseAuthorities "authorities"
  integrity <- checkIntegrity cases requirements dispositions policies authorities
  results <- forM cases (replayCase requirements dispositions policies)
  unless (integrity && and results) exitFailure
  putStrLn ("PASS: INT-004 portable generic-instantiation negatives (" <> show (length cases) <> " fixtures)")

readParsed :: FilePath -> (Text -> Either String a) -> String -> IO a
readParsed path parser label = do
  input <- TextIO.readFile path
  case parser input of
    Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> exitFailure
    Right value -> pure value

parseManifest :: Text -> Either String [PortableCase]
parseManifest = parseTable expected parseRow
  where
    expected = ["fixture_id", "expect", "competent_layer", "governing_authority", "expected_a", "expected_b", "expected_c", "expected_d"]
    parseRow row = case row of
      [fixtureId, expectedResult, layer, authorities, a, b, c, d]
        | all (not . Text.null) [fixtureId, expectedResult, layer, authorities, a, b, c, d] ->
            Right (PortableCase fixtureId expectedResult layer authorities a b c d)
      _ -> Left ("invalid manifest row: " <> show row)

parseRequirements :: Text -> Either String [PortableRequirement]
parseRequirements = parseTable expected parseRow
  where
    expected = ["fixture_id", "requirement_id", "requirement_kind", "parameter_name", "value"]
    parseRow row = case row of
      [fixtureId, reqId, kind, parameterName, value]
        | all (not . Text.null) row -> Right (PortableRequirement fixtureId reqId kind parameterName value)
      _ -> Left ("invalid requirement row: " <> show row)

parseDispositions :: Text -> Either String [PortableDisposition]
parseDispositions = parseTable expected parseRow
  where
    expected = ["fixture_id", "requirement_id", "disposition_kind", "value1", "value2", "value3"]
    parseRow row = case row of
      [fixtureId, reqId, kind, value1, value2, value3]
        | all (not . Text.null) row -> Right (PortableDisposition fixtureId reqId kind value1 value2 value3)
      _ -> Left ("invalid disposition row: " <> show row)

parsePolicies :: Text -> Either String [PortablePolicy]
parsePolicies = parseTable expected parseRow
  where
    expected = ["fixture_id", "allow_assumptions", "allow_exports"]
    parseRow row = case row of
      [fixtureId, assumptions, exports]
        | all (not . Text.null) row -> Right (PortablePolicy fixtureId assumptions exports)
      _ -> Left ("invalid policy row: " <> show row)

parseAuthorities :: Text -> Either String [PortableAuthority]
parseAuthorities = parseTable expected parseRow
  where
    expected = ["authority_ref", "authority_kind", "canonical_id", "canonical_source"]
    parseRow row = case row of
      [ref, kind, canonicalId, source]
        | all (not . Text.null) row -> Right (PortableAuthority ref kind canonicalId source)
      _ -> Left ("invalid authority row: " <> show row)

parseTable :: [Text] -> ([Text] -> Either String a) -> Text -> Either String [a]
parseTable expectedHeader parseRow input = case Text.lines input of
  [] -> Left "empty TSV"
  header : rows
    | Text.splitOn "\t" header /= expectedHeader -> Left ("unexpected header: " <> Text.unpack header)
    | otherwise -> traverse (parseRow . Text.splitOn "\t") (filter (not . Text.null) rows)

checkIntegrity
  :: [PortableCase]
  -> [PortableRequirement]
  -> [PortableDisposition]
  -> [PortablePolicy]
  -> [PortableAuthority]
  -> IO Bool
checkIntegrity cases requirements dispositions policies authorities = do
  let fixtureIds = map caseId cases
      fixtureDomain = Set.fromList fixtureIds
      exactCount = length cases == 7
      uniqueFixtures = Set.size fixtureDomain == length fixtureIds
      layersExact = all ((== "generic-instantiation") . caseLayer) cases
      requirementFixtures = Set.fromList (map requirementFixtureId requirements)
      dispositionFixtures = Set.fromList (map dispositionFixtureId dispositions)
      policyIds = map policyFixtureId policies
      policyDomainExact = Set.fromList policyIds == fixtureDomain && Set.size (Set.fromList policyIds) == length policyIds
      rowsReferenceFixtures = requirementFixtures `Set.isSubsetOf` fixtureDomain && dispositionFixtures `Set.isSubsetOf` fixtureDomain
      authorityMap = Map.fromList [(authorityRef authority, authority) | authority <- authorities]
      authorityUnique = Map.size authorityMap == length authorities
      authorityRowsWellFormed = all authorityRowWellFormed authorities
      parsedRefs = traverse caseAuthorityRefs cases
      usedRefs = either (const Set.empty) (Set.fromList . concat) parsedRefs
      authorityDomainExact = either (const False) (const True) parsedRefs && usedRefs == Map.keysSet authorityMap
      rowDomainsValid = all (fixtureRowsValid requirements dispositions policies) cases
      expectedKinds = Set.fromList (map caseExpected cases)
      expectedKindsExact = expectedKinds == Set.fromList
        [ "provider-interface-mismatch"
        , "provider-refinement-mismatch"
        , "missing-requirement"
        , "proposition-evidence-mismatch"
        , "assumption-not-permitted"
        , "export-not-permitted"
        ]
      certifiedPaths =
        [ Text.unpack (authorityCanonicalSource authority)
        | authority <- authorities
        , authorityKind authority == "certified"
        ]
  certifiedPresent <- and <$> mapM doesFileExist certifiedPaths
  report "seven generic-instantiation negatives are manifest-owned" exactCount
  report "portable fixture identities are unique" uniqueFixtures
  report "competent layer is exactly generic-instantiation" layersExact
  report "requirement/disposition rows reference declared fixtures" rowsReferenceFixtures
  report "every fixture has exactly one portable policy" policyDomainExact
  report "authority registry rows are unique and well formed" (authorityUnique && authorityRowsWellFormed)
  report "manifest authority domain resolves exactly" authorityDomainExact
  report "every Certified authority proof artifact exists" certifiedPresent
  report "portable per-fixture requirement/disposition domains are valid" rowDomainsValid
  report "portable expected rejection vocabulary is exact" expectedKindsExact
  pure (and
    [ exactCount
    , uniqueFixtures
    , layersExact
    , rowsReferenceFixtures
    , policyDomainExact
    , authorityUnique
    , authorityRowsWellFormed
    , authorityDomainExact
    , certifiedPresent
    , rowDomainsValid
    , expectedKindsExact
    ])

authorityRowWellFormed :: PortableAuthority -> Bool
authorityRowWellFormed authority =
  authorityKind authority `elem` ["matrix", "certified"]
    && authorityRef authority == authorityKind authority <> ":" <> authorityCanonicalId authority
    && authorityCanonicalId authority /= "INT-004"
    && case authorityKind authority of
      "matrix" -> authorityCanonicalSource authority == "Phil Phase 1 Conformance Matrix"
      "certified" -> "proof/" `Text.isPrefixOf` authorityCanonicalSource authority && ".v" `Text.isSuffixOf` authorityCanonicalSource authority
      _ -> False

caseAuthorityRefs :: PortableCase -> Either String [Text]
caseAuthorityRefs portableCase = do
  let refs = Text.splitOn ";" (caseAuthorities portableCase)
  if null refs || any Text.null refs
    then Left "empty authority reference"
    else if Set.size (Set.fromList refs) /= length refs
      then Left "duplicate authority reference"
      else traverse checkRef refs
  where
    checkRef ref = case Text.breakOn ":" ref of
      (kind, rest) -> case Text.stripPrefix ":" rest of
        Just canonicalId
          | kind `elem` ["matrix", "certified"] && not (Text.null canonicalId) && canonicalId /= "INT-004" -> Right ref
        _ -> Left ("invalid authority reference: " <> Text.unpack ref)

fixtureRowsValid
  :: [PortableRequirement]
  -> [PortableDisposition]
  -> [PortablePolicy]
  -> PortableCase
  -> Bool
fixtureRowsValid requirements dispositions policies portableCase =
  case materializeRequirements reqRows of
    Left _ -> False
    Right reqMap ->
      length policyRows == 1
        && all (\row -> Map.member (dispositionRequirementId row) reqMap) dispRows
  where
    fixture = caseId portableCase
    reqRows = filter ((== fixture) . requirementFixtureId) requirements
    dispRows = filter ((== fixture) . dispositionFixtureId) dispositions
    policyRows = filter ((== fixture) . policyFixtureId) policies

replayCase
  :: [PortableRequirement]
  -> [PortableDisposition]
  -> [PortablePolicy]
  -> PortableCase
  -> IO Bool
replayCase requirements dispositions policies portableCase = do
  let fixture = caseId portableCase
      reqRows = filter ((== fixture) . requirementFixtureId) requirements
      dispRows = filter ((== fixture) . dispositionFixtureId) dispositions
      policyRows = filter ((== fixture) . policyFixtureId) policies
      result = do
        reqMap <- materializeRequirements reqRows
        policy <- case policyRows of
          [row] -> materializePolicy row
          _ -> Left "fixture must have exactly one policy row"
        dispEntries <- traverse (materializeDisposition reqMap) dispRows
        case checkGenericInstantiation policy (Set.fromList (Map.elems reqMap)) dispEntries of
          Left err -> matchExpected portableCase err
          Right _ -> Left "portable negative unexpectedly accepted"
  case result of
    Right () -> putStrLn ("PASS: " <> Text.unpack fixture) >> pure True
    Left detail -> putStrLn ("FAIL: " <> Text.unpack fixture <> " -- " <> detail) >> pure False

materializeRequirements :: [PortableRequirement] -> Either String (Map Text GenericRequirement)
materializeRequirements rows = go Map.empty rows
  where
    go result [] = Right result
    go result (row : rest)
      | Map.member (requirementId row) result = Left "duplicate portable requirement_id within fixture"
      | otherwise = do
          requirement <- materializeRequirement row
          go (Map.insert (requirementId row) requirement result) rest

materializeRequirement :: PortableRequirement -> Either String GenericRequirement
materializeRequirement row = case requirementKind row of
  "provider-contract"
    | requirementParameter row /= "-" && requirementValue row /= "-" ->
        Right (GenericProviderContractRequirement
          (GenericStaticParameterKey (requirementParameter row))
          (InterfaceRevision (requirementValue row)))
  "proposition"
    | requirementParameter row == "-" && requirementValue row /= "-" ->
        Right (GenericPropositionRequirement (Atom (requirementValue row) []))
  other -> Left ("unsupported or malformed portable requirement kind: " <> Text.unpack other)

materializeDisposition
  :: Map Text GenericRequirement
  -> PortableDisposition
  -> Either String (GenericRequirement, GenericRequirementDisposition)
materializeDisposition requirements row = do
  requirement <- maybe (Left "disposition references undeclared requirement_id") Right
    (Map.lookup (dispositionRequirementId row) requirements)
  disposition <- case dispositionKind row of
    "exact-provider" -> do
      requireDash (dispositionValue2 row)
      requireDash (dispositionValue3 row)
      Right (GenericSatisfiedByExactProvider (InterfaceRevision (dispositionValue1 row)))
    "checked-provider-refinement" -> Right
      (GenericSatisfiedByCheckedProviderRefinement CheckedProviderRefinement
        { checkedProviderRefinementActual = InterfaceRevision (dispositionValue1 row)
        , checkedProviderRefinementRequired = InterfaceRevision (dispositionValue2 row)
        , checkedProviderRefinementWitness = dispositionValue3 row
        })
    "evidence" -> do
      requireDash (dispositionValue3 row)
      Right (GenericSatisfiedByEvidence GenericEvidence
        { genericEvidenceProposition = Atom (dispositionValue1 row) []
        , genericEvidenceIdentity = dispositionValue2 row
        })
    "assumption" -> do
      requireDash (dispositionValue2 row)
      requireDash (dispositionValue3 row)
      Right (GenericAssumptionDependent (dispositionValue1 row))
    "export" -> do
      requireDash (dispositionValue2 row)
      requireDash (dispositionValue3 row)
      Right (GenericExported (dispositionValue1 row))
    other -> Left ("unsupported portable disposition kind: " <> Text.unpack other)
  pure (requirement, disposition)

materializePolicy :: PortablePolicy -> Either String GenericInstantiationPolicy
materializePolicy row = GenericInstantiationPolicy
  <$> parseBool (policyAllowsAssumptions row)
  <*> parseBool (policyAllowsExports row)

parseBool :: Text -> Either String Bool
parseBool value = case value of
  "true" -> Right True
  "false" -> Right False
  _ -> Left ("invalid portable boolean: " <> Text.unpack value)

requireDash :: Text -> Either String ()
requireDash value
  | value == "-" = Right ()
  | otherwise = Left "unused portable disposition field must be '-'"

matchExpected :: PortableCase -> GenericInstantiationError -> Either String ()
matchExpected portableCase err = case (caseExpected portableCase, err) of
  ("provider-interface-mismatch", GenericProviderInterfaceMismatch (GenericStaticParameterKey key) (InterfaceRevision required) (InterfaceRevision actual)) ->
    assertFields [key, required, actual, "-"]
  ("provider-refinement-mismatch", GenericProviderRefinementMismatch (GenericStaticParameterKey key) (InterfaceRevision required) (InterfaceRevision actual) (InterfaceRevision target)) ->
    assertFields [key, required, actual, target]
  ("missing-requirement", MissingGenericRequirementDisposition requirement) ->
    assertFields [portableRequirementLabel requirement, "-", "-", "-"]
  ("proposition-evidence-mismatch", GenericPropositionEvidenceMismatch (Atom expected []) (Atom actual [])) ->
    assertFields [expected, actual, "-", "-"]
  ("assumption-not-permitted", GenericAssumptionNotPermitted requirement) ->
    assertFields [portableRequirementLabel requirement, "-", "-", "-"]
  ("export-not-permitted", GenericExportNotPermitted requirement) ->
    assertFields [portableRequirementLabel requirement, "-", "-", "-"]
  _ -> Left ("unexpected generic-instantiation rejection: " <> show err)
  where
    assertFields actual =
      let expected = [caseExpectedA portableCase, caseExpectedB portableCase, caseExpectedC portableCase, caseExpectedD portableCase]
      in if actual == expected
          then Right ()
          else Left ("rejection details differ: expected " <> show expected <> ", got " <> show actual)

portableRequirementLabel :: GenericRequirement -> Text
portableRequirementLabel requirement = case requirement of
  GenericPropositionRequirement (Atom claim []) -> "proposition:" <> claim
  GenericProviderContractRequirement (GenericStaticParameterKey key) (InterfaceRevision revision) ->
    "provider:" <> key <> ":" <> revision
  _ -> "unsupported-requirement-shape"

report :: String -> Bool -> IO ()
report label ok = putStrLn ((if ok then "PASS: " else "FAIL: ") <> label)
