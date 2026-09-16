{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (forM, unless)
import qualified Data.Set as Set
import qualified Data.Text as Text
import Data.Text (Text)
import qualified Data.Text.IO as TextIO
import Phil.Core.Callable
import Phil.Core.CallableRefinement
import Phil.Core.Static (InterfaceRevision (..))
import Phil.Core.Syntax (Outcome (..))
import System.Directory (doesFileExist)
import System.Exit (exitFailure)

data PortableCase = PortableCase
  { caseId :: Text
  , caseExpected :: Text
  , caseLayer :: Text
  , caseAuthorities :: Text
  , caseExpectedA :: Text
  , caseExpectedB :: Text
  }
  deriving (Eq, Show)

data PortableSurface = PortableSurface
  { surfaceFixtureId :: Text
  , surfaceRole :: Text
  , surfaceMachineShape :: Text
  , surfaceInterfaceRevision :: Text
  , surfaceTransitionKind :: Text
  , surfaceSuccessorRevision :: Text
  , surfaceSuccessorState :: Text
  }
  deriving (Eq, Ord, Show)

data PortableAuthorityRequirement = PortableAuthorityRequirement
  { authorityFixtureId :: Text
  , authorityRole :: Text
  , authorityRequirement :: Text
  }
  deriving (Eq, Ord, Show)

data PortableEffect = PortableEffect
  { effectFixtureId :: Text
  , effectRole :: Text
  , effectName :: Text
  }
  deriving (Eq, Ord, Show)

data PortableFailure = PortableFailure
  { failureFixtureId :: Text
  , failureRole :: Text
  , failureKind :: Text
  , failureValue :: Text
  }
  deriving (Eq, Ord, Show)

data PortableAuthority = PortableAuthority
  { authorityRef :: Text
  , authorityKind :: Text
  , authorityCanonicalId :: Text
  , authorityCanonicalSource :: Text
  }
  deriving (Eq, Ord, Show)

root :: FilePath
root = "test/fixtures/phase1-negative/callable-refinement-v1"

manifestPath, surfacesPath, requirementsPath, effectsPath, failuresPath,
  authoritiesPath :: FilePath
manifestPath = root <> "/manifest.tsv"
surfacesPath = root <> "/surfaces-v1.tsv"
requirementsPath = root <> "/authority-requirements-v1.tsv"
effectsPath = root <> "/effect-bounds-v1.tsv"
failuresPath = root <> "/failures-v1.tsv"
authoritiesPath = root <> "/authority-registry-v1.tsv"

main :: IO ()
main = do
  cases <- readParsed manifestPath parseManifest "manifest"
  surfaces <- readParsed surfacesPath parseSurfaces "surfaces"
  requirements <- readParsed requirementsPath parseRequirements "authority requirements"
  effects <- readParsed effectsPath parseEffects "effect bounds"
  failures <- readParsed failuresPath parseFailures "failures"
  authorities <- readParsed authoritiesPath parseAuthorities "authority registry"
  integrity <- checkIntegrity cases surfaces requirements effects failures authorities
  results <- forM cases (replayCase surfaces requirements effects failures)
  unless (integrity && and results) exitFailure
  putStrLn
    ("PASS: INT-004 portable callable-refinement negatives ("
      <> show (length cases) <> " fixtures)")

readParsed :: FilePath -> (Text -> Either String a) -> String -> IO a
readParsed path parser label = do
  input <- TextIO.readFile path
  case parser input of
    Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> exitFailure
    Right value -> pure value

parseManifest :: Text -> Either String [PortableCase]
parseManifest = parseTable expected parseRow
  where
    expected =
      [ "fixture_id", "expect", "competent_layer", "governing_authority"
      , "expected_a", "expected_b"
      ]
    parseRow row = case row of
      [fixtureId, expectedResult, layer, authorities, a, b]
        | all (not . Text.null) row ->
            Right (PortableCase fixtureId expectedResult layer authorities a b)
      _ -> Left ("invalid manifest row: " <> show row)

parseSurfaces :: Text -> Either String [PortableSurface]
parseSurfaces = parseTable expected parseRow
  where
    expected =
      [ "fixture_id", "role", "machine_shape", "interface_revision"
      , "transition_kind", "successor_revision", "successor_state"
      ]
    parseRow row = case row of
      [fixtureId, role, shape, revision, transition, successorRevision, successorState]
        | all (not . Text.null) row -> Right
            (PortableSurface fixtureId role shape revision transition successorRevision successorState)
      _ -> Left ("invalid surface row: " <> show row)

parseRequirements :: Text -> Either String [PortableAuthorityRequirement]
parseRequirements = parseTable
  ["fixture_id", "role", "requirement"] parseRow
  where
    parseRow row = case row of
      [fixtureId, role, requirement]
        | all (not . Text.null) row ->
            Right (PortableAuthorityRequirement fixtureId role requirement)
      _ -> Left ("invalid authority-requirement row: " <> show row)

parseEffects :: Text -> Either String [PortableEffect]
parseEffects = parseTable ["fixture_id", "role", "effect"] parseRow
  where
    parseRow row = case row of
      [fixtureId, role, effect]
        | all (not . Text.null) row -> Right (PortableEffect fixtureId role effect)
      _ -> Left ("invalid effect row: " <> show row)

parseFailures :: Text -> Either String [PortableFailure]
parseFailures = parseTable
  ["fixture_id", "role", "failure_kind", "failure_value"] parseRow
  where
    parseRow row = case row of
      [fixtureId, role, kind, value]
        | all (not . Text.null) row -> Right (PortableFailure fixtureId role kind value)
      _ -> Left ("invalid failure row: " <> show row)

parseAuthorities :: Text -> Either String [PortableAuthority]
parseAuthorities = parseTable
  ["authority_ref", "authority_kind", "canonical_id", "canonical_source"] parseRow
  where
    parseRow row = case row of
      [ref, kind, canonicalId, source]
        | all (not . Text.null) row ->
            Right (PortableAuthority ref kind canonicalId source)
      _ -> Left ("invalid authority row: " <> show row)

parseTable :: [Text] -> ([Text] -> Either String a) -> Text -> Either String [a]
parseTable expectedHeader parseRow input = case Text.lines input of
  [] -> Left "empty TSV"
  header : rows
    | Text.splitOn "\t" header /= expectedHeader ->
        Left ("unexpected header: " <> Text.unpack header)
    | otherwise ->
        traverse (parseRow . Text.splitOn "\t") (filter (not . Text.null) rows)

checkIntegrity
  :: [PortableCase]
  -> [PortableSurface]
  -> [PortableAuthorityRequirement]
  -> [PortableEffect]
  -> [PortableFailure]
  -> [PortableAuthority]
  -> IO Bool
checkIntegrity cases surfaces requirements effects failures authorities = do
  let fixtureIds = map caseId cases
      fixtureDomain = Set.fromList fixtureIds
      exactCount = length cases == 6
      uniqueFixtures = Set.size fixtureDomain == length fixtureIds
      layerExact = all ((== "callable-refinement") . caseLayer) cases
      expectedVocabulary = Set.fromList (map caseExpected cases)
      expectedVocabularyExact = expectedVocabulary == Set.fromList
        [ "authority-too-strong"
        , "effect-bound-too-wide"
        , "failure-set-too-wide"
        , "transition-incompatible"
        , "machine-shape-mismatch"
        ]
      surfaceRowsKnown = all ((`Set.member` fixtureDomain) . surfaceFixtureId) surfaces
      surfacePairsExact = all (surfacePairExact surfaces) fixtureIds
      surfaceRowsValid = all surfaceRowWellFormed surfaces
      requirementRowsValid = repeatedRowsValid fixtureDomain
        authorityFixtureId authorityRole requirements
          && uniqueRows requirements
      effectRowsValid = repeatedRowsValid fixtureDomain effectFixtureId effectRole effects
        && uniqueRows effects
      failureRowsValid = repeatedRowsValid fixtureDomain failureFixtureId failureRole failures
        && uniqueRows failures
        && all failureRowWellFormed failures
      registryRefs = Set.fromList (map authorityRef authorities)
      registryUnique = Set.size registryRefs == length authorities
      registryRowsValid = all authorityRowWellFormed authorities
      parsedRefs = traverse caseAuthorityRefs cases
      usedRefs = either (const Set.empty) (Set.fromList . concat) parsedRefs
      authorityDomainExact =
        either (const False) (const True) parsedRefs && usedRefs == registryRefs
      certifiedPaths =
        [ Text.unpack (authorityCanonicalSource authority)
        | authority <- authorities
        , authorityKind authority == "certified"
        ]
  certifiedPresent <- and <$> mapM doesFileExist certifiedPaths
  report "six CALL-012 negative fixtures are manifest-owned" exactCount
  report "portable fixture identities are unique" uniqueFixtures
  report "competent layer is callable-refinement" layerExact
  report "portable rejection vocabulary is exact" expectedVocabularyExact
  report "surface rows reference declared fixtures" surfaceRowsKnown
  report "every fixture has exactly expected and actual surfaces" surfacePairsExact
  report "portable surface vocabulary is valid" surfaceRowsValid
  report "authority requirement rows are valid and unique" requirementRowsValid
  report "effect rows are valid and unique" effectRowsValid
  report "failure rows are valid and unique" failureRowsValid
  report "authority registry is unique and well formed" (registryUnique && registryRowsValid)
  report "manifest authority domain resolves exactly" authorityDomainExact
  report "every Certified authority proof artifact exists" certifiedPresent
  pure (and
    [ exactCount
    , uniqueFixtures
    , layerExact
    , expectedVocabularyExact
    , surfaceRowsKnown
    , surfacePairsExact
    , surfaceRowsValid
    , requirementRowsValid
    , effectRowsValid
    , failureRowsValid
    , registryUnique
    , registryRowsValid
    , authorityDomainExact
    , certifiedPresent
    ])

surfacePairExact :: [PortableSurface] -> Text -> Bool
surfacePairExact surfaces fixtureId =
  let rows = filter ((== fixtureId) . surfaceFixtureId) surfaces
  in length rows == 2
      && Set.fromList (map surfaceRole rows) == Set.fromList ["expected", "actual"]

surfaceRowWellFormed :: PortableSurface -> Bool
surfaceRowWellFormed row =
  validRole (surfaceRole row)
    && not (Text.null (surfaceMachineShape row))
    && not (Text.null (surfaceInterfaceRevision row))
    && case surfaceTransitionKind row of
      "preserve" -> surfaceSuccessorRevision row == "-" && surfaceSuccessorState row == "-"
      "consume" -> surfaceSuccessorRevision row == "-" && surfaceSuccessorState row == "-"
      "replace" -> surfaceSuccessorRevision row /= "-"
      _ -> False

failureRowWellFormed :: PortableFailure -> Bool
failureRowWellFormed row =
  validRole (failureRole row)
    && failureKind row `elem` ["typed-negative", "declared-terminal", "fatal"]
    && not (Text.null (failureValue row))

repeatedRowsValid :: Set.Set Text -> (a -> Text) -> (a -> Text) -> [a] -> Bool
repeatedRowsValid fixtureDomain fixtureOf roleOf =
  all (\row -> fixtureOf row `Set.member` fixtureDomain && validRole (roleOf row))

uniqueRows :: Ord a => [a] -> Bool
uniqueRows rows = Set.size (Set.fromList rows) == length rows

validRole :: Text -> Bool
validRole role = role == "expected" || role == "actual"

authorityRowWellFormed :: PortableAuthority -> Bool
authorityRowWellFormed authority =
  authorityKind authority `elem` ["matrix", "certified"]
    && authorityRef authority
      == authorityKind authority <> ":" <> authorityCanonicalId authority
    && authorityCanonicalId authority /= "INT-004"
    && case authorityKind authority of
      "matrix" -> authorityCanonicalSource authority == "Phil Phase 1 Conformance Matrix"
      "certified" ->
        "proof/" `Text.isPrefixOf` authorityCanonicalSource authority
          && ".v" `Text.isSuffixOf` authorityCanonicalSource authority
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
          | kind `elem` ["matrix", "certified"]
              && not (Text.null canonicalId)
              && canonicalId /= "INT-004" -> Right ref
        _ -> Left ("invalid authority reference: " <> Text.unpack ref)

replayCase
  :: [PortableSurface]
  -> [PortableAuthorityRequirement]
  -> [PortableEffect]
  -> [PortableFailure]
  -> PortableCase
  -> IO Bool
replayCase surfaces requirements effects failures portableCase = do
  let fixture = caseId portableCase
      result = do
        expected <- materializeSurface fixture "expected" surfaces requirements effects failures
        actual <- materializeSurface fixture "actual" surfaces requirements effects failures
        case checkCallableRefinement expected actual of
          Left err -> matchExpected portableCase err
          Right _ -> Left "portable callable-refinement negative unexpectedly accepted"
  case result of
    Right () -> putStrLn ("PASS: " <> Text.unpack fixture) >> pure True
    Left detail -> putStrLn ("FAIL: " <> Text.unpack fixture <> " -- " <> detail) >> pure False

materializeSurface
  :: Text
  -> Text
  -> [PortableSurface]
  -> [PortableAuthorityRequirement]
  -> [PortableEffect]
  -> [PortableFailure]
  -> Either String CallableRefinementSurface
materializeSurface fixture role surfaces requirements effects failures = do
  surface <- case filter
      (\row -> surfaceFixtureId row == fixture && surfaceRole row == role) surfaces of
    [row] -> Right row
    _ -> Left "fixture must have exactly one surface row per role"
  transition <- materializeTransition surface
  failureSet <- Set.fromList <$> traverse materializeFailure
    [ row
    | row <- failures
    , failureFixtureId row == fixture
    , failureRole row == role
    ]
  let authoritySet = Set.fromList
        [ CallableAuthorityRequirement (authorityRequirement row)
        | row <- requirements
        , authorityFixtureId row == fixture
        , authorityRole row == role
        ]
      effectSet = Set.fromList
        [ SemanticEffect (effectName row)
        | row <- effects
        , effectFixtureId row == fixture
        , effectRole row == role
        ]
      contract = CallableContract
        { callableContractInterfaceRevision = InterfaceRevision (surfaceInterfaceRevision surface)
        , callableContractCalleeTransition = transition
        , callableContractEffectBound = effectSet
        }
  Right CallableRefinementSurface
    { callableRefinementMachineShape = CallableMachineShape (surfaceMachineShape surface)
    , callableRefinementContract = contract
    , callableRefinementCallerAuthority = authoritySet
    , callableRefinementFailures = failureSet
    }

materializeTransition :: PortableSurface -> Either String CalleeTransition
materializeTransition surface = case surfaceTransitionKind surface of
  "preserve"
    | surfaceSuccessorRevision surface == "-" && surfaceSuccessorState surface == "-" ->
        Right PreserveCallee
  "consume"
    | surfaceSuccessorRevision surface == "-" && surfaceSuccessorState surface == "-" ->
        Right ConsumeCallee
  "replace"
    | surfaceSuccessorRevision surface /= "-" -> Right
        (ReplaceCallee
          (InterfaceRevision (surfaceSuccessorRevision surface))
          (if surfaceSuccessorState surface == "-"
            then Nothing
            else Just (CallableStateKey (surfaceSuccessorState surface))))
  other -> Left ("unsupported or malformed callee transition: " <> Text.unpack other)

materializeFailure :: PortableFailure -> Either String CallableFailure
materializeFailure row = case failureKind row of
  "typed-negative" -> Right (CallableTypedNegative (Outcome (failureValue row)))
  "declared-terminal" -> Right (CallableDeclaredTerminal (Outcome (failureValue row)))
  "fatal" -> Right (CallableFatal (failureValue row))
  other -> Left ("unsupported failure kind: " <> Text.unpack other)

matchExpected :: PortableCase -> CallableRefinementError -> Either String ()
matchExpected portableCase err = case (caseExpected portableCase, err) of
  ("authority-too-strong", CallableAuthorityRequirementTooStrong excess) ->
    case Set.toList excess of
      [CallableAuthorityRequirement requirement] ->
        compareFields portableCase [requirement, "-"]
      _ -> Left ("unexpected authority excess: " <> show excess)
  ("effect-bound-too-wide", CallableEffectBoundTooWide excess) ->
    case Set.toList excess of
      [SemanticEffect effect] -> compareFields portableCase [effect, "-"]
      _ -> Left ("unexpected effect excess: " <> show excess)
  ("failure-set-too-wide", CallableFailureSetTooWide excess) ->
    case Set.toList excess of
      [CallableFatal detail] -> compareFields portableCase ["fatal", detail]
      [CallableTypedNegative (Outcome outcome)] ->
        compareFields portableCase ["typed-negative", outcome]
      [CallableDeclaredTerminal (Outcome outcome)] ->
        compareFields portableCase ["declared-terminal", outcome]
      _ -> Left ("unexpected failure excess: " <> show excess)
  ("transition-incompatible", CallableCalleeTransitionIncompatible expected actual) ->
    compareFields portableCase [renderTransition expected, renderTransition actual]
  ("machine-shape-mismatch", CallableMachineShapeMismatch expected actual) ->
    compareFields portableCase
      [unCallableMachineShape expected, unCallableMachineShape actual]
  _ -> Left ("unexpected callable-refinement rejection: " <> show err)

compareFields :: PortableCase -> [Text] -> Either String ()
compareFields portableCase actual =
  let expected = [caseExpectedA portableCase, caseExpectedB portableCase]
  in if actual == expected
      then Right ()
      else Left
        ("diagnostic payload mismatch: expected " <> show expected <> ", got " <> show actual)

renderTransition :: CalleeTransition -> Text
renderTransition transition = case transition of
  PreserveCallee -> "preserve"
  ConsumeCallee -> "consume"
  ReplaceCallee (InterfaceRevision revision) state ->
    "replace:" <> revision <> ":" <> maybe "-" unCallableStateKey state

report :: String -> Bool -> IO ()
report label condition =
  putStrLn ((if condition then "PASS: " else "FAIL: ") <> label)
