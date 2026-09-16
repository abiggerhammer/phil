{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (forM, unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Data.Text (Text)
import qualified Data.Text.IO as TextIO
import Phil.Core.Callable
import Phil.Core.CallableQualification
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
  deriving (Eq, Ord, Show)

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
  { requirementFixtureId :: Text
  , requirementRole :: Text
  , requirementName :: Text
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

data PortableArtifactBinding = PortableArtifactBinding
  { artifactFixtureId :: Text
  , artifactKey :: Text
  , artifactQualificationPresent :: Bool
  , artifactQualificationKey :: Text
  }
  deriving (Eq, Ord, Show)

data PortableEvidence = PortableEvidence
  { evidenceFixtureId :: Text
  , evidenceKind :: Text
  , evidenceValue :: Text
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
root = "test/fixtures/phase1-negative/foreign-callable-v1"

manifestPath, surfacesPath, requirementsPath, effectsPath, failuresPath,
  artifactsPath, evidencePath, authoritiesPath :: FilePath
manifestPath = root <> "/manifest.tsv"
surfacesPath = root <> "/surfaces-v1.tsv"
requirementsPath = root <> "/authority-requirements-v1.tsv"
effectsPath = root <> "/effect-bounds-v1.tsv"
failuresPath = root <> "/failures-v1.tsv"
artifactsPath = root <> "/artifacts-v1.tsv"
evidencePath = root <> "/evidence-v1.tsv"
authoritiesPath = root <> "/authority-registry-v1.tsv"

main :: IO ()
main = do
  cases <- readParsed manifestPath parseManifest "manifest"
  surfaces <- readParsed surfacesPath parseSurfaces "surfaces"
  requirements <- readParsed requirementsPath parseRequirements "authority requirements"
  effects <- readParsed effectsPath parseEffects "effect bounds"
  failures <- readParsed failuresPath parseFailures "failures"
  artifacts <- readParsed artifactsPath parseArtifacts "artifacts"
  evidence <- readParsed evidencePath parseEvidence "evidence"
  authorities <- readParsed authoritiesPath parseAuthorities "authority registry"
  integrity <- checkIntegrity
    cases surfaces requirements effects failures artifacts evidence authorities
  results <- forM cases
    (replayCase surfaces requirements effects failures artifacts evidence)
  unless (integrity && and results) exitFailure
  putStrLn
    ("PASS: INT-004 portable foreign-callable negatives ("
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

parseArtifacts :: Text -> Either String [PortableArtifactBinding]
parseArtifacts = parseTable
  ["fixture_id", "artifact_key", "qualification_present", "qualification_artifact_key"] parseRow
  where
    parseRow row = case row of
      [fixtureId, key, present, qualificationKey]
        | all (not . Text.null) row -> do
            presentValue <- parseBool present
            Right (PortableArtifactBinding fixtureId key presentValue qualificationKey)
      _ -> Left ("invalid artifact row: " <> show row)

parseEvidence :: Text -> Either String [PortableEvidence]
parseEvidence = parseTable
  ["fixture_id", "evidence_kind", "evidence_value"] parseRow
  where
    parseRow row = case row of
      [fixtureId, kind, value]
        | all (not . Text.null) row -> Right (PortableEvidence fixtureId kind value)
      _ -> Left ("invalid evidence row: " <> show row)

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

parseBool :: Text -> Either String Bool
parseBool value = case value of
  "true" -> Right True
  "false" -> Right False
  _ -> Left ("invalid boolean: " <> Text.unpack value)

checkIntegrity
  :: [PortableCase]
  -> [PortableSurface]
  -> [PortableAuthorityRequirement]
  -> [PortableEffect]
  -> [PortableFailure]
  -> [PortableArtifactBinding]
  -> [PortableEvidence]
  -> [PortableAuthority]
  -> IO Bool
checkIntegrity cases surfaces requirements effects failures artifacts evidence authorities = do
  let fixtureIds = map caseId cases
      fixtureDomain = Set.fromList fixtureIds
      exactCount = length cases == 7
      uniqueFixtures = Set.size fixtureDomain == length fixtureIds
      layerExact = all ((== "foreign-callable-qualification") . caseLayer) cases
      expectedVocabulary = Set.fromList (map caseExpected cases)
      expectedVocabularyExact = expectedVocabulary == Set.fromList
        [ "qualification-missing"
        , "missing-evidence"
        , "artifact-mismatch"
        , "surface-mismatch"
        , "refinement-effect-too-wide"
        , "refinement-authority-too-strong"
        , "refinement-failure-too-wide"
        ]
      artifactIds = map artifactFixtureId artifacts
      artifactDomainExact =
        Set.fromList artifactIds == fixtureDomain
          && Set.size (Set.fromList artifactIds) == length artifactIds
      artifactRowsValid = all artifactRowWellFormed artifacts
      surfaceRowsKnown = all ((`Set.member` fixtureDomain) . surfaceFixtureId) surfaces
      surfaceRowsValid = all surfaceRowWellFormed surfaces
      surfaceRolesExact = all (rolesExact surfaces artifacts) fixtureIds
      setRowsValid =
        repeatedRowsValid fixtureDomain requirementFixtureId requirementRole requirements
          && repeatedRowsValid fixtureDomain effectFixtureId effectRole effects
          && repeatedRowsValid fixtureDomain failureFixtureId failureRole failures
          && uniqueRows requirements
          && uniqueRows effects
          && uniqueRows failures
          && all failureRowWellFormed failures
      evidenceRowsValid =
        all (evidenceRowWellFormed fixtureDomain) evidence && uniqueRows evidence
      evidenceOnlyForPresent = all
        (\row -> maybe False artifactQualificationPresent
          (lookupArtifact (evidenceFixtureId row) artifacts))
        evidence
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
  report "seven CALL-015 negative fixtures are manifest-owned" exactCount
  report "portable fixture identities are unique" uniqueFixtures
  report "competent layer is foreign-callable-qualification" layerExact
  report "portable rejection vocabulary is exact" expectedVocabularyExact
  report "every fixture has exactly one artifact binding" artifactDomainExact
  report "portable artifact bindings are well formed" artifactRowsValid
  report "surface rows reference declared fixtures" surfaceRowsKnown
  report "surface role domains match qualification presence" surfaceRolesExact
  report "portable surface vocabulary is valid" surfaceRowsValid
  report "authority/effect/failure rows are valid and unique" setRowsValid
  report "qualification evidence vocabulary is valid and unique" evidenceRowsValid
  report "evidence exists only for present qualifications" evidenceOnlyForPresent
  report "authority registry is unique and well formed" (registryUnique && registryRowsValid)
  report "manifest authority domain resolves exactly" authorityDomainExact
  report "every Certified authority proof artifact exists" certifiedPresent
  pure (and
    [ exactCount
    , uniqueFixtures
    , layerExact
    , expectedVocabularyExact
    , artifactDomainExact
    , artifactRowsValid
    , surfaceRowsKnown
    , surfaceRolesExact
    , surfaceRowsValid
    , setRowsValid
    , evidenceRowsValid
    , evidenceOnlyForPresent
    , registryUnique
    , registryRowsValid
    , authorityDomainExact
    , certifiedPresent
    ])

lookupArtifact :: Text -> [PortableArtifactBinding] -> Maybe PortableArtifactBinding
lookupArtifact fixture artifacts = case filter ((== fixture) . artifactFixtureId) artifacts of
  [row] -> Just row
  _ -> Nothing

rolesExact :: [PortableSurface] -> [PortableArtifactBinding] -> Text -> Bool
rolesExact surfaces artifacts fixture = case lookupArtifact fixture artifacts of
  Nothing -> False
  Just binding ->
    let roles = [surfaceRole row | row <- surfaces, surfaceFixtureId row == fixture]
        roleSet = Set.fromList roles
        expectedRoles = if artifactQualificationPresent binding
          then Set.fromList ["expected", "observed", "qualified"]
          else Set.fromList ["expected", "observed"]
    in roleSet == expectedRoles && Set.size roleSet == length roles

artifactRowWellFormed :: PortableArtifactBinding -> Bool
artifactRowWellFormed row =
  not (Text.null (artifactKey row))
    && if artifactQualificationPresent row
      then artifactQualificationKey row /= "-"
      else artifactQualificationKey row == "-"

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

evidenceRowWellFormed :: Set.Set Text -> PortableEvidence -> Bool
evidenceRowWellFormed fixtureDomain row =
  evidenceFixtureId row `Set.member` fixtureDomain
    && evidenceKind row `elem`
      [ "abi-correspondence"
      , "resource-lifecycle"
      , "effect-confinement"
      , "authority-confinement"
      , "failure-behavior"
      ]
    && not (Text.null (evidenceValue row))

repeatedRowsValid :: Set.Set Text -> (a -> Text) -> (a -> Text) -> [a] -> Bool
repeatedRowsValid fixtureDomain fixtureOf roleOf =
  all (\row -> fixtureOf row `Set.member` fixtureDomain && validRole (roleOf row))

uniqueRows :: Ord a => [a] -> Bool
uniqueRows rows = Set.size (Set.fromList rows) == length rows

validRole :: Text -> Bool
validRole role = role `elem` ["expected", "observed", "qualified"]

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
  -> [PortableArtifactBinding]
  -> [PortableEvidence]
  -> PortableCase
  -> IO Bool
replayCase surfaces requirements effects failures artifacts evidence portableCase = do
  let fixture = caseId portableCase
      result = do
        binding <- maybe (Left "fixture must have exactly one artifact binding") Right
          (lookupArtifact fixture artifacts)
        expected <- materializeSurface fixture "expected" surfaces requirements effects failures
        observed <- materializeSurface fixture "observed" surfaces requirements effects failures
        maybeQualification <- if artifactQualificationPresent binding
          then do
            qualified <- materializeSurface fixture "qualified" surfaces requirements effects failures
            evidenceMap <- materializeEvidence fixture evidence
            Right (Just ForeignCallableQualification
              { foreignQualificationArtifactKey = ForeignCallableArtifactKey
                  (artifactQualificationKey binding)
              , foreignQualificationSurface = qualified
              , foreignQualificationEvidence = evidenceMap
              })
          else Right Nothing
        let artifact = ForeignCallableArtifact
              { foreignCallableArtifactKey = ForeignCallableArtifactKey (artifactKey binding)
              , foreignCallableObservedSurface = observed
              }
        case checkForeignCallableQualification expected artifact maybeQualification of
          Left err -> matchExpected portableCase observed maybeQualification err
          Right _ -> Left "portable CALL-015 negative unexpectedly accepted"
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
    _ -> Left "fixture must have exactly one surface row per required role"
  transition <- materializeTransition surface
  failureSet <- Set.fromList <$> traverse materializeFailure
    [ row
    | row <- failures
    , failureFixtureId row == fixture
    , failureRole row == role
    ]
  let authoritySet = Set.fromList
        [ CallableAuthorityRequirement (requirementName row)
        | row <- requirements
        , requirementFixtureId row == fixture
        , requirementRole row == role
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

materializeEvidence
  :: Text
  -> [PortableEvidence]
  -> Either String (Map.Map ForeignCallableEvidenceKind Text)
materializeEvidence fixture rows = do
  entries <- traverse materialize
    [row | row <- rows, evidenceFixtureId row == fixture]
  let result = Map.fromList entries
  if Map.size result /= length entries
    then Left "duplicate qualification evidence kind"
    else Right result
  where
    materialize row = do
      kind <- parseEvidenceKind (evidenceKind row)
      Right (kind, evidenceValue row)

parseEvidenceKind :: Text -> Either String ForeignCallableEvidenceKind
parseEvidenceKind kind = case kind of
  "abi-correspondence" -> Right ForeignCallableAbiCorrespondence
  "resource-lifecycle" -> Right ForeignCallableResourceLifecycle
  "effect-confinement" -> Right ForeignCallableEffectConfinement
  "authority-confinement" -> Right ForeignCallableAuthorityConfinement
  "failure-behavior" -> Right ForeignCallableFailureBehavior
  _ -> Left ("unsupported evidence kind: " <> Text.unpack kind)

renderEvidenceKind :: ForeignCallableEvidenceKind -> Text
renderEvidenceKind kind = case kind of
  ForeignCallableAbiCorrespondence -> "abi-correspondence"
  ForeignCallableResourceLifecycle -> "resource-lifecycle"
  ForeignCallableEffectConfinement -> "effect-confinement"
  ForeignCallableAuthorityConfinement -> "authority-confinement"
  ForeignCallableFailureBehavior -> "failure-behavior"

matchExpected
  :: PortableCase
  -> CallableRefinementSurface
  -> Maybe ForeignCallableQualification
  -> ForeignCallableQualificationError
  -> Either String ()
matchExpected portableCase observed maybeQualification err =
  case (caseExpected portableCase, err) of
    ("qualification-missing", ForeignCallableQualificationMissing key) ->
      compareFields portableCase [renderArtifactKey key]
    ("missing-evidence", ForeignCallableQualificationMissingEvidence missing) ->
      compareFields portableCase
        [Text.intercalate "," (map renderEvidenceKind (Set.toAscList missing))]
    ("artifact-mismatch", ForeignCallableQualificationArtifactMismatch actual qualified) ->
      compareFields portableCase [renderArtifactKey actual, renderArtifactKey qualified]
    ("surface-mismatch", ForeignCallableQualificationSurfaceMismatch actual qualified) -> do
      qualification <- maybe (Left "surface-mismatch fixture lacked qualification") Right
        maybeQualification
      if actual /= observed
        then Left "surface-mismatch diagnostic lost observed artifact surface"
        else if qualified /= foreignQualificationSurface qualification
          then Left "surface-mismatch diagnostic lost qualified surface"
          else compareFields portableCase ["observed", "qualified"]
    ( "refinement-effect-too-wide"
      , ForeignCallableQualificationRefinementError (CallableEffectBoundTooWide excess) ) ->
        case Set.toList excess of
          [SemanticEffect effect] -> compareFields portableCase [effect]
          _ -> Left "refinement effect diagnostic did not contain exactly one excess effect"
    ( "refinement-authority-too-strong"
      , ForeignCallableQualificationRefinementError
          (CallableAuthorityRequirementTooStrong excess) ) ->
        case Set.toList excess of
          [CallableAuthorityRequirement requirement] -> compareFields portableCase [requirement]
          _ -> Left "refinement authority diagnostic did not contain exactly one excess requirement"
    ( "refinement-failure-too-wide"
      , ForeignCallableQualificationRefinementError (CallableFailureSetTooWide excess) ) ->
        case Set.toList excess of
          [CallableFatal detail] -> compareFields portableCase ["fatal", detail]
          _ -> Left "refinement failure diagnostic did not contain exactly one fatal failure"
    _ -> Left ("unexpected CALL-015 rejection: " <> show err)

renderArtifactKey :: ForeignCallableArtifactKey -> Text
renderArtifactKey (ForeignCallableArtifactKey key) = key

compareFields :: PortableCase -> [Text] -> Either String ()
compareFields portableCase actual =
  let expected = filter (/= "-") [caseExpectedA portableCase, caseExpectedB portableCase]
  in if actual == expected
      then Right ()
      else Left
        ("diagnostic payload mismatch: expected " <> show expected <> ", got " <> show actual)

report :: String -> Bool -> IO ()
report label condition =
  putStrLn ((if condition then "PASS: " else "FAIL: ") <> label)
