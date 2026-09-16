{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (forM, unless)
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Data.Text (Text)
import qualified Data.Text.IO as TextIO
import Phil.Core.Callable
import Phil.Core.Static (InterfaceRevision (..))
import Phil.Core.Syntax (Mode (..))
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
  } deriving (Eq, Show)

data PortableOccurrence = PortableOccurrence
  { occurrenceFixtureId :: Text
  , occurrenceDefinitionId :: Text
  , occurrenceKeyText :: Text
  , occurrenceInterface :: Text
  , occurrenceTransition :: Text
  , occurrenceSuccessorInterface :: Text
  , occurrenceSuccessorState :: Text
  , occurrenceState :: Text
  , occurrenceInitiallyAvailable :: Text
  } deriving (Eq, Show)

data PortableCapture = PortableCapture
  { captureFixtureId :: Text
  , captureDefinitionId :: Text
  , captureKeyText :: Text
  , captureTransferText :: Text
  , captureModeText :: Text
  } deriving (Eq, Show)

data PortableAction = PortableAction
  { actionFixtureId :: Text
  , actionStepText :: Text
  , actionInvokeKey :: Text
  , actionResidue :: Text
  , actionSuccessorDefinition :: Text
  } deriving (Eq, Show)

data PortableAuthority = PortableAuthority
  { authorityRef :: Text
  , authorityKind :: Text
  , authorityCanonicalId :: Text
  , authorityCanonicalSource :: Text
  } deriving (Eq, Show)

root :: FilePath
root = "test/fixtures/phase1-negative/callable-lifecycle-v1"

main :: IO ()
main = do
  cases <- readParsed (root <> "/manifest.tsv") parseManifest "manifest"
  occurrences <- readParsed (root <> "/occurrences-v1.tsv") parseOccurrences "occurrences"
  captures <- readParsed (root <> "/captures-v1.tsv") parseCaptures "captures"
  actions <- readParsed (root <> "/actions-v1.tsv") parseActions "actions"
  authorities <- readParsed (root <> "/authority-registry-v1.tsv") parseAuthorities "authorities"
  integrity <- checkIntegrity cases occurrences captures actions authorities
  results <- forM cases (replayCase occurrences captures actions)
  unless (integrity && and results) exitFailure
  putStrLn ("PASS: INT-004 portable callable-lifecycle negatives (" <> show (length cases) <> " fixtures)")

readParsed :: FilePath -> (Text -> Either String a) -> String -> IO a
readParsed path parser label = do
  input <- TextIO.readFile path
  case parser input of
    Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> exitFailure
    Right value -> pure value

parseManifest :: Text -> Either String [PortableCase]
parseManifest = parseTable
  ["fixture_id", "expect", "competent_layer", "governing_authority", "expected_a", "expected_b", "expected_c"]
  parseRow
  where
    parseRow row = case row of
      [fixture, expected, layer, authorities, a, b, c]
        | all (not . Text.null) row -> Right (PortableCase fixture expected layer authorities a b c)
      _ -> Left ("invalid manifest row: " <> show row)

parseOccurrences :: Text -> Either String [PortableOccurrence]
parseOccurrences = parseTable
  ["fixture_id", "definition_id", "occurrence_key", "interface_revision", "callee_transition", "declared_successor_interface", "declared_successor_state", "state_key", "initially_available"]
  parseRow
  where
    parseRow row = case row of
      [fixture, definitionId, key, interfaceRevision, transition, successorInterface, successorState, stateKey, initiallyAvailable]
        | all (not . Text.null) row -> Right
            (PortableOccurrence fixture definitionId key interfaceRevision transition successorInterface successorState stateKey initiallyAvailable)
      _ -> Left ("invalid occurrence row: " <> show row)

parseCaptures :: Text -> Either String [PortableCapture]
parseCaptures = parseTable
  ["fixture_id", "definition_id", "capture_key", "capture_transfer", "capture_mode"]
  parseRow
  where
    parseRow row = case row of
      [fixture, definitionId, key, transfer, mode]
        | all (not . Text.null) row -> Right (PortableCapture fixture definitionId key transfer mode)
      _ -> Left ("invalid capture row: " <> show row)

parseActions :: Text -> Either String [PortableAction]
parseActions = parseTable
  ["fixture_id", "step", "invoke_occurrence_key", "restricted_capture_residue", "successor_definition_id"]
  parseRow
  where
    parseRow row = case row of
      [fixture, step, invokeKey, residue, successorDefinition]
        | all (not . Text.null) row -> Right (PortableAction fixture step invokeKey residue successorDefinition)
      _ -> Left ("invalid action row: " <> show row)

parseAuthorities :: Text -> Either String [PortableAuthority]
parseAuthorities = parseTable
  ["authority_ref", "authority_kind", "canonical_id", "canonical_source"]
  parseRow
  where
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
  -> [PortableOccurrence]
  -> [PortableCapture]
  -> [PortableAction]
  -> [PortableAuthority]
  -> IO Bool
checkIntegrity cases occurrences captures actions authorities = do
  let fixtureIds = map caseId cases
      fixtureDomain = Set.fromList fixtureIds
      exactCount = length cases == 8
      uniqueFixtures = Set.size fixtureDomain == length fixtureIds
      layersExact = all ((== "callable-lifecycle") . caseLayer) cases
      rowFixtures = Set.fromList
        (map occurrenceFixtureId occurrences <> map captureFixtureId captures <> map actionFixtureId actions)
      rowsKnown = rowFixtures `Set.isSubsetOf` fixtureDomain
      perFixtureValid = all (fixtureRowsValid occurrences captures actions) cases
      authorityMap = Map.fromList [(authorityRef row, row) | row <- authorities]
      authorityUnique = Map.size authorityMap == length authorities
      authorityRowsValid = all authorityRowValid authorities
      parsedRefs = traverse authorityRefs cases
      usedRefs = either (const Set.empty) (Set.fromList . concat) parsedRefs
      authorityDomainExact = either (const False) (const True) parsedRefs && usedRefs == Map.keysSet authorityMap
      expectedVocabulary = Set.fromList (map caseExpected cases)
      expectedVocabularyExact = expectedVocabulary == Set.fromList
        [ "preserve-residue-mismatch"
        , "preserve-produced-successor"
        , "unavailable-callable"
        , "consume-produced-successor"
        , "replace-reused-predecessor-key"
        , "replace-interface-mismatch"
        , "replace-state-mismatch"
        ]
      certifiedPaths =
        [ Text.unpack (authorityCanonicalSource row)
        | row <- authorities
        , authorityKind row == "certified"
        ]
  certifiedPresent <- and <$> mapM doesFileExist certifiedPaths
  report "eight callable-lifecycle negatives are manifest-owned" exactCount
  report "portable fixture identities are unique" uniqueFixtures
  report "competent layer is exactly callable-lifecycle" layersExact
  report "all portable rows name manifest fixtures" rowsKnown
  report "per-fixture occurrence/capture/action domains are valid" perFixtureValid
  report "authority registry is unique and well formed" (authorityUnique && authorityRowsValid)
  report "manifest authority domain resolves exactly" authorityDomainExact
  report "every Certified authority proof artifact exists" certifiedPresent
  report "portable expected rejection vocabulary is exact" expectedVocabularyExact
  pure (and
    [ exactCount, uniqueFixtures, layersExact, rowsKnown, perFixtureValid
    , authorityUnique, authorityRowsValid, authorityDomainExact, certifiedPresent
    , expectedVocabularyExact
    ])

fixtureRowsValid
  :: [PortableOccurrence]
  -> [PortableCapture]
  -> [PortableAction]
  -> PortableCase
  -> Bool
fixtureRowsValid occurrences captures actions portableCase =
  let fixture = caseId portableCase
      occurrenceRows = filter ((== fixture) . occurrenceFixtureId) occurrences
      captureRows = filter ((== fixture) . captureFixtureId) captures
      actionRows = filter ((== fixture) . actionFixtureId) actions
      definitionIds = map occurrenceDefinitionId occurrenceRows
      definitionDomain = Set.fromList definitionIds
      definitionsUnique = Set.size definitionDomain == length definitionIds && not (null definitionIds)
      initialRows = filter ((== "true") . occurrenceInitiallyAvailable) occurrenceRows
      initialKeys = map occurrenceKeyText initialRows
      initialKeysUnique = Set.size (Set.fromList initialKeys) == length initialKeys && not (null initialRows)
      capturesKnown = all ((`Set.member` definitionDomain) . captureDefinitionId) captureRows
      actionSuccessorsKnown = all
        (\row -> actionSuccessorDefinition row == "-" || actionSuccessorDefinition row `Set.member` definitionDomain)
        actionRows
      definedOccurrenceKeys = Set.fromList (map occurrenceKeyText occurrenceRows)
      invokedKeysKnown = all ((`Set.member` definedOccurrenceKeys) . actionInvokeKey) actionRows
      parsedSteps = traverse parseStep actionRows
      stepsContiguous = case parsedSteps of
        Left _ -> False
        Right steps -> List.sort steps == [1 .. length steps] && length steps == Set.size (Set.fromList steps)
      boolsValid = all (\row -> occurrenceInitiallyAvailable row `elem` ["true", "false"]) occurrenceRows
  in definitionsUnique && initialKeysUnique && capturesKnown && actionSuccessorsKnown
      && invokedKeysKnown && stepsContiguous && boolsValid && not (null actionRows)

parseStep :: PortableAction -> Either String Int
parseStep row = case reads (Text.unpack (actionStepText row)) of
  [(value, "")] | value > 0 -> Right value
  _ -> Left "invalid action step"

authorityRowValid :: PortableAuthority -> Bool
authorityRowValid row =
  authorityKind row `elem` ["matrix", "certified"]
    && authorityRef row == authorityKind row <> ":" <> authorityCanonicalId row
    && authorityCanonicalId row /= "INT-004"
    && case authorityKind row of
      "matrix" -> authorityCanonicalSource row == "Phil Phase 1 Conformance Matrix"
      "certified" -> "proof/" `Text.isPrefixOf` authorityCanonicalSource row
        && ".v" `Text.isSuffixOf` authorityCanonicalSource row
      _ -> False

authorityRefs :: PortableCase -> Either String [Text]
authorityRefs portableCase = do
  let refs = Text.splitOn ";" (caseAuthorities portableCase)
  if null refs || any Text.null refs
    then Left "empty authority reference"
    else if length refs /= Set.size (Set.fromList refs)
      then Left "duplicate authority reference"
      else traverse validate refs
  where
    validate ref = case Text.breakOn ":" ref of
      (kind, rest) -> case Text.stripPrefix ":" rest of
        Just canonicalId
          | kind `elem` ["matrix", "certified"]
          , not (Text.null canonicalId)
          , canonicalId /= "INT-004" -> Right ref
        _ -> Left ("invalid authority reference: " <> Text.unpack ref)

replayCase
  :: [PortableOccurrence]
  -> [PortableCapture]
  -> [PortableAction]
  -> PortableCase
  -> IO Bool
replayCase occurrences captures actions portableCase = do
  let fixture = caseId portableCase
      occurrenceRows = filter ((== fixture) . occurrenceFixtureId) occurrences
      captureRows = filter ((== fixture) . captureFixtureId) captures
      actionRows = filter ((== fixture) . actionFixtureId) actions
      result = do
        definitions <- materializeDefinitions occurrenceRows captureRows
        state <- materializeInitialState occurrenceRows definitions
        orderedActions <- orderActions actionRows
        runTrace portableCase definitions state orderedActions
  case result of
    Right () -> putStrLn ("PASS: " <> Text.unpack fixture) >> pure True
    Left detail -> putStrLn ("FAIL: " <> Text.unpack fixture <> " -- " <> detail) >> pure False

materializeDefinitions
  :: [PortableOccurrence]
  -> [PortableCapture]
  -> Either String (Map.Map Text CallableOccurrence)
materializeDefinitions occurrenceRows captureRows = go Map.empty occurrenceRows
  where
    go result [] = Right result
    go result (row : rest)
      | Map.member (occurrenceDefinitionId row) result = Left "duplicate occurrence definition_id"
      | otherwise = do
          occurrence <- materializeOccurrence row
            (filter ((== occurrenceDefinitionId row) . captureDefinitionId) captureRows)
          go (Map.insert (occurrenceDefinitionId row) occurrence result) rest

materializeOccurrence :: PortableOccurrence -> [PortableCapture] -> Either String CallableOccurrence
materializeOccurrence row captures = do
  captureValues <- traverse materializeCapture captures
  captureSummary <- mapLeft show (checkClosureCaptures captureValues)
  transition <- materializeTransition row
  stateKey <- parseStateKey (occurrenceState row)
  _ <- parseBool (occurrenceInitiallyAvailable row)
  pure CallableOccurrence
    { callableOccurrenceKey = CallableOccurrenceKey (occurrenceKeyText row)
    , callableOccurrenceContract = CallableContract
        { callableContractInterfaceRevision = InterfaceRevision (occurrenceInterface row)
        , callableContractCalleeTransition = transition
        , callableContractEffectBound = Set.empty
        }
    , callableOccurrenceCaptures = captureSummary
    , callableOccurrenceStateKey = stateKey
    }

materializeCapture :: PortableCapture -> Either String ClosureCapture
materializeCapture row = do
  transfer <- case captureTransferText row of
    "copy" -> Right CopyCapture
    "move" -> Right MoveCapture
    other -> Left ("unsupported capture transfer: " <> Text.unpack other)
  mode <- case captureModeText row of
    "unrestricted" -> Right Unrestricted
    "affine" -> Right Affine
    "linear" -> Right Linear
    other -> Left ("unsupported capture mode: " <> Text.unpack other)
  pure (ClosureCapture (CaptureOccurrenceKey (captureKeyText row)) transfer mode)

materializeTransition :: PortableOccurrence -> Either String CalleeTransition
materializeTransition row = case occurrenceTransition row of
  "preserve"
    | occurrenceSuccessorInterface row == "-" && occurrenceSuccessorState row == "-" -> Right PreserveCallee
  "consume"
    | occurrenceSuccessorInterface row == "-" && occurrenceSuccessorState row == "-" -> Right ConsumeCallee
  "replace"
    | occurrenceSuccessorInterface row /= "-" ->
        ReplaceCallee (InterfaceRevision (occurrenceSuccessorInterface row))
          <$> parseStateKey (occurrenceSuccessorState row)
  other -> Left ("unsupported or malformed callee transition: " <> Text.unpack other)

parseStateKey :: Text -> Either String (Maybe CallableStateKey)
parseStateKey value
  | value == "-" = Right Nothing
  | Text.null value = Left "empty state key"
  | otherwise = Right (Just (CallableStateKey value))

parseBool :: Text -> Either String Bool
parseBool value = case value of
  "true" -> Right True
  "false" -> Right False
  _ -> Left ("invalid portable boolean: " <> Text.unpack value)

materializeInitialState
  :: [PortableOccurrence]
  -> Map.Map Text CallableOccurrence
  -> Either String CallableResourceState
materializeInitialState rows definitions = do
  initial <- traverse lookupDefinition
    [ occurrenceDefinitionId row
    | row <- rows
    , occurrenceInitiallyAvailable row == "true"
    ]
  let keyed = [(callableOccurrenceKey occurrence, occurrence) | occurrence <- initial]
  if length keyed /= Map.size (Map.fromList keyed)
    then Left "duplicate initially available occurrence key"
    else Right (CallableResourceState (Map.fromList keyed))
  where
    lookupDefinition definitionId = maybe
      (Left "missing occurrence definition") Right (Map.lookup definitionId definitions)

orderActions :: [PortableAction] -> Either String [PortableAction]
orderActions rows = do
  numbered <- traverse (\row -> (,) <$> parseStep row <*> pure row) rows
  let ordered = List.sortOn fst numbered
      steps = map fst ordered
  if steps == [1 .. length rows] && length steps == Set.size (Set.fromList steps)
    then Right (map snd ordered)
    else Left "action steps must be contiguous and unique"

runTrace
  :: PortableCase
  -> Map.Map Text CallableOccurrence
  -> CallableResourceState
  -> [PortableAction]
  -> Either String ()
runTrace _ _ _ [] = Left "negative fixture has no action"
runTrace portableCase definitions state [finalAction] = do
  body <- materializeBody definitions finalAction
  case invokeCallableOccurrence (CallableOccurrenceKey (actionInvokeKey finalAction)) body state of
    Left err -> matchExpected portableCase err
    Right _ -> Left "final negative action unexpectedly accepted"
runTrace portableCase definitions state (action : rest) = do
  body <- materializeBody definitions action
  case invokeCallableOccurrence (CallableOccurrenceKey (actionInvokeKey action)) body state of
    Left err -> Left ("unrelated early rejection before recorded final step: " <> show err)
    Right next -> runTrace portableCase definitions next rest

materializeBody
  :: Map.Map Text CallableOccurrence
  -> PortableAction
  -> Either String CallableInvocationBodySummary
materializeBody definitions action = do
  residue <- parseResidue (actionResidue action)
  successor <- if actionSuccessorDefinition action == "-"
    then Right Nothing
    else Just <$> maybe (Left "action references missing successor definition") Right
      (Map.lookup (actionSuccessorDefinition action) definitions)
  pure CallableInvocationBodySummary
    { invocationRestrictedCaptureResidue = residue
    , invocationSuccessorCallable = successor
    }

parseResidue :: Text -> Either String (Set.Set CaptureOccurrenceKey)
parseResidue value
  | value == "-" = Right Set.empty
  | otherwise = do
      let parts = Text.splitOn ";" value
      if any Text.null parts || length parts /= Set.size (Set.fromList parts)
        then Left "malformed or duplicate capture residue"
        else Right (Set.fromList (map CaptureOccurrenceKey parts))

matchExpected :: PortableCase -> CallableCheckError -> Either String ()
matchExpected portableCase err = case (caseExpected portableCase, err) of
  ("preserve-residue-mismatch", PreserveCalleeRestrictedStateMismatch (CallableOccurrenceKey key) expected actual) ->
    check [key, renderCaptureSet expected, renderCaptureSet actual]
  ("preserve-produced-successor", PreserveCalleeProducedSuccessor (CallableOccurrenceKey predecessor) (CallableOccurrenceKey successor)) ->
    check [predecessor, successor, "-"]
  ("unavailable-callable", UnavailableCallableOccurrence (CallableOccurrenceKey key)) ->
    check [key, "-", "-"]
  ("consume-produced-successor", ConsumeCalleeProducedSuccessor (CallableOccurrenceKey predecessor) (CallableOccurrenceKey successor)) ->
    check [predecessor, successor, "-"]
  ("replace-reused-predecessor-key", ReplaceCalleeReusedPredecessorKey (CallableOccurrenceKey key)) ->
    check [key, "-", "-"]
  ("replace-interface-mismatch", ReplaceCalleeInterfaceMismatch (InterfaceRevision expected) (InterfaceRevision actual)) ->
    check [expected, actual, "-"]
  ("replace-state-mismatch", ReplaceCalleeStateMismatch expected actual) ->
    check [renderState expected, renderState actual, "-"]
  _ -> Left ("unexpected callable-lifecycle rejection: " <> show err)
  where
    check actual =
      let expected = [caseExpectedA portableCase, caseExpectedB portableCase, caseExpectedC portableCase]
      in if actual == expected then Right ()
          else Left ("rejection details differ: expected " <> show expected <> ", got " <> show actual)

renderCaptureSet :: Set.Set CaptureOccurrenceKey -> Text
renderCaptureSet captures
  | Set.null captures = "-"
  | otherwise = Text.intercalate ";"
      [ key | CaptureOccurrenceKey key <- Set.toAscList captures ]

renderState :: Maybe CallableStateKey -> Text
renderState state = case state of
  Nothing -> "-"
  Just (CallableStateKey key) -> key

report :: String -> Bool -> IO ()
report label ok = putStrLn ((if ok then "PASS: " else "FAIL: ") <> label)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
