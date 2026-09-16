{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (forM, unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Data.Text (Text)
import qualified Data.Text.IO as TextIO
import Phil.Core.Callable
import Phil.Core.Callable.ModeDeclaration
import Phil.Core.Static (InterfaceRevision (..))
import Phil.Core.Syntax (Mode (..))
import System.Directory (doesFileExist)
import System.Exit (exitFailure)

data PortableCase = PortableCase
  { caseId :: Text
  , caseCheckKind :: Text
  , caseExpected :: Text
  , caseLayer :: Text
  , caseAuthorities :: Text
  , caseExpectedA :: Text
  , caseExpectedB :: Text
  }
  deriving (Eq, Show)

data PortableCapture = PortableCapture
  { captureFixtureId :: Text
  , captureOccurrence :: Text
  , captureTransfer :: Text
  , captureMode :: Text
  }
  deriving (Eq, Show)

data PortableModeDeclaration = PortableModeDeclaration
  { declarationFixtureId :: Text
  , declarationContractRevision :: Text
  , declarationMode :: Text
  , declarationJustificationKind :: Text
  , declarationJustificationRevision :: Text
  , declarationDetail :: Text
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
root = "test/fixtures/phase1-negative/callable-structural-mode-v1"

manifestPath, capturesPath, declarationsPath, authoritiesPath :: FilePath
manifestPath = root <> "/manifest.tsv"
capturesPath = root <> "/captures-v1.tsv"
declarationsPath = root <> "/mode-declarations-v1.tsv"
authoritiesPath = root <> "/authority-registry-v1.tsv"

main :: IO ()
main = do
  cases <- readParsed manifestPath parseManifest "manifest"
  captures <- readParsed capturesPath parseCaptures "captures"
  declarations <- readParsed declarationsPath parseDeclarations "mode declarations"
  authorities <- readParsed authoritiesPath parseAuthorities "authority registry"
  integrity <- checkIntegrity cases captures declarations authorities
  results <- forM cases (replayCase captures declarations)
  unless (integrity && and results) exitFailure
  putStrLn
    ("PASS: INT-004 portable callable structural-mode negatives ("
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
      [ "fixture_id", "check_kind", "expect", "competent_layer"
      , "governing_authority", "expected_a", "expected_b"
      ]
    parseRow row = case row of
      [fixtureId, checkKind, expectedResult, layer, authorities, a, b]
        | all (not . Text.null) row ->
            Right (PortableCase fixtureId checkKind expectedResult layer authorities a b)
      _ -> Left ("invalid manifest row: " <> show row)

parseCaptures :: Text -> Either String [PortableCapture]
parseCaptures = parseTable expected parseRow
  where
    expected = ["fixture_id", "occurrence_id", "transfer", "mode"]
    parseRow row = case row of
      [fixtureId, occurrence, transfer, mode]
        | all (not . Text.null) row ->
            Right (PortableCapture fixtureId occurrence transfer mode)
      _ -> Left ("invalid capture row: " <> show row)

parseDeclarations :: Text -> Either String [PortableModeDeclaration]
parseDeclarations = parseTable expected parseRow
  where
    expected =
      [ "fixture_id", "contract_revision", "declared_mode"
      , "justification_kind", "justification_revision", "detail"
      ]
    parseRow row = case row of
      [fixtureId, revision, mode, kind, justificationRevision, detail]
        | all (not . Text.null) row -> Right
            (PortableModeDeclaration
              fixtureId revision mode kind justificationRevision detail)
      _ -> Left ("invalid mode-declaration row: " <> show row)

parseAuthorities :: Text -> Either String [PortableAuthority]
parseAuthorities = parseTable expected parseRow
  where
    expected = ["authority_ref", "authority_kind", "canonical_id", "canonical_source"]
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
  -> [PortableCapture]
  -> [PortableModeDeclaration]
  -> [PortableAuthority]
  -> IO Bool
checkIntegrity cases captures declarations authorities = do
  let fixtureIds = map caseId cases
      fixtureDomain = Set.fromList fixtureIds
      exactCount = length cases == 6
      uniqueFixtures = Set.size fixtureDomain == length fixtureIds
      checkKindsExact = Set.fromList (map caseCheckKind cases)
        == Set.fromList ["capture", "mode-declaration"]
      layerKindsExact = all layerMatchesKind cases
      captureRowsKnown =
        Set.fromList (map captureFixtureId captures) `Set.isSubsetOf` fixtureDomain
      declarationIds = map declarationFixtureId declarations
      declarationDomain = Set.fromList declarationIds
      modeFixtureDomain = Set.fromList
        [caseId portableCase | portableCase <- cases, caseCheckKind portableCase == "mode-declaration"]
      declarationsExact =
        declarationDomain == modeFixtureDomain
          && Set.size declarationDomain == length declarationIds
      authorityMap = Map.fromList [(authorityRef authority, authority) | authority <- authorities]
      authorityUnique = Map.size authorityMap == length authorities
      authorityRowsValid = all authorityRowWellFormed authorities
      parsedRefs = traverse caseAuthorityRefs cases
      usedRefs = either (const Set.empty) (Set.fromList . concat) parsedRefs
      authorityDomainExact =
        either (const False) (const True) parsedRefs
          && usedRefs == Map.keysSet authorityMap
      expectedVocabulary = Set.fromList (map caseExpected cases)
      expectedVocabularyExact = expectedVocabulary == Set.fromList
        [ "restricted-capture-must-move"
        , "duplicate-restricted-capture"
        , "explicit-mode-weakens-minimum"
        , "stricter-mode-missing-justification"
        , "stricter-mode-wrong-contract"
        , "target-implementation-cannot-strengthen"
        ]
      semanticRowsValid =
        all captureRowWellFormed captures && all declarationRowWellFormed declarations
      certifiedPaths =
        [ Text.unpack (authorityCanonicalSource authority)
        | authority <- authorities
        , authorityKind authority == "certified"
        ]
  certifiedPresent <- and <$> mapM doesFileExist certifiedPaths
  report "six callable structural-mode negatives are manifest-owned" exactCount
  report "portable fixture identities are unique" uniqueFixtures
  report "portable competent-layer/check-kind pairing is exact" (checkKindsExact && layerKindsExact)
  report "capture rows reference declared fixtures" captureRowsKnown
  report "every mode-declaration fixture has exactly one declaration row" declarationsExact
  report "authority registry is unique and well formed" (authorityUnique && authorityRowsValid)
  report "manifest authority domain resolves exactly" authorityDomainExact
  report "every Certified authority proof artifact exists" certifiedPresent
  report "portable capture/declaration vocabulary is valid" semanticRowsValid
  report "portable rejection vocabulary is exact" expectedVocabularyExact
  pure (and
    [ exactCount
    , uniqueFixtures
    , checkKindsExact
    , layerKindsExact
    , captureRowsKnown
    , declarationsExact
    , authorityUnique
    , authorityRowsValid
    , authorityDomainExact
    , certifiedPresent
    , semanticRowsValid
    , expectedVocabularyExact
    ])

layerMatchesKind :: PortableCase -> Bool
layerMatchesKind portableCase = case caseCheckKind portableCase of
  "capture" -> caseLayer portableCase == "callable-capture"
  "mode-declaration" -> caseLayer portableCase == "callable-mode-declaration"
  _ -> False

captureRowWellFormed :: PortableCapture -> Bool
captureRowWellFormed row =
  captureTransfer row `elem` ["copy", "move"]
    && captureMode row `elem` ["unrestricted", "affine", "linear"]

declarationRowWellFormed :: PortableModeDeclaration -> Bool
declarationRowWellFormed row =
  declarationMode row `elem` ["unrestricted", "affine", "linear"]
    && case declarationJustificationKind row of
      "none" -> declarationJustificationRevision row == "-" && declarationDetail row == "-"
      "lifecycle" -> declarationJustificationRevision row /= "-" && declarationDetail row /= "-"
      "authority" -> declarationJustificationRevision row /= "-" && declarationDetail row /= "-"
      "target" -> declarationJustificationRevision row == "-" && declarationDetail row /= "-"
      _ -> False

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
  :: [PortableCapture]
  -> [PortableModeDeclaration]
  -> PortableCase
  -> IO Bool
replayCase captures declarations portableCase = do
  let fixture = caseId portableCase
      captureRows = filter ((== fixture) . captureFixtureId) captures
      declarationRows = filter ((== fixture) . declarationFixtureId) declarations
      result = case caseCheckKind portableCase of
        "capture" -> replayCapture portableCase captureRows
        "mode-declaration" -> replayModeDeclaration portableCase captureRows declarationRows
        other -> Left ("unsupported check kind: " <> Text.unpack other)
  case result of
    Right () -> putStrLn ("PASS: " <> Text.unpack fixture) >> pure True
    Left detail -> putStrLn ("FAIL: " <> Text.unpack fixture <> " -- " <> detail) >> pure False

replayCapture :: PortableCase -> [PortableCapture] -> Either String ()
replayCapture portableCase rows = do
  concrete <- traverse materializeCapture rows
  case checkClosureCaptures concrete of
    Left err -> matchCaptureExpected portableCase err
    Right _ -> Left "portable capture negative unexpectedly accepted"

replayModeDeclaration
  :: PortableCase
  -> [PortableCapture]
  -> [PortableModeDeclaration]
  -> Either String ()
replayModeDeclaration portableCase captureRows declarationRows = do
  concreteCaptures <- traverse materializeCapture captureRows
  captureSummary <- case checkClosureCaptures concreteCaptures of
    Left err -> Left
      ("capture setup rejected before callable-mode-declaration competence: " <> show err)
    Right summary -> Right summary
  declarationRow <- case declarationRows of
    [row] -> Right row
    _ -> Left "mode-declaration fixture must have exactly one declaration row"
  declaredMode <- parseMode (declarationMode declarationRow)
  justification <- materializeJustification declarationRow
  let contract = CallableContract
        { callableContractInterfaceRevision =
            InterfaceRevision (declarationContractRevision declarationRow)
        , callableContractCalleeTransition = PreserveCallee
        , callableContractEffectBound = Set.empty
        }
      declaration = ExplicitClosureMode declaredMode justification
  case checkClosureModeDeclaration contract captureSummary declaration of
    Left err -> matchModeExpected portableCase err
    Right _ -> Left "portable mode-declaration negative unexpectedly accepted"

materializeCapture :: PortableCapture -> Either String ClosureCapture
materializeCapture row = do
  transfer <- case captureTransfer row of
    "copy" -> Right CopyCapture
    "move" -> Right MoveCapture
    other -> Left ("unsupported capture transfer: " <> Text.unpack other)
  mode <- parseMode (captureMode row)
  Right ClosureCapture
    { closureCaptureOccurrence = CaptureOccurrenceKey (captureOccurrence row)
    , closureCaptureTransfer = transfer
    , closureCaptureStructuralMode = mode
    }

parseMode :: Text -> Either String Mode
parseMode value = case value of
  "unrestricted" -> Right Unrestricted
  "affine" -> Right Affine
  "linear" -> Right Linear
  _ -> Left ("unsupported structural mode: " <> Text.unpack value)

materializeJustification
  :: PortableModeDeclaration
  -> Either String (Maybe ClosureModeJustification)
materializeJustification row = case declarationJustificationKind row of
  "none"
    | declarationJustificationRevision row == "-" && declarationDetail row == "-" ->
        Right Nothing
  "lifecycle"
    | declarationJustificationRevision row /= "-" && declarationDetail row /= "-" ->
        Right (Just (LifecycleModeObligation
          (InterfaceRevision (declarationJustificationRevision row))
          (declarationDetail row)))
  "authority"
    | declarationJustificationRevision row /= "-" && declarationDetail row /= "-" ->
        Right (Just (AuthorityModeObligation
          (InterfaceRevision (declarationJustificationRevision row))
          (declarationDetail row)))
  "target"
    | declarationJustificationRevision row == "-" && declarationDetail row /= "-" ->
        Right (Just (TargetImplementationModeReason (declarationDetail row)))
  other -> Left ("unsupported or malformed justification kind: " <> Text.unpack other)

matchCaptureExpected :: PortableCase -> CallableCheckError -> Either String ()
matchCaptureExpected portableCase err = case (caseExpected portableCase, err) of
  ( "restricted-capture-must-move"
    , RestrictedCaptureMustMove (CaptureOccurrenceKey occurrence) mode ) ->
      assertFields [occurrence, renderMode mode]
  ( "duplicate-restricted-capture"
    , DuplicateRestrictedCapture (CaptureOccurrenceKey occurrence) mode ) ->
      assertFields [occurrence, renderMode mode]
  _ -> Left ("unexpected callable-capture rejection: " <> show err)
  where
    assertFields actual = compareExpected portableCase actual

matchModeExpected
  :: PortableCase
  -> ClosureModeDeclarationError
  -> Either String ()
matchModeExpected portableCase err = case (caseExpected portableCase, err) of
  ( "explicit-mode-weakens-minimum"
    , ExplicitClosureModeWeakensCaptureMinimum minimumMode declaredMode ) ->
      compareExpected portableCase [renderMode minimumMode, renderMode declaredMode]
  ( "stricter-mode-missing-justification"
    , StricterClosureModeMissingSemanticJustification minimumMode declaredMode ) ->
      compareExpected portableCase [renderMode minimumMode, renderMode declaredMode]
  ( "stricter-mode-wrong-contract"
    , StricterClosureModeWrongContract
        (InterfaceRevision expectedRevision)
        (InterfaceRevision actualRevision) ) ->
      compareExpected portableCase [expectedRevision, actualRevision]
  ( "target-implementation-cannot-strengthen"
    , TargetImplementationCannotStrengthenClosureMode detail ) ->
      compareExpected portableCase [detail, "-"]
  _ -> Left ("unexpected callable-mode-declaration rejection: " <> show err)

compareExpected :: PortableCase -> [Text] -> Either String ()
compareExpected portableCase actual =
  let expected = [caseExpectedA portableCase, caseExpectedB portableCase]
  in if actual == expected
      then Right ()
      else Left
        ("rejection details differ: expected " <> show expected <> ", got " <> show actual)

renderMode :: Mode -> Text
renderMode mode = case mode of
  Unrestricted -> "unrestricted"
  Affine -> "affine"
  Linear -> "linear"

report :: String -> Bool -> IO ()
report label ok = putStrLn ((if ok then "PASS: " else "FAIL: ") <> label)
