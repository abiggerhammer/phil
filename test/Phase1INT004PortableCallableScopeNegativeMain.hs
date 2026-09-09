{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (forM, unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Data.Text (Text)
import qualified Data.Text.IO as TextIO
import Phil.Core.Callable
  ( CallableOccurrenceKey (..)
  , CaptureOccurrenceKey (..)
  )
import Phil.Core.CallableScope
import System.Directory (doesFileExist)
import System.Exit (exitFailure)

data PortableCase = PortableCase
  { caseId :: Text
  , caseCheckKind :: Text
  , caseExpected :: Text
  , caseLayer :: Text
  , caseAuthorities :: Text
  , caseExpectedPayload :: Text
  }
  deriving (Eq, Show)

data ScopeRow = ScopeRow
  { scopeFixtureId :: Text
  , scopeClosureId :: Text
  , scopeExtentKind :: Text
  , scopeExtentScope :: Text
  , scopeCaptureKind :: Text
  , scopeCaptureId :: Text
  , scopeLoanScope :: Text
  }
  deriving (Eq, Show)

data NodeRow = NodeRow
  { nodeFixtureId :: Text
  , nodeId :: Text
  , nodeRestrictedCaptures :: Text
  }
  deriving (Eq, Show)

data ReferenceRow = ReferenceRow
  { referenceFixtureId :: Text
  , referenceSource :: Text
  , referenceTarget :: Text
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
root = "test/fixtures/phase1-negative/callable-scope-v1"

manifestPath, scopePath, nodesPath, referencesPath, authoritiesPath :: FilePath
manifestPath = root <> "/manifest.tsv"
scopePath = root <> "/scope-captures-v1.tsv"
nodesPath = root <> "/recursion-nodes-v1.tsv"
referencesPath = root <> "/recursion-references-v1.tsv"
authoritiesPath = root <> "/authority-registry-v1.tsv"

main :: IO ()
main = do
  cases <- readParsed manifestPath parseManifest "manifest"
  scopeRows <- readParsed scopePath parseScopeRows "scope captures"
  nodeRows <- readParsed nodesPath parseNodeRows "recursion nodes"
  referenceRows <- readParsed referencesPath parseReferenceRows "recursion references"
  authorities <- readParsed authoritiesPath parseAuthorities "authority registry"
  integrity <- checkIntegrity cases scopeRows nodeRows referenceRows authorities
  results <- forM cases (replayCase scopeRows nodeRows referenceRows)
  unless (integrity && and results) exitFailure
  putStrLn
    ("PASS: INT-004 portable callable scope negatives ("
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
      , "governing_authority", "expected_payload"
      ]
    parseRow row = case row of
      [fixtureId, checkKind, expectedResult, layer, authorities, payload]
        | all (not . Text.null) row ->
            Right (PortableCase fixtureId checkKind expectedResult layer authorities payload)
      _ -> Left ("invalid manifest row: " <> show row)

parseScopeRows :: Text -> Either String [ScopeRow]
parseScopeRows = parseTable expected parseRow
  where
    expected =
      [ "fixture_id", "closure_id", "extent_kind", "extent_scope"
      , "capture_kind", "capture_id", "loan_scope"
      ]
    parseRow row = case row of
      [fixtureId, closureId, extentKind, extentScope, captureKind, captureId, loanScope]
        | all (not . Text.null) row -> Right
            (ScopeRow fixtureId closureId extentKind extentScope captureKind captureId loanScope)
      _ -> Left ("invalid scope-capture row: " <> show row)

parseNodeRows :: Text -> Either String [NodeRow]
parseNodeRows = parseTable expected parseRow
  where
    expected = ["fixture_id", "node_id", "restricted_captures"]
    parseRow row = case row of
      [fixtureId, closureId, restricted]
        | all (not . Text.null) row -> Right (NodeRow fixtureId closureId restricted)
      _ -> Left ("invalid recursion-node row: " <> show row)

parseReferenceRows :: Text -> Either String [ReferenceRow]
parseReferenceRows = parseTable expected parseRow
  where
    expected = ["fixture_id", "source_node", "target_node"]
    parseRow row = case row of
      [fixtureId, source, target]
        | all (not . Text.null) row -> Right (ReferenceRow fixtureId source target)
      _ -> Left ("invalid recursion-reference row: " <> show row)

parseAuthorities :: Text -> Either String [PortableAuthority]
parseAuthorities = parseTable expected parseRow
  where
    expected = ["authority_ref", "authority_kind", "canonical_id", "canonical_source"]
    parseRow row = case row of
      [ref, kind, canonicalId, source]
        | all (not . Text.null) row -> Right
            (PortableAuthority ref kind canonicalId source)
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
  -> [ScopeRow]
  -> [NodeRow]
  -> [ReferenceRow]
  -> [PortableAuthority]
  -> IO Bool
checkIntegrity cases scopeRows nodeRows referenceRows authorities = do
  let fixtureIds = map caseId cases
      fixtureDomain = Set.fromList fixtureIds
      exactCount = length cases == 6
      uniqueFixtures = Set.size fixtureDomain == length fixtureIds
      expectedKinds = Set.fromList ["scope-capture", "recursive-graph"]
      checkKindsExact = Set.fromList (map caseCheckKind cases) == expectedKinds
      layersExact = all ((== "callable-scope") . caseLayer) cases
      scopeDomain = Set.fromList (map scopeFixtureId scopeRows)
      expectedScopeDomain = Set.fromList
        [ caseId portableCase
        | portableCase <- cases
        , caseCheckKind portableCase == "scope-capture"
        ]
      scopeRowsExact = scopeDomain == expectedScopeDomain
        && length scopeRows == Set.size expectedScopeDomain
      nodeDomain = Set.fromList (map nodeFixtureId nodeRows)
      expectedNodeDomain = Set.fromList
        [ caseId portableCase
        | portableCase <- cases
        , caseCheckKind portableCase == "recursive-graph"
        ]
      nodeRowsCoverGraphs = nodeDomain == expectedNodeDomain
      referenceRowsKnown = all
        (\row -> referenceFixtureId row `Set.member` expectedNodeDomain)
        referenceRows
      semanticRowsValid =
        all scopeRowWellFormed scopeRows
          && all nodeRowWellFormed nodeRows
          && all referenceRowWellFormed referenceRows
      expectedVocabulary = Set.fromList (map caseExpected cases)
      expectedVocabularyExact = expectedVocabulary == Set.fromList
        [ "escaping-scoped-loan"
        , "outside-loan-validity"
        , "restricted-recursive-cycle"
        , "unknown-recursive-reference"
        , "duplicate-recursive-node"
        ]
      authorityMap = Map.fromList [(authorityRef authority, authority) | authority <- authorities]
      authorityUnique = Map.size authorityMap == length authorities
      authorityRowsValid = all authorityRowWellFormed authorities
      parsedRefs = traverse caseAuthorityRefs cases
      usedRefs = either (const Set.empty) (Set.fromList . concat) parsedRefs
      authorityDomainExact =
        either (const False) (const True) parsedRefs
          && usedRefs == Map.keysSet authorityMap
      certifiedPaths =
        [ Text.unpack (authorityCanonicalSource authority)
        | authority <- authorities
        , authorityKind authority == "certified"
        ]
  certifiedPresent <- and <$> mapM doesFileExist certifiedPaths
  report "six callable-scope negatives are manifest-owned" exactCount
  report "portable fixture identities are unique" uniqueFixtures
  report "portable check-kind and competent-layer vocabulary is exact"
    (checkKindsExact && layersExact)
  report "scope-capture rows cover exactly the scope fixtures" scopeRowsExact
  report "recursion nodes cover exactly the graph fixtures" nodeRowsCoverGraphs
  report "recursion references stay inside graph fixtures" referenceRowsKnown
  report "portable callable-scope vocabulary is valid" semanticRowsValid
  report "portable rejection vocabulary is exact" expectedVocabularyExact
  report "authority registry is unique and well formed" (authorityUnique && authorityRowsValid)
  report "manifest authority domain resolves exactly" authorityDomainExact
  report "every Certified authority proof artifact exists" certifiedPresent
  pure (and
    [ exactCount
    , uniqueFixtures
    , checkKindsExact
    , layersExact
    , scopeRowsExact
    , nodeRowsCoverGraphs
    , referenceRowsKnown
    , semanticRowsValid
    , expectedVocabularyExact
    , authorityUnique
    , authorityRowsValid
    , authorityDomainExact
    , certifiedPresent
    ])

scopeRowWellFormed :: ScopeRow -> Bool
scopeRowWellFormed row =
  scopeCaptureKind row == "scoped-loan"
    && scopeLoanScope row /= "-"
    && case scopeExtentKind row of
      "escaping" -> scopeExtentScope row == "-"
      "contained" -> scopeExtentScope row /= "-"
      _ -> False

nodeRowWellFormed :: NodeRow -> Bool
nodeRowWellFormed row =
  nodeId row /= "-" && validNameList (nodeRestrictedCaptures row)

referenceRowWellFormed :: ReferenceRow -> Bool
referenceRowWellFormed row =
  referenceSource row /= "-" && referenceTarget row /= "-"

validNameList :: Text -> Bool
validNameList value
  | value == "-" = True
  | otherwise = all (not . Text.null) (Text.splitOn "," value)

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
  :: [ScopeRow]
  -> [NodeRow]
  -> [ReferenceRow]
  -> PortableCase
  -> IO Bool
replayCase scopeRows nodeRows referenceRows portableCase = do
  let fixture = caseId portableCase
      result = case caseCheckKind portableCase of
        "scope-capture" -> replayScopeCase portableCase
          (filter ((== fixture) . scopeFixtureId) scopeRows)
        "recursive-graph" -> replayGraphCase portableCase
          (filter ((== fixture) . nodeFixtureId) nodeRows)
          (filter ((== fixture) . referenceFixtureId) referenceRows)
        other -> Left ("unsupported check kind: " <> Text.unpack other)
  case result of
    Right () -> putStrLn ("PASS: " <> Text.unpack fixture) >> pure True
    Left detail -> putStrLn ("FAIL: " <> Text.unpack fixture <> " -- " <> detail) >> pure False

replayScopeCase :: PortableCase -> [ScopeRow] -> Either String ()
replayScopeCase portableCase rows = do
  row <- case rows of
    [one] -> Right one
    _ -> Left "scope fixture must have exactly one portable scope row"
  extent <- materializeExtent row
  capture <- materializeScopeCapture row
  let closure = CallableOccurrenceKey (scopeClosureId row)
  case checkClosureCaptureScope closure extent [capture] of
    Left err -> matchScopeExpected portableCase err
    Right () -> Left "portable callable-scope negative unexpectedly accepted"

materializeExtent :: ScopeRow -> Either String ClosureExtent
materializeExtent row = case scopeExtentKind row of
  "escaping"
    | scopeExtentScope row == "-" -> Right EscapingClosure
  "contained"
    | scopeExtentScope row /= "-" ->
        Right (ClosureContainedIn (LoanScopeKey (scopeExtentScope row)))
  other -> Left ("unsupported or malformed closure extent: " <> Text.unpack other)

materializeScopeCapture :: ScopeRow -> Either String ClosureScopeCapture
materializeScopeCapture row = case scopeCaptureKind row of
  "scoped-loan"
    | scopeLoanScope row /= "-" -> Right
        (ScopedSharedLoanCapture
          (CaptureOccurrenceKey (scopeCaptureId row))
          (LoanScopeKey (scopeLoanScope row)))
  other -> Left ("unsupported or malformed scope capture: " <> Text.unpack other)

replayGraphCase
  :: PortableCase
  -> [NodeRow]
  -> [ReferenceRow]
  -> Either String ()
replayGraphCase portableCase rows references = do
  nodes <- traverse (materializeNode references) rows
  case checkRestrictedRecursiveClosureCycles nodes of
    Left err -> matchGraphExpected portableCase err
    Right () -> Left "portable recursive-closure negative unexpectedly accepted"

materializeNode :: [ReferenceRow] -> NodeRow -> Either String ClosureRecursionNode
materializeNode references row = do
  captures <- parseCaptureSet (nodeRestrictedCaptures row)
  let outgoing = Set.fromList
        [ CallableOccurrenceKey (referenceTarget reference)
        | reference <- references
        , referenceSource reference == nodeId row
        ]
  Right ClosureRecursionNode
    { closureRecursionOccurrence = CallableOccurrenceKey (nodeId row)
    , closureRecursionReferences = outgoing
    , closureRecursionRestrictedCaptures = captures
    }

parseCaptureSet :: Text -> Either String (Set.Set CaptureOccurrenceKey)
parseCaptureSet value
  | value == "-" = Right Set.empty
  | otherwise = do
      let names = Text.splitOn "," value
      if any Text.null names
        then Left "malformed restricted-capture list"
        else Right (Set.fromList (map CaptureOccurrenceKey names))

matchScopeExpected :: PortableCase -> CallableScopeError -> Either String ()
matchScopeExpected portableCase err = case (caseExpected portableCase, err) of
  ( "escaping-scoped-loan"
    , EscapingClosureCapturesScopedLoan
        (CallableOccurrenceKey closure)
        (CaptureOccurrenceKey capture)
        (LoanScopeKey scope) ) ->
      comparePayload portableCase [closure, capture, scope]
  ( "outside-loan-validity"
    , ClosureOutsideScopedLoanValidity
        (CallableOccurrenceKey closure)
        (CaptureOccurrenceKey capture)
        (LoanScopeKey expectedScope)
        (LoanScopeKey actualScope) ) ->
      comparePayload portableCase [closure, capture, expectedScope, actualScope]
  _ -> Left ("unexpected callable-scope rejection: " <> show err)

matchGraphExpected :: PortableCase -> CallableScopeError -> Either String ()
matchGraphExpected portableCase err = case (caseExpected portableCase, err) of
  ( "restricted-recursive-cycle"
    , RestrictedRecursiveClosureCycle closures captures ) ->
      comparePayload portableCase
        [ renderClosureSet closures
        , renderCaptureSet captures
        ]
  ( "unknown-recursive-reference"
    , UnknownRecursiveClosureReference
        (CallableOccurrenceKey source)
        (CallableOccurrenceKey target) ) ->
      comparePayload portableCase [source, target]
  ( "duplicate-recursive-node"
    , DuplicateRecursiveClosureNode (CallableOccurrenceKey closure) ) ->
      comparePayload portableCase [closure]
  _ -> Left ("unexpected recursive-closure rejection: " <> show err)

renderClosureSet :: Set.Set CallableOccurrenceKey -> Text
renderClosureSet = Text.intercalate "," . map unKey . Set.toAscList
  where
    unKey (CallableOccurrenceKey key) = key

renderCaptureSet :: Set.Set CaptureOccurrenceKey -> Text
renderCaptureSet = Text.intercalate "," . map unKey . Set.toAscList
  where
    unKey (CaptureOccurrenceKey key) = key

comparePayload :: PortableCase -> [Text] -> Either String ()
comparePayload portableCase actual =
  let expected = Text.splitOn "|" (caseExpectedPayload portableCase)
  in if expected == actual
      then Right ()
      else Left
        ("portable rejection payload mismatch: expected "
          <> show expected <> ", got " <> show actual)

report :: String -> Bool -> IO ()
report label ok = putStrLn ((if ok then "PASS: " else "FAIL: ") <> label)
