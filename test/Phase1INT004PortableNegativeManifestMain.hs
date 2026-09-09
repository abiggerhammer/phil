{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (forM, unless, when)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Text as Text
import Data.Text (Text)
import qualified Data.Text.IO as TextIO
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
  ( Branch (..)
  , GrammarId (..)
  , Mode (..)
  , Name (..)
  , Outcome (..)
  , Session (..)
  , Ty (..)
  )
import Phil.Surface.Check
  ( InitialBinding (..)
  , PrimitiveSemantics (..)
  , RejectionClass (..)
  , SurfaceCheckError (..)
  , SurfaceEnvironment (..)
  , SurfaceShape (..)
  , checkSurfaceComponent
  , emptySurfaceEnvironment
  )
import Phil.Surface.Parser (parseSurfaceFile)
import Phil.Surface.Phase0
  ( FixtureExpectation (..)
  , phase0EnvironmentFor
  , phase0ExpectationFor
  )
import Phil.Surface.Syntax (SurfaceFile (..))
import System.Directory (doesFileExist)
import System.Exit (exitFailure)
import System.Timeout (timeout)

data NegativeCase = NegativeCase
  { negativeCaseId :: Text
  , negativeCasePath :: FilePath
  , negativeCaseExpectedClass :: RejectionClass
  , negativeCaseLayer :: Text
  , negativeCaseEnvironmentProfile :: Text
  , negativeCaseAuthority :: Text
  }
  deriving (Eq, Show)

data PortableEnvironmentProfile = PortableEnvironmentProfile
  { portableProfileId :: Text
  , portableBindingName :: Text
  , portableBindingMode :: Text
  , portableSessionKind :: Text
  , portableMessageName :: Text
  , portableMessageType :: Text
  , portableTerminalOutcome :: Text
  , portableBranches :: Text
  , portablePrimitiveBindings :: Text
  , portableLegacyReceiveFrameRaw :: Text
  }
  deriving (Eq, Show)

manifestPath :: FilePath
manifestPath = "test/fixtures/phase1-negative/manifest.tsv"

environmentProfilesPath :: FilePath
environmentProfilesPath = "test/fixtures/phase1-negative/environment-profiles-v1.tsv"

seedPortableProfiles :: Set Text
seedPortableProfiles = Set.fromList
  [ "phase0.simple-receive"
  , "phase0.wrong-order"
  , "phase0.nonexhaustive-offer"
  , "phase0.legacy-raw"
  , "phase0.failure-reuse"
  ]

seedPortableFixtures :: Set Text
seedPortableFixtures = Set.fromList
  [ "P1-NEG-P0-001"
  , "P1-NEG-P0-002"
  , "P1-NEG-P0-003"
  , "P1-NEG-P0-004"
  , "P1-NEG-P0-005"
  , "P1-NEG-P0-009"
  ]

main :: IO ()
main = do
  manifest <- TextIO.readFile manifestPath
  cases <- case parseManifest manifest of
    Left detail -> putStrLn ("FAIL: manifest -- " <> detail) >> exitFailure
    Right value -> pure value
  profileText <- TextIO.readFile environmentProfilesPath
  profiles <- case parseEnvironmentProfiles profileText of
    Left detail -> putStrLn ("FAIL: environment profiles -- " <> detail) >> exitFailure
    Right value -> pure value
  integrityOk <- checkIntegrity profiles cases
  results <- forM cases (replayCase profiles)
  unless (integrityOk && and results) exitFailure
  putStrLn ("PASS: INT-004 portable frozen negative manifest (" <> show (length cases) <> " fixtures)")

parseManifest :: Text -> Either String [NegativeCase]
parseManifest input = case Text.lines input of
  [] -> Left "empty manifest"
  header : rows
    | header /= expectedHeader -> Left ("unexpected header: " <> Text.unpack header)
    | otherwise -> traverse parseRow (filter (not . Text.null) rows)
  where
    expectedHeader = Text.intercalate "\t"
      [ "fixture_id"
      , "path"
      , "expect"
      , "competent_layer"
      , "environment_profile"
      , "governing_authority"
      ]

parseRow :: Text -> Either String NegativeCase
parseRow row = case Text.splitOn "\t" row of
  [fixtureId, path, expected, layer, environmentProfile, authority] -> do
    rejectionClass <- parseRejectionClass expected
    if any Text.null [fixtureId, path, layer, environmentProfile, authority]
      then Left ("empty required field: " <> Text.unpack row)
      else Right NegativeCase
        { negativeCaseId = fixtureId
        , negativeCasePath = Text.unpack path
        , negativeCaseExpectedClass = rejectionClass
        , negativeCaseLayer = layer
        , negativeCaseEnvironmentProfile = environmentProfile
        , negativeCaseAuthority = authority
        }
  _ -> Left ("invalid TSV row: " <> Text.unpack row)

parseRejectionClass :: Text -> Either String RejectionClass
parseRejectionClass value = case value of
  "structural-use" -> Right StructuralUse
  "linear-completion" -> Right LinearCompletion
  "session-action" -> Right SessionAction
  "branch-exhaustiveness" -> Right BranchExhaustiveness
  "illegal-projection" -> Right IllegalProjection
  "missing-evidence" -> Right MissingEvidence
  "explicit-transport" -> Right ExplicitTransport
  "incompatible-branch-residue" -> Right IncompatibleBranchResidue
  "control-after-terminal" -> Right ControlAfterTerminal
  "recognition-provenance" -> Right RecognitionProvenance
  "borrow-escape" -> Right BorrowEscape
  "opaque-proof" -> Right OpaqueProof
  "unchecked-arithmetic" -> Right UncheckedArithmetic
  _ -> Left ("unknown portable rejection class: " <> Text.unpack value)

parseEnvironmentProfiles :: Text -> Either String (Map Text PortableEnvironmentProfile)
parseEnvironmentProfiles input = case Text.lines input of
  [] -> Left "empty environment profile file"
  header : rows
    | header /= expectedHeader -> Left ("unexpected environment header: " <> Text.unpack header)
    | otherwise -> do
        parsed <- traverse parseEnvironmentRow (filter (not . Text.null) rows)
        let profiles = Map.fromList [(portableProfileId profile, profile) | profile <- parsed]
        if Map.size profiles /= length parsed
          then Left "duplicate portable environment profile id"
          else Right profiles
  where
    expectedHeader = Text.intercalate "\t"
      [ "profile_id"
      , "binding_name"
      , "binding_mode"
      , "session_kind"
      , "message_name"
      , "message_type"
      , "terminal_outcome"
      , "branches"
      , "primitive_bindings"
      , "legacy_receive_frame_raw"
      ]

parseEnvironmentRow :: Text -> Either String PortableEnvironmentProfile
parseEnvironmentRow row = case Text.splitOn "\t" row of
  [profileId, bindingName, bindingMode, sessionKind, messageName, messageType, terminalOutcome, branches, primitiveBindings, legacyReceiveFrameRaw]
    | any Text.null [profileId, bindingName, bindingMode, sessionKind, messageName, messageType, terminalOutcome, branches, primitiveBindings, legacyReceiveFrameRaw] ->
        Left ("empty portable environment field: " <> Text.unpack row)
    | otherwise -> Right PortableEnvironmentProfile
        { portableProfileId = profileId
        , portableBindingName = bindingName
        , portableBindingMode = bindingMode
        , portableSessionKind = sessionKind
        , portableMessageName = messageName
        , portableMessageType = messageType
        , portableTerminalOutcome = terminalOutcome
        , portableBranches = branches
        , portablePrimitiveBindings = primitiveBindings
        , portableLegacyReceiveFrameRaw = legacyReceiveFrameRaw
        }
  _ -> Left ("invalid portable environment TSV row: " <> Text.unpack row)

materializePortableProfile :: PortableEnvironmentProfile -> Either Text SurfaceEnvironment
materializePortableProfile profile = do
  mode <- parsePortableMode (portableBindingMode profile)
  session <- parsePortableSession profile
  primitives <- parsePrimitiveBindings (portablePrimitiveBindings profile)
  legacyReceiveFrameRaw <- parsePortableBool
    "legacy_receive_frame_raw"
    (portableLegacyReceiveFrameRaw profile)
  let binding = InitialBinding mode (TyEndpoint session) PlainShape
  pure (emptySurfaceEnvironment emptyStaticContext)
    { surfaceInitialBindings = Map.singleton (portableBindingName profile) binding
    , surfacePrimitives = primitives
    , surfaceLegacyReceiveFrameRaw = legacyReceiveFrameRaw
    }

parsePortableMode :: Text -> Either Text Mode
parsePortableMode value = case value of
  "linear" -> Right Linear
  "affine" -> Right Affine
  "unrestricted" -> Right Unrestricted
  _ -> Left ("unknown portable binding mode: " <> value)

parsePortableBool :: Text -> Text -> Either Text Bool
parsePortableBool field value = case value of
  "true" -> Right True
  "false" -> Right False
  _ -> Left ("invalid portable boolean for " <> field <> ": " <> value)

parsePortableSession :: PortableEnvironmentProfile -> Either Text Session
parsePortableSession profile = case portableSessionKind profile of
  "receive" -> do
    messageName <- requireValue "message_name" (portableMessageName profile)
    messageType <- parsePortableType (portableMessageType profile)
    terminal <- requireValue "terminal_outcome" (portableTerminalOutcome profile)
    requireDash "branches" (portableBranches profile)
    pure (Receive (Name messageName) messageType (End (Outcome terminal)))
  "offer" -> do
    requireDash "message_name" (portableMessageName profile)
    requireDash "message_type" (portableMessageType profile)
    requireDash "terminal_outcome" (portableTerminalOutcome profile)
    branches <- parsePortableBranches (portableBranches profile)
    pure (Offer branches)
  other -> Left ("unknown portable session kind: " <> other)

parsePortableType :: Text -> Either Text Ty
parsePortableType value
  | Just name <- Text.stripPrefix "opaque:" value
  , not (Text.null name) = Right (TyOpaque name)
  | Just grammar <- Text.stripPrefix "frame:" value
  , not (Text.null grammar) = Right (TyFrame (GrammarId grammar))
  | otherwise = Left ("unsupported portable message type: " <> value)

parsePortableBranches :: Text -> Either Text [Branch]
parsePortableBranches value
  | value == "-" = Left "offer session requires at least one branch"
  | otherwise = do
      branches <- traverse parseBranch (Text.splitOn ";" value)
      let labels = [label | Branch label _ _ <- branches]
      if Set.size (Set.fromList labels) /= length labels
        then Left "duplicate portable offer branch label"
        else Right branches
  where
    parseBranch branchText = case Text.splitOn ":" branchText of
      [label, outcome]
        | not (Text.null label) && not (Text.null outcome) ->
            Right (Branch label Nothing (End (Outcome outcome)))
      _ -> Left ("invalid portable offer branch: " <> branchText)

parsePrimitiveBindings :: Text -> Either Text (Map Text PrimitiveSemantics)
parsePrimitiveBindings value
  | value == "-" = Right Map.empty
  | otherwise = do
      bindings <- traverse parsePrimitive (Text.splitOn ";" value)
      let result = Map.fromList bindings
      if Map.size result /= length bindings
        then Left "duplicate portable primitive binding name"
        else Right result
  where
    parsePrimitive entry = case Text.splitOn ":" entry of
      [name, "handle-payload"] | not (Text.null name) -> Right (name, PrimitiveHandlePayload)
      _ -> Left ("unsupported portable primitive binding: " <> entry)

requireValue :: Text -> Text -> Either Text Text
requireValue field value
  | value == "-" = Left (field <> " must be populated")
  | otherwise = Right value

requireDash :: Text -> Text -> Either Text ()
requireDash field value
  | value == "-" = Right ()
  | otherwise = Left (field <> " must be '-' for this session kind")

resolveProfileEnvironment
  :: Map Text PortableEnvironmentProfile
  -> Text
  -> Either Text SurfaceEnvironment
resolveProfileEnvironment profiles profile =
  case Map.lookup profile profiles of
    Just portable -> materializePortableProfile portable
    Nothing
      | Set.member profile seedPortableProfiles ->
          Left ("seed profile missing portable environment material: " <> profile)
      | otherwise -> legacyProfileEnvironment profile

-- Remaining frozen profiles still use a compatibility adapter while their
-- environment material is migrated in later INT-004 slices. Seed profiles are
-- deliberately absent here so they cannot silently fall back to filenames.
legacyProfileEnvironment :: Text -> Either Text SurfaceEnvironment
legacyProfileEnvironment profile =
  case profile of
    "phase0.parsed-validation-bypass" -> legacy "06-parsed-used-as-validated.phil"
    "phase0.unrelated-length" -> legacy "07-unrelated-payload-length.phil"
    "phase0.incompatible-join" -> legacy "08-incompatible-branch-join.phil"
    "phase0.premature-acceptance" -> legacy "10-accept-before-digest-check.phil"
    "phase0.common" -> legacy "11-copy-authority-capability.phil"
    "phase0.pending-commit" -> legacy "13-commit-unrelated-parsed.phil"
    "phase0.pending-drop" -> legacy "15-drop-pending-receive.phil"
    "phase0.stale-policy" -> legacy "17-use-evidence-wrong-context.phil"
    "phase0.opaque-proof" -> legacy "18-prove-opaque-digest.phil"
    "phase0.label-proof" -> legacy "19-label-does-not-transfer-proof.phil"
    _ -> Left ("unknown Phase-0 environment profile: " <> profile)
  where
    legacy name = phase0EnvironmentFor ("examples/rejected/" <> Text.unpack name)

checkIntegrity :: Map Text PortableEnvironmentProfile -> [NegativeCase] -> IO Bool
checkIntegrity profiles cases = do
  let ids = map negativeCaseId cases
      paths = map negativeCasePath cases
      uniqueIds = Set.size (Set.fromList ids) == length ids
      uniquePaths = Set.size (Set.fromList paths) == length paths
      exactFrozenCount = length cases == 20
      layersExact = all ((== "surface-check") . negativeCaseLayer) cases
      authoritiesPresent = all ((== "INT-004") . negativeCaseAuthority) cases
      profilesNamed = all (Text.isPrefixOf "phase0." . negativeCaseEnvironmentProfile) cases
      seedProfileDomainExact = Map.keysSet profiles == seedPortableProfiles
      seedFixturesPortable = all
        (\negativeCase ->
          not (Set.member (negativeCaseId negativeCase) seedPortableFixtures)
            || Map.member (negativeCaseEnvironmentProfile negativeCase) profiles)
        cases
      profilesResolve = all
        (either (const False) (const True)
          . resolveProfileEnvironment profiles
          . negativeCaseEnvironmentProfile)
        cases
  filesPresent <- and <$> mapM doesFileExist paths
  report "20 frozen negative fixtures are manifest-owned" exactFrozenCount
  report "stable fixture IDs are unique" uniqueIds
  report "portable fixture paths are unique" uniquePaths
  report "every fixture names surface-check as competent layer" layersExact
  report "every fixture names its governing INT-004 matrix authority" authoritiesPresent
  report "every fixture names an explicit environment profile" profilesNamed
  report "portable environment seed has exact profile domain" seedProfileDomainExact
  report "fixtures 001-005 and 009 use portable environment material" seedFixturesPortable
  report "every named environment profile resolves" profilesResolve
  report "every portable fixture path exists" filesPresent
  pure (and
    [ exactFrozenCount
    , uniqueIds
    , uniquePaths
    , layersExact
    , authoritiesPresent
    , profilesNamed
    , seedProfileDomainExact
    , seedFixturesPortable
    , profilesResolve
    , filesPresent
    ])

replayCase :: Map Text PortableEnvironmentProfile -> NegativeCase -> IO Bool
replayCase profiles negativeCase = do
  source <- TextIO.readFile (negativeCasePath negativeCase)
  let path = negativeCasePath negativeCase
      expected = negativeCaseExpectedClass negativeCase
  parityOk <- case phase0ExpectationFor path of
    Just (FixtureReject legacyClass) -> do
      let ok = legacyClass == expected
      when (not ok) $ putStrLn
        ("FAIL: " <> Text.unpack (negativeCaseId negativeCase)
          <> " -- portable manifest disagrees with frozen legacy classification")
      pure ok
    _ -> putStrLn
      ("FAIL: " <> Text.unpack (negativeCaseId negativeCase)
        <> " -- frozen legacy fixture missing during migration") >> pure False
  case resolveProfileEnvironment profiles (negativeCaseEnvironmentProfile negativeCase) of
    Left detail -> failCase ("environment profile failed: " <> Text.unpack detail)
    Right environment -> case parseSurfaceFile (Text.pack path) source of
      Left diagnostic -> failCase
        ("rejected before recorded competent layer: syntax -- " <> show diagnostic)
      Right (SurfaceFile [component]) -> do
        checked <- timeout 2000000 $ evaluate (checkSurfaceComponent environment component)
        case checked of
          Nothing -> failCase "checker did not terminate"
          Just (Right _) -> failCase
            ("expected portable rejection class " <> show expected <> ", checker accepted")
          Just (Left errorValue)
            | surfaceErrorClass errorValue == expected -> do
                putStrLn ("PASS: " <> Text.unpack (negativeCaseId negativeCase)
                  <> " " <> path <> " @ surface-check")
                pure parityOk
            | otherwise -> failCase
                ("expected " <> show expected <> ", got "
                  <> show (surfaceErrorClass errorValue) <> ": "
                  <> Text.unpack (surfaceErrorDetail errorValue))
      Right (SurfaceFile components) -> failCase
        ("unexpected component count before competent layer: " <> show (length components))
  where
    failCase detail = putStrLn
      ("FAIL: " <> Text.unpack (negativeCaseId negativeCase)
        <> " " <> negativeCasePath negativeCase <> " -- " <> detail) >> pure False

report :: String -> Bool -> IO ()
report label ok = putStrLn ((if ok then "PASS: " else "FAIL: ") <> label)
