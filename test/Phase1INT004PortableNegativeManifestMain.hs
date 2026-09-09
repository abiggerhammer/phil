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

data PortableEnvironmentBinding = PortableEnvironmentBinding
  { portableExtraProfileId :: Text
  , portableExtraBindingName :: Text
  , portableExtraBindingMode :: Text
  , portableExtraBindingType :: Text
  , portableExtraBindingShape :: Text
  }
  deriving (Eq, Show)

manifestPath :: FilePath
manifestPath = "test/fixtures/phase1-negative/manifest.tsv"

environmentProfilesPath :: FilePath
environmentProfilesPath = "test/fixtures/phase1-negative/environment-profiles-v1.tsv"

environmentBindingsPath :: FilePath
environmentBindingsPath = "test/fixtures/phase1-negative/environment-bindings-v1.tsv"

seedPortableProfiles :: Set Text
seedPortableProfiles = Set.fromList
  [ "phase0.simple-receive"
  , "phase0.wrong-order"
  , "phase0.nonexhaustive-offer"
  , "phase0.legacy-raw"
  , "phase0.failure-reuse"
  , "phase0.common"
  , "phase0.incompatible-join"
  ]

seedPortableFixtures :: Set Text
seedPortableFixtures = Set.fromList
  [ "P1-NEG-P0-001"
  , "P1-NEG-P0-002"
  , "P1-NEG-P0-003"
  , "P1-NEG-P0-004"
  , "P1-NEG-P0-005"
  , "P1-NEG-P0-008"
  , "P1-NEG-P0-009"
  , "P1-NEG-P0-011"
  , "P1-NEG-P0-012"
  , "P1-NEG-P0-014"
  , "P1-NEG-P0-016"
  , "P1-NEG-P0-020"
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
  bindingText <- TextIO.readFile environmentBindingsPath
  bindings <- case parseEnvironmentBindings bindingText of
    Left detail -> putStrLn ("FAIL: environment bindings -- " <> detail) >> exitFailure
    Right value -> pure value
  integrityOk <- checkIntegrity bindings profiles cases
  results <- forM cases (replayCase bindings profiles)
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

parseEnvironmentBindings :: Text -> Either String (Map Text [PortableEnvironmentBinding])
parseEnvironmentBindings input = case Text.lines input of
  [] -> Left "empty environment binding file"
  header : rows
    | header /= expectedHeader -> Left ("unexpected binding header: " <> Text.unpack header)
    | otherwise -> do
        parsed <- traverse parseEnvironmentBindingRow (filter (not . Text.null) rows)
        let grouped = Map.fromListWith (++)
              [(portableExtraProfileId binding, [binding]) | binding <- parsed]
            names bindingsForProfile = map portableExtraBindingName bindingsForProfile
            unique bindingsForProfile =
              Set.size (Set.fromList (names bindingsForProfile)) == length bindingsForProfile
        if all unique (Map.elems grouped)
          then Right grouped
          else Left "duplicate portable extra binding name within profile"
  where
    expectedHeader = Text.intercalate "\t"
      [ "profile_id"
      , "binding_name"
      , "binding_mode"
      , "binding_type"
      , "binding_shape"
      ]

parseEnvironmentBindingRow :: Text -> Either String PortableEnvironmentBinding
parseEnvironmentBindingRow row = case Text.splitOn "\t" row of
  [profileId, bindingName, bindingMode, bindingType, bindingShape]
    | any Text.null [profileId, bindingName, bindingMode, bindingType, bindingShape] ->
        Left ("empty portable binding field: " <> Text.unpack row)
    | otherwise -> Right PortableEnvironmentBinding
        { portableExtraProfileId = profileId
        , portableExtraBindingName = bindingName
        , portableExtraBindingMode = bindingMode
        , portableExtraBindingType = bindingType
        , portableExtraBindingShape = bindingShape
        }
  _ -> Left ("invalid portable binding TSV row: " <> Text.unpack row)

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

materializePortableProfile
  :: Map Text [PortableEnvironmentBinding]
  -> PortableEnvironmentProfile
  -> Either Text SurfaceEnvironment
materializePortableProfile extraBindings profile = do
  bindings <- materializePortableBindings extraBindings profile
  primitives <- parsePrimitiveBindings (portablePrimitiveBindings profile)
  legacyReceiveFrameRaw <- parsePortableBool
    "legacy_receive_frame_raw"
    (portableLegacyReceiveFrameRaw profile)
  pure (emptySurfaceEnvironment emptyStaticContext)
    { surfaceInitialBindings = bindings
    , surfacePrimitives = primitives
    , surfaceLegacyReceiveFrameRaw = legacyReceiveFrameRaw
    }

materializePortableBindings
  :: Map Text [PortableEnvironmentBinding]
  -> PortableEnvironmentProfile
  -> Either Text (Map Text InitialBinding)
materializePortableBindings extraBindings profile = do
  primary <- case portableSessionKind profile of
    "none" -> do
      requireDash "binding_name" (portableBindingName profile)
      requireDash "binding_mode" (portableBindingMode profile)
      requireDash "message_name" (portableMessageName profile)
      requireDash "message_type" (portableMessageType profile)
      requireDash "terminal_outcome" (portableTerminalOutcome profile)
      requireDash "branches" (portableBranches profile)
      Right Map.empty
    _ -> do
      bindingName <- requireValue "binding_name" (portableBindingName profile)
      mode <- parsePortableMode (portableBindingMode profile)
      session <- parsePortableSession profile
      let binding = InitialBinding mode (TyEndpoint session) PlainShape
      Right (Map.singleton bindingName binding)
  extras <- traverse materializePortableExtraBinding
    (Map.findWithDefault [] (portableProfileId profile) extraBindings)
  let extrasMap = Map.fromList extras
  if Map.size extrasMap /= length extras
    then Left "duplicate materialized portable extra binding"
    else if not (Set.null (Map.keysSet primary `Set.intersection` Map.keysSet extrasMap))
      then Left "portable extra binding conflicts with primary binding"
      else Right (Map.union primary extrasMap)

materializePortableExtraBinding
  :: PortableEnvironmentBinding
  -> Either Text (Text, InitialBinding)
materializePortableExtraBinding binding = do
  mode <- parsePortableMode (portableExtraBindingMode binding)
  ty <- parsePortableBindingType (portableExtraBindingType binding)
  shape <- case portableExtraBindingShape binding of
    "plain" -> Right PlainShape
    other -> Left ("unsupported portable binding shape: " <> other)
  Right
    ( portableExtraBindingName binding
    , InitialBinding mode ty shape
    )

parsePortableBindingType :: Text -> Either Text Ty
parsePortableBindingType value = case value of
  "bool" -> Right TyBool
  _ -> Left ("unsupported portable binding type: " <> value)

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
  "select" -> do
    requireDash "message_name" (portableMessageName profile)
    requireDash "message_type" (portableMessageType profile)
    requireDash "terminal_outcome" (portableTerminalOutcome profile)
    branches <- parsePortableBranches (portableBranches profile)
    pure (Select branches)
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
      [name, semantic] | not (Text.null name) ->
        case semantic of
          "handle-payload" -> Right (name, PrimitiveHandlePayload)
          "authorize-store" -> Right (name, PrimitiveAuthorizeStore)
          "delegate" -> Right (name, PrimitiveDelegate)
          "new-cancellation-scope" -> Right (name, PrimitiveNewCancellationScope)
          "allocate-linear-buffer" -> Right (name, PrimitiveAllocateLinearBuffer)
          "inspect" -> Right (name, PrimitiveInspect)
          "unchecked-u32-add" -> Right (name, PrimitiveUncheckedU32Add)
          "continue-common-state" -> Right (name, PrimitiveContinueCommonState)
          _ -> Left ("unsupported portable primitive semantic: " <> semantic)
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
  :: Map Text [PortableEnvironmentBinding]
  -> Map Text PortableEnvironmentProfile
  -> Text
  -> Either Text SurfaceEnvironment
resolveProfileEnvironment bindings profiles profile =
  case Map.lookup profile profiles of
    Just portable -> materializePortableProfile bindings portable
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
    "phase0.premature-acceptance" -> legacy "10-accept-before-digest-check.phil"
    "phase0.pending-commit" -> legacy "13-commit-unrelated-parsed.phil"
    "phase0.pending-drop" -> legacy "15-drop-pending-receive.phil"
    "phase0.stale-policy" -> legacy "17-use-evidence-wrong-context.phil"
    "phase0.opaque-proof" -> legacy "18-prove-opaque-digest.phil"
    "phase0.label-proof" -> legacy "19-label-does-not-transfer-proof.phil"
    _ -> Left ("unknown Phase-0 environment profile: " <> profile)
  where
    legacy name = phase0EnvironmentFor ("examples/rejected/" <> Text.unpack name)

checkIntegrity
  :: Map Text [PortableEnvironmentBinding]
  -> Map Text PortableEnvironmentProfile
  -> [NegativeCase]
  -> IO Bool
checkIntegrity bindings profiles cases = do
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
      bindingProfilesDeclared = Map.keysSet bindings `Set.isSubsetOf` Map.keysSet profiles
      multibindingDomainExact = Map.keysSet bindings == Set.singleton "phase0.incompatible-join"
      profilesResolve = all
        (either (const False) (const True)
          . resolveProfileEnvironment bindings profiles
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
  report "portable extra bindings reference declared profiles" bindingProfilesDeclared
  report "portable extra-binding domain is exact for this slice" multibindingDomainExact
  report "fixtures 001-005, 008, 009, 011, 012, 014, 016, and 020 use portable environment material" seedFixturesPortable
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
    , bindingProfilesDeclared
    , multibindingDomainExact
    , seedFixturesPortable
    , profilesResolve
    , filesPresent
    ])

replayCase
  :: Map Text [PortableEnvironmentBinding]
  -> Map Text PortableEnvironmentProfile
  -> NegativeCase
  -> IO Bool
replayCase bindings profiles negativeCase = do
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
  case resolveProfileEnvironment bindings profiles (negativeCaseEnvironmentProfile negativeCase) of
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
