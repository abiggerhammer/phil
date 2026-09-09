{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (foldM, forM, unless, when)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Text as Text
import Data.Text (Text)
import qualified Data.Text.IO as TextIO
import Phil.Core.Static (StaticContext, declareOpaqueClaim, emptyStaticContext)
import Phil.Core.Syntax
  ( Branch (..)
  , FrameId (..)
  , GrammarId (..)
  , Mode (..)
  , Name (..)
  , Outcome (..)
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  , Session (..)
  , Ty (..)
  )
import Phil.Surface.Check
  ( FieldInfo (..)
  , InitialBinding (..)
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

data PortableEnvironmentRequirement = PortableEnvironmentRequirement
  { portableRequirementProfileId :: Text
  , portableRequirementSiteKind :: Text
  , portableRequirementSiteName :: Text
  , portableRequirementProposition :: Text
  }
  deriving (Eq, Show)

data PortableStaticClaim = PortableStaticClaim
  { portableStaticClaimName :: Text
  , portableStaticClaimDefinitionKind :: Text
  , portableStaticClaimParameters :: Text
  }
  deriving (Eq, Show)

manifestPath :: FilePath
manifestPath = "test/fixtures/phase1-negative/manifest.tsv"

environmentProfilesPath :: FilePath
environmentProfilesPath = "test/fixtures/phase1-negative/environment-profiles-v1.tsv"

environmentBindingsPath :: FilePath
environmentBindingsPath = "test/fixtures/phase1-negative/environment-bindings-v1.tsv"

environmentRequirementsPath :: FilePath
environmentRequirementsPath = "test/fixtures/phase1-negative/environment-requirements-v1.tsv"

environmentStaticClaimsPath :: FilePath
environmentStaticClaimsPath = "test/fixtures/phase1-negative/environment-static-claims-v1.tsv"

seedPortableProfiles :: Set Text
seedPortableProfiles = Set.fromList
  [ "phase0.simple-receive"
  , "phase0.wrong-order"
  , "phase0.nonexhaustive-offer"
  , "phase0.legacy-raw"
  , "phase0.failure-reuse"
  , "phase0.common"
  , "phase0.incompatible-join"
  , "phase0.parsed-validation-bypass"
  , "phase0.unrelated-length"
  , "phase0.stale-policy"
  , "phase0.opaque-proof"
  ]

seedPortableFixtures :: Set Text
seedPortableFixtures = Set.fromList
  [ "P1-NEG-P0-001"
  , "P1-NEG-P0-002"
  , "P1-NEG-P0-003"
  , "P1-NEG-P0-004"
  , "P1-NEG-P0-005"
  , "P1-NEG-P0-006"
  , "P1-NEG-P0-007"
  , "P1-NEG-P0-008"
  , "P1-NEG-P0-009"
  , "P1-NEG-P0-011"
  , "P1-NEG-P0-012"
  , "P1-NEG-P0-014"
  , "P1-NEG-P0-016"
  , "P1-NEG-P0-017"
  , "P1-NEG-P0-018"
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
  requirementText <- TextIO.readFile environmentRequirementsPath
  requirements <- case parseEnvironmentRequirements requirementText of
    Left detail -> putStrLn ("FAIL: environment requirements -- " <> detail) >> exitFailure
    Right value -> pure value
  staticClaimText <- TextIO.readFile environmentStaticClaimsPath
  staticClaims <- case parsePortableStaticClaims staticClaimText of
    Left detail -> putStrLn ("FAIL: static claims -- " <> detail) >> exitFailure
    Right value -> pure value
  staticContext <- case materializePortableStaticContext staticClaims of
    Left detail -> putStrLn ("FAIL: static context -- " <> Text.unpack detail) >> exitFailure
    Right value -> pure value
  integrityOk <- checkIntegrity staticClaims requirements bindings profiles cases
  results <- forM cases (replayCase staticContext requirements bindings profiles)
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

parseEnvironmentRequirements :: Text -> Either String (Map Text [PortableEnvironmentRequirement])
parseEnvironmentRequirements input = case Text.lines input of
  [] -> Left "empty environment requirement file"
  header : rows
    | header /= expectedHeader -> Left ("unexpected requirement header: " <> Text.unpack header)
    | otherwise -> do
        parsed <- traverse parseEnvironmentRequirementRow (filter (not . Text.null) rows)
        Right (Map.fromListWith (++)
          [(portableRequirementProfileId requirement, [requirement]) | requirement <- parsed])
  where
    expectedHeader = Text.intercalate "\t"
      [ "profile_id"
      , "site_kind"
      , "site_name"
      , "proposition"
      ]

parseEnvironmentRequirementRow :: Text -> Either String PortableEnvironmentRequirement
parseEnvironmentRequirementRow row = case Text.splitOn "\t" row of
  [profileId, siteKind, siteName, proposition]
    | any Text.null [profileId, siteKind, siteName, proposition] ->
        Left ("empty portable requirement field: " <> Text.unpack row)
    | otherwise -> Right PortableEnvironmentRequirement
        { portableRequirementProfileId = profileId
        , portableRequirementSiteKind = siteKind
        , portableRequirementSiteName = siteName
        , portableRequirementProposition = proposition
        }
  _ -> Left ("invalid portable requirement TSV row: " <> Text.unpack row)

parsePortableStaticClaims :: Text -> Either String [PortableStaticClaim]
parsePortableStaticClaims input = case Text.lines input of
  [] -> Left "empty static claim file"
  header : rows
    | header /= Text.intercalate "\t" ["claim_name", "definition_kind", "parameters"] ->
        Left ("unexpected static claim header: " <> Text.unpack header)
    | otherwise -> traverse parsePortableStaticClaimRow (filter (not . Text.null) rows)

parsePortableStaticClaimRow :: Text -> Either String PortableStaticClaim
parsePortableStaticClaimRow row = case Text.splitOn "\t" row of
  [claimName, definitionKind, parameters]
    | any Text.null [claimName, definitionKind, parameters] ->
        Left ("empty portable static claim field: " <> Text.unpack row)
    | otherwise -> Right PortableStaticClaim
        { portableStaticClaimName = claimName
        , portableStaticClaimDefinitionKind = definitionKind
        , portableStaticClaimParameters = parameters
        }
  _ -> Left ("invalid portable static claim TSV row: " <> Text.unpack row)

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
  :: StaticContext
  -> Map Text [PortableEnvironmentRequirement]
  -> Map Text [PortableEnvironmentBinding]
  -> PortableEnvironmentProfile
  -> Either Text SurfaceEnvironment
materializePortableProfile staticContext requirements extraBindings profile = do
  bindings <- materializePortableBindings extraBindings profile
  primitives <- parsePrimitiveBindings (portablePrimitiveBindings profile)
  legacyReceiveFrameRaw <- parsePortableBool
    "legacy_receive_frame_raw"
    (portableLegacyReceiveFrameRaw profile)
  (receiveExactRequirement, selectRequirements) <- materializePortableRequirements
    (Map.findWithDefault [] (portableProfileId profile) requirements)
  pure (emptySurfaceEnvironment staticContext)
    { surfaceInitialBindings = bindings
    , surfacePrimitives = primitives
    , surfaceLegacyReceiveFrameRaw = legacyReceiveFrameRaw
    , surfaceReceiveExactRequirement = receiveExactRequirement
    , surfaceSelectRequirements = selectRequirements
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
  shape <- parsePortableBindingShape
    (portableExtraBindingName binding)
    ty
    (portableExtraBindingShape binding)
  Right
    ( portableExtraBindingName binding
    , InitialBinding mode ty shape
    )

parsePortableBindingType :: Text -> Either Text Ty
parsePortableBindingType value
  | value == "bool" = Right TyBool
  | Just grammar <- Text.stripPrefix "frame:" value
  , not (Text.null grammar) = Right (TyFrame (GrammarId grammar))
  | Just rest <- Text.stripPrefix "validated:" value =
      case Text.splitOn ":" rest of
        [claim, context, subject]
          | all (not . Text.null) [claim, context, subject] ->
              Right (TyValidated claim (Name context) (Name subject))
        _ -> Left ("invalid portable validated binding type: " <> value)
  | Just rest <- Text.stripPrefix "opaque-sorted:" value =
      case Text.splitOn ":" rest of
        [name, sortEncoding] | not (Text.null name) ->
          TyOpaqueSorted name <$> parsePortableSort sortEncoding
        _ -> Left ("invalid portable sorted opaque binding type: " <> value)
  | otherwise = Left ("unsupported portable binding type: " <> value)

parsePortableSort :: Text -> Either Text RefSort
parsePortableSort value
  | value == "finite-seq-u8" = Right (SortFiniteSeq (SortUInt 8))
  | Just name <- Text.stripPrefix "opaque-" value
  , not (Text.null name) = Right (SortOpaque name)
  | Just name <- Text.stripPrefix "stable-id-" value
  , not (Text.null name) = Right (SortStableId name)
  | otherwise = Left ("unsupported portable sort: " <> value)

materializePortableStaticContext :: [PortableStaticClaim] -> Either Text StaticContext
materializePortableStaticContext claims = foldM addClaim emptyStaticContext claims
  where
    addClaim context claim = do
      parameters <- parsePortableStaticClaimParameters (portableStaticClaimParameters claim)
      case portableStaticClaimDefinitionKind claim of
        "opaque" -> case declareOpaqueClaim (portableStaticClaimName claim) parameters context of
          Left errorValue -> Left (Text.pack (show errorValue))
          Right next -> Right next
        other -> Left ("unsupported portable static claim definition: " <> other)

parsePortableStaticClaimParameters :: Text -> Either Text [(Name, RefSort)]
parsePortableStaticClaimParameters value
  | value == "-" = Right []
  | otherwise = traverse parseParameter (Text.splitOn ";" value)
  where
    parseParameter entry = case Text.splitOn ":" entry of
      [name, sortEncoding]
        | not (Text.null name) && not (Text.null sortEncoding) -> do
            sortValue <- parsePortableSort sortEncoding
            Right (Name name, sortValue)
      _ -> Left ("invalid portable static claim parameter: " <> entry)

parsePortableBindingShape :: Text -> Ty -> Text -> Either Text SurfaceShape
parsePortableBindingShape bindingName ty value
  | value == "plain" = Right PlainShape
  | Just grammar <- Text.stripPrefix "record:" value =
      case ty of
        TyFrame (GrammarId actual) | actual == grammar -> portableRecordShape bindingName grammar
        _ -> Left ("record shape/type mismatch for " <> bindingName)
  | Just frame <- Text.stripPrefix "fixture-raw:" value
  , not (Text.null frame) = Right (FixtureRawShape (FrameId frame))
  | Just amount <- Text.stripPrefix "owned-bytes:nat:" value =
      OwnedBytesShape . RefNat <$> parsePortableNat amount
  | otherwise = Left ("unsupported portable binding shape: " <> value)

portableRecordShape :: Text -> Text -> Either Text SurfaceShape
portableRecordShape bindingName grammar = case grammar of
  "Begin" -> Right (RecordShape "Begin" (Map.singleton "length" (FieldInfo
      (TyUInt 64)
      (SortUInt 64)
      (Just (RefField (RefVar (Name bindingName)) "length" (SortUInt 64))))))
  _ -> Left ("unsupported portable record shape: " <> grammar)

parsePortableNat :: Text -> Either Text Integer
parsePortableNat value = case reads (Text.unpack value) of
  [(number, "")] | number >= 0 -> Right number
  _ -> Left ("invalid portable natural: " <> value)

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
  | Just amount <- Text.stripPrefix "bytes:nat:" value =
      TyBytes . RefNat <$> parsePortableNat amount
  | Just fieldSpec <- Text.stripPrefix "bytes:toNat-field:" value =
      case Text.splitOn ":" fieldSpec of
        [pathSpec, "u64"] -> case Text.splitOn "." pathSpec of
          [bindingName, fieldName]
            | all (not . Text.null) [bindingName, fieldName] ->
                Right (TyBytes (RefToNat (RefField
                  (RefVar (Name bindingName))
                  fieldName
                  (SortUInt 64))))
          _ -> Left ("invalid portable byte field path: " <> fieldSpec)
        _ -> Left ("invalid portable byte-index type: " <> value)
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

materializePortableRequirements
  :: [PortableEnvironmentRequirement]
  -> Either Text (Maybe Proposition, Map Text [Proposition])
materializePortableRequirements requirements = do
  materialized <- traverse materializeRequirement requirements
  let receiveRequirements = [proposition | ("receive-exact", _, proposition) <- materialized]
      selectEntries = [(siteName, [proposition]) | ("select", siteName, proposition) <- materialized]
      selectMap = Map.fromList selectEntries
  if length receiveRequirements > 1
    then Left "duplicate portable receive-exact requirement"
    else if Map.size selectMap /= length selectEntries
      then Left "duplicate portable select requirement site"
      else Right
        ( case receiveRequirements of
            [] -> Nothing
            [proposition] -> Just proposition
            _ -> Nothing
        , selectMap
        )
  where
    materializeRequirement
      :: PortableEnvironmentRequirement
      -> Either Text (Text, Text, Proposition)
    materializeRequirement requirement = do
      proposition <- parsePortableProposition (portableRequirementProposition requirement)
      case portableRequirementSiteKind requirement of
        "receive-exact" -> do
          requireDash "receive-exact site_name" (portableRequirementSiteName requirement)
          Right ("receive-exact", "-", proposition)
        "select" -> do
          siteName <- requireValue "select site_name" (portableRequirementSiteName requirement)
          Right ("select", siteName, proposition)
        other -> Left ("unsupported portable requirement site kind: " <> other)

parsePortableProposition :: Text -> Either Text Proposition
parsePortableProposition value = case Text.stripPrefix "atom:" value of
  Nothing -> Left ("unsupported portable proposition: " <> value)
  Just body ->
    let (claim, argumentTextWithColon) = Text.breakOn ":" body
    in case Text.stripPrefix ":" argumentTextWithColon of
      Nothing -> Left ("portable atom requires arguments: " <> value)
      Just argumentText
        | Text.null claim || Text.null argumentText -> Left ("invalid portable atom: " <> value)
        | otherwise -> Atom claim <$> traverse parseArgument (Text.splitOn "," argumentText)
  where
    parseArgument argument = case Text.stripPrefix "var:" argument of
      Just name | not (Text.null name) -> Right (RefVar (Name name))
      _ -> Left ("unsupported portable proposition argument: " <> argument)

requireValue :: Text -> Text -> Either Text Text
requireValue field value
  | value == "-" = Left (field <> " must be populated")
  | otherwise = Right value

requireDash :: Text -> Text -> Either Text ()
requireDash field value
  | value == "-" = Right ()
  | otherwise = Left (field <> " must be '-' for this session kind")

resolveProfileEnvironment
  :: StaticContext
  -> Map Text [PortableEnvironmentRequirement]
  -> Map Text [PortableEnvironmentBinding]
  -> Map Text PortableEnvironmentProfile
  -> Text
  -> Either Text SurfaceEnvironment
resolveProfileEnvironment staticContext requirements bindings profiles profile =
  case Map.lookup profile profiles of
    Just portable -> materializePortableProfile staticContext requirements bindings portable
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
    "phase0.premature-acceptance" -> legacy "10-accept-before-digest-check.phil"
    "phase0.pending-commit" -> legacy "13-commit-unrelated-parsed.phil"
    "phase0.pending-drop" -> legacy "15-drop-pending-receive.phil"
    "phase0.label-proof" -> legacy "19-label-does-not-transfer-proof.phil"
    _ -> Left ("unknown Phase-0 environment profile: " <> profile)
  where
    legacy name = phase0EnvironmentFor ("examples/rejected/" <> Text.unpack name)

checkIntegrity
  :: [PortableStaticClaim]
  -> Map Text [PortableEnvironmentRequirement]
  -> Map Text [PortableEnvironmentBinding]
  -> Map Text PortableEnvironmentProfile
  -> [NegativeCase]
  -> IO Bool
checkIntegrity staticClaims requirements bindings profiles cases = do
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
      requirementProfilesDeclared = Map.keysSet requirements `Set.isSubsetOf` Map.keysSet profiles
      multibindingDomainExact = Map.keysSet bindings == Set.fromList
        [ "phase0.incompatible-join"
        , "phase0.parsed-validation-bypass"
        , "phase0.unrelated-length"
        , "phase0.stale-policy"
        , "phase0.opaque-proof"
        ]
      requirementDomainExact = Map.keysSet requirements == Set.fromList
        [ "phase0.parsed-validation-bypass"
        , "phase0.stale-policy"
        ]
      staticClaimDomainExact = map portableStaticClaimName staticClaims == ["DigestMatches"]
      staticContextResult = materializePortableStaticContext staticClaims
      profilesResolve = case staticContextResult of
        Left _ -> False
        Right staticContext -> all
          (either (const False) (const True)
            . resolveProfileEnvironment staticContext requirements bindings profiles
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
  report "portable requirements reference declared profiles" requirementProfilesDeclared
  report "portable extra-binding domain is exact for this slice" multibindingDomainExact
  report "portable requirement domain is exact for this slice" requirementDomainExact
  report "portable static claim domain is exact for frozen Phase 0" staticClaimDomainExact
  report "fixtures 001-009, 011, 012, 014, 016-018, and 020 use portable environment material" seedFixturesPortable
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
    , requirementProfilesDeclared
    , multibindingDomainExact
    , requirementDomainExact
    , staticClaimDomainExact
    , seedFixturesPortable
    , profilesResolve
    , filesPresent
    ])

replayCase
  :: StaticContext
  -> Map Text [PortableEnvironmentRequirement]
  -> Map Text [PortableEnvironmentBinding]
  -> Map Text PortableEnvironmentProfile
  -> NegativeCase
  -> IO Bool
replayCase staticContext requirements bindings profiles negativeCase = do
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
  case resolveProfileEnvironment staticContext requirements bindings profiles (negativeCaseEnvironmentProfile negativeCase) of
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
