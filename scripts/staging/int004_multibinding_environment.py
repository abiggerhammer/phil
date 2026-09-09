from pathlib import Path

path = Path("test/Phase1INT004PortableNegativeManifestMain.hs")
text = path.read_text()


def replace_once(old: str, new: str) -> None:
    global text
    if new in text:
        return
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"expected exactly one patch site, found {count}: {old[:100]!r}")
    text = text.replace(old, new, 1)


replace_once(
    '''data PortableEnvironmentProfile = PortableEnvironmentProfile\n  { portableProfileId :: Text\n  , portableBindingName :: Text\n  , portableBindingMode :: Text\n  , portableSessionKind :: Text\n  , portableMessageName :: Text\n  , portableMessageType :: Text\n  , portableTerminalOutcome :: Text\n  , portableBranches :: Text\n  , portablePrimitiveBindings :: Text\n  , portableLegacyReceiveFrameRaw :: Text\n  }\n  deriving (Eq, Show)\n''',
    '''data PortableEnvironmentProfile = PortableEnvironmentProfile\n  { portableProfileId :: Text\n  , portableBindingName :: Text\n  , portableBindingMode :: Text\n  , portableSessionKind :: Text\n  , portableMessageName :: Text\n  , portableMessageType :: Text\n  , portableTerminalOutcome :: Text\n  , portableBranches :: Text\n  , portablePrimitiveBindings :: Text\n  , portableLegacyReceiveFrameRaw :: Text\n  }\n  deriving (Eq, Show)\n\ndata PortableEnvironmentBinding = PortableEnvironmentBinding\n  { portableExtraProfileId :: Text\n  , portableExtraBindingName :: Text\n  , portableExtraBindingMode :: Text\n  , portableExtraBindingType :: Text\n  , portableExtraBindingShape :: Text\n  }\n  deriving (Eq, Show)\n''',
)

replace_once(
    '''environmentProfilesPath :: FilePath\nenvironmentProfilesPath = "test/fixtures/phase1-negative/environment-profiles-v1.tsv"\n''',
    '''environmentProfilesPath :: FilePath\nenvironmentProfilesPath = "test/fixtures/phase1-negative/environment-profiles-v1.tsv"\n\nenvironmentBindingsPath :: FilePath\nenvironmentBindingsPath = "test/fixtures/phase1-negative/environment-bindings-v1.tsv"\n''',
)

replace_once(
    '''  , "phase0.common"\n  ]\n''',
    '''  , "phase0.common"\n  , "phase0.incompatible-join"\n  ]\n''',
)

replace_once(
    '''  , "P1-NEG-P0-005"\n  , "P1-NEG-P0-009"\n''',
    '''  , "P1-NEG-P0-005"\n  , "P1-NEG-P0-008"\n  , "P1-NEG-P0-009"\n''',
)

replace_once(
    '''  profiles <- case parseEnvironmentProfiles profileText of\n    Left detail -> putStrLn ("FAIL: environment profiles -- " <> detail) >> exitFailure\n    Right value -> pure value\n  integrityOk <- checkIntegrity profiles cases\n  results <- forM cases (replayCase profiles)\n''',
    '''  profiles <- case parseEnvironmentProfiles profileText of\n    Left detail -> putStrLn ("FAIL: environment profiles -- " <> detail) >> exitFailure\n    Right value -> pure value\n  bindingText <- TextIO.readFile environmentBindingsPath\n  bindings <- case parseEnvironmentBindings bindingText of\n    Left detail -> putStrLn ("FAIL: environment bindings -- " <> detail) >> exitFailure\n    Right value -> pure value\n  integrityOk <- checkIntegrity bindings profiles cases\n  results <- forM cases (replayCase bindings profiles)\n''',
)

replace_once(
    '''parseEnvironmentRow :: Text -> Either String PortableEnvironmentProfile\nparseEnvironmentRow row = case Text.splitOn "\\t" row of\n''',
    '''parseEnvironmentBindings :: Text -> Either String (Map Text [PortableEnvironmentBinding])\nparseEnvironmentBindings input = case Text.lines input of\n  [] -> Left "empty environment binding file"\n  header : rows\n    | header /= expectedHeader -> Left ("unexpected binding header: " <> Text.unpack header)\n    | otherwise -> do\n        parsed <- traverse parseEnvironmentBindingRow (filter (not . Text.null) rows)\n        let grouped = Map.fromListWith (++)\n              [(portableExtraProfileId binding, [binding]) | binding <- parsed]\n            names bindingsForProfile = map portableExtraBindingName bindingsForProfile\n            unique bindingsForProfile =\n              Set.size (Set.fromList (names bindingsForProfile)) == length bindingsForProfile\n        if all unique (Map.elems grouped)\n          then Right grouped\n          else Left "duplicate portable extra binding name within profile"\n  where\n    expectedHeader = Text.intercalate "\\t"\n      [ "profile_id"\n      , "binding_name"\n      , "binding_mode"\n      , "binding_type"\n      , "binding_shape"\n      ]\n\nparseEnvironmentBindingRow :: Text -> Either String PortableEnvironmentBinding\nparseEnvironmentBindingRow row = case Text.splitOn "\\t" row of\n  [profileId, bindingName, bindingMode, bindingType, bindingShape]\n    | any Text.null [profileId, bindingName, bindingMode, bindingType, bindingShape] ->\n        Left ("empty portable binding field: " <> Text.unpack row)\n    | otherwise -> Right PortableEnvironmentBinding\n        { portableExtraProfileId = profileId\n        , portableExtraBindingName = bindingName\n        , portableExtraBindingMode = bindingMode\n        , portableExtraBindingType = bindingType\n        , portableExtraBindingShape = bindingShape\n        }\n  _ -> Left ("invalid portable binding TSV row: " <> Text.unpack row)\n\nparseEnvironmentRow :: Text -> Either String PortableEnvironmentProfile\nparseEnvironmentRow row = case Text.splitOn "\\t" row of\n''',
)

replace_once(
    '''materializePortableProfile :: PortableEnvironmentProfile -> Either Text SurfaceEnvironment\nmaterializePortableProfile profile = do\n  bindings <- materializePortableBindings profile\n''',
    '''materializePortableProfile\n  :: Map Text [PortableEnvironmentBinding]\n  -> PortableEnvironmentProfile\n  -> Either Text SurfaceEnvironment\nmaterializePortableProfile extraBindings profile = do\n  bindings <- materializePortableBindings extraBindings profile\n''',
)

replace_once(
    '''materializePortableBindings\n  :: PortableEnvironmentProfile\n  -> Either Text (Map Text InitialBinding)\nmaterializePortableBindings profile =\n  case portableSessionKind profile of\n    "none" -> do\n      requireDash "binding_name" (portableBindingName profile)\n      requireDash "binding_mode" (portableBindingMode profile)\n      requireDash "message_name" (portableMessageName profile)\n      requireDash "message_type" (portableMessageType profile)\n      requireDash "terminal_outcome" (portableTerminalOutcome profile)\n      requireDash "branches" (portableBranches profile)\n      Right Map.empty\n    _ -> do\n      bindingName <- requireValue "binding_name" (portableBindingName profile)\n      mode <- parsePortableMode (portableBindingMode profile)\n      session <- parsePortableSession profile\n      let binding = InitialBinding mode (TyEndpoint session) PlainShape\n      Right (Map.singleton bindingName binding)\n''',
    '''materializePortableBindings\n  :: Map Text [PortableEnvironmentBinding]\n  -> PortableEnvironmentProfile\n  -> Either Text (Map Text InitialBinding)\nmaterializePortableBindings extraBindings profile = do\n  primary <- case portableSessionKind profile of\n    "none" -> do\n      requireDash "binding_name" (portableBindingName profile)\n      requireDash "binding_mode" (portableBindingMode profile)\n      requireDash "message_name" (portableMessageName profile)\n      requireDash "message_type" (portableMessageType profile)\n      requireDash "terminal_outcome" (portableTerminalOutcome profile)\n      requireDash "branches" (portableBranches profile)\n      Right Map.empty\n    _ -> do\n      bindingName <- requireValue "binding_name" (portableBindingName profile)\n      mode <- parsePortableMode (portableBindingMode profile)\n      session <- parsePortableSession profile\n      let binding = InitialBinding mode (TyEndpoint session) PlainShape\n      Right (Map.singleton bindingName binding)\n  extras <- traverse materializePortableExtraBinding\n    (Map.findWithDefault [] (portableProfileId profile) extraBindings)\n  let extrasMap = Map.fromList extras\n  if Map.size extrasMap /= length extras\n    then Left "duplicate materialized portable extra binding"\n    else if not (Set.null (Map.keysSet primary `Set.intersection` Map.keysSet extrasMap))\n      then Left "portable extra binding conflicts with primary binding"\n      else Right (Map.union primary extrasMap)\n\nmaterializePortableExtraBinding\n  :: PortableEnvironmentBinding\n  -> Either Text (Text, InitialBinding)\nmaterializePortableExtraBinding binding = do\n  mode <- parsePortableMode (portableExtraBindingMode binding)\n  ty <- parsePortableBindingType (portableExtraBindingType binding)\n  shape <- case portableExtraBindingShape binding of\n    "plain" -> Right PlainShape\n    other -> Left ("unsupported portable binding shape: " <> other)\n  Right\n    ( portableExtraBindingName binding\n    , InitialBinding mode ty shape\n    )\n\nparsePortableBindingType :: Text -> Either Text Ty\nparsePortableBindingType value = case value of\n  "bool" -> Right TyBool\n  _ -> Left ("unsupported portable binding type: " <> value)\n''',
)

replace_once(
    '''  "offer" -> do\n    requireDash "message_name" (portableMessageName profile)\n    requireDash "message_type" (portableMessageType profile)\n    requireDash "terminal_outcome" (portableTerminalOutcome profile)\n    branches <- parsePortableBranches (portableBranches profile)\n    pure (Offer branches)\n  other -> Left ("unknown portable session kind: " <> other)\n''',
    '''  "offer" -> do\n    requireDash "message_name" (portableMessageName profile)\n    requireDash "message_type" (portableMessageType profile)\n    requireDash "terminal_outcome" (portableTerminalOutcome profile)\n    branches <- parsePortableBranches (portableBranches profile)\n    pure (Offer branches)\n  "select" -> do\n    requireDash "message_name" (portableMessageName profile)\n    requireDash "message_type" (portableMessageType profile)\n    requireDash "terminal_outcome" (portableTerminalOutcome profile)\n    branches <- parsePortableBranches (portableBranches profile)\n    pure (Select branches)\n  other -> Left ("unknown portable session kind: " <> other)\n''',
)

replace_once(
    '''          "unchecked-u32-add" -> Right (name, PrimitiveUncheckedU32Add)\n          _ -> Left ("unsupported portable primitive semantic: " <> semantic)\n''',
    '''          "unchecked-u32-add" -> Right (name, PrimitiveUncheckedU32Add)\n          "continue-common-state" -> Right (name, PrimitiveContinueCommonState)\n          _ -> Left ("unsupported portable primitive semantic: " <> semantic)\n''',
)

replace_once(
    '''resolveProfileEnvironment\n  :: Map Text PortableEnvironmentProfile\n  -> Text\n  -> Either Text SurfaceEnvironment\nresolveProfileEnvironment profiles profile =\n  case Map.lookup profile profiles of\n    Just portable -> materializePortableProfile portable\n''',
    '''resolveProfileEnvironment\n  :: Map Text [PortableEnvironmentBinding]\n  -> Map Text PortableEnvironmentProfile\n  -> Text\n  -> Either Text SurfaceEnvironment\nresolveProfileEnvironment bindings profiles profile =\n  case Map.lookup profile profiles of\n    Just portable -> materializePortableProfile bindings portable\n''',
)

replace_once(
    '''    "phase0.unrelated-length" -> legacy "07-unrelated-payload-length.phil"\n    "phase0.incompatible-join" -> legacy "08-incompatible-branch-join.phil"\n    "phase0.premature-acceptance" -> legacy "10-accept-before-digest-check.phil"\n''',
    '''    "phase0.unrelated-length" -> legacy "07-unrelated-payload-length.phil"\n    "phase0.premature-acceptance" -> legacy "10-accept-before-digest-check.phil"\n''',
)

replace_once(
    '''checkIntegrity :: Map Text PortableEnvironmentProfile -> [NegativeCase] -> IO Bool\ncheckIntegrity profiles cases = do\n''',
    '''checkIntegrity\n  :: Map Text [PortableEnvironmentBinding]\n  -> Map Text PortableEnvironmentProfile\n  -> [NegativeCase]\n  -> IO Bool\ncheckIntegrity bindings profiles cases = do\n''',
)

replace_once(
    '''      seedFixturesPortable = all\n        (\\negativeCase ->\n          not (Set.member (negativeCaseId negativeCase) seedPortableFixtures)\n            || Map.member (negativeCaseEnvironmentProfile negativeCase) profiles)\n        cases\n      profilesResolve = all\n        (either (const False) (const True)\n          . resolveProfileEnvironment profiles\n          . negativeCaseEnvironmentProfile)\n        cases\n''',
    '''      seedFixturesPortable = all\n        (\\negativeCase ->\n          not (Set.member (negativeCaseId negativeCase) seedPortableFixtures)\n            || Map.member (negativeCaseEnvironmentProfile negativeCase) profiles)\n        cases\n      bindingProfilesDeclared = Map.keysSet bindings `Set.isSubsetOf` Map.keysSet profiles\n      multibindingDomainExact = Map.keysSet bindings == Set.singleton "phase0.incompatible-join"\n      profilesResolve = all\n        (either (const False) (const True)\n          . resolveProfileEnvironment bindings profiles\n          . negativeCaseEnvironmentProfile)\n        cases\n''',
)

replace_once(
    '''  report "portable environment seed has exact profile domain" seedProfileDomainExact\n  report "fixtures 001-005, 009, 011, 012, 014, 016, and 020 use portable environment material" seedFixturesPortable\n  report "every named environment profile resolves" profilesResolve\n''',
    '''  report "portable environment seed has exact profile domain" seedProfileDomainExact\n  report "portable extra bindings reference declared profiles" bindingProfilesDeclared\n  report "portable extra-binding domain is exact for this slice" multibindingDomainExact\n  report "fixtures 001-005, 008, 009, 011, 012, 014, 016, and 020 use portable environment material" seedFixturesPortable\n  report "every named environment profile resolves" profilesResolve\n''',
)

replace_once(
    '''    , profilesNamed\n    , seedProfileDomainExact\n    , seedFixturesPortable\n    , profilesResolve\n''',
    '''    , profilesNamed\n    , seedProfileDomainExact\n    , bindingProfilesDeclared\n    , multibindingDomainExact\n    , seedFixturesPortable\n    , profilesResolve\n''',
)

replace_once(
    '''replayCase :: Map Text PortableEnvironmentProfile -> NegativeCase -> IO Bool\nreplayCase profiles negativeCase = do\n''',
    '''replayCase\n  :: Map Text [PortableEnvironmentBinding]\n  -> Map Text PortableEnvironmentProfile\n  -> NegativeCase\n  -> IO Bool\nreplayCase bindings profiles negativeCase = do\n''',
)

replace_once(
    '''  case resolveProfileEnvironment profiles (negativeCaseEnvironmentProfile negativeCase) of\n''',
    '''  case resolveProfileEnvironment bindings profiles (negativeCaseEnvironmentProfile negativeCase) of\n''',
)

path.write_text(text)
