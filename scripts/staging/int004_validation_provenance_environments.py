from pathlib import Path

path = Path("test/Phase1INT004PortableNegativeManifestMain.hs")
text = path.read_text()


def replace_once(old: str, new: str) -> None:
    global text
    if new in text:
        return
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"expected exactly one patch site, found {count}: {old[:120]!r}")
    text = text.replace(old, new, 1)


replace_once(
    '''  ( Branch (..)\n  , GrammarId (..)\n  , Mode (..)\n  , Name (..)\n  , Outcome (..)\n  , Session (..)\n  , Ty (..)\n  )\n''',
    '''  ( Branch (..)\n  , FrameId (..)\n  , GrammarId (..)\n  , Mode (..)\n  , Name (..)\n  , Outcome (..)\n  , Proposition (..)\n  , RefSort (..)\n  , RefTerm (..)\n  , Session (..)\n  , Ty (..)\n  )\n''',
)

replace_once(
    '''import Phil.Surface.Check\n  ( InitialBinding (..)\n''',
    '''import Phil.Surface.Check\n  ( FieldInfo (..)\n  , InitialBinding (..)\n''',
)

replace_once(
    '''data PortableEnvironmentBinding = PortableEnvironmentBinding\n  { portableExtraProfileId :: Text\n  , portableExtraBindingName :: Text\n  , portableExtraBindingMode :: Text\n  , portableExtraBindingType :: Text\n  , portableExtraBindingShape :: Text\n  }\n  deriving (Eq, Show)\n''',
    '''data PortableEnvironmentBinding = PortableEnvironmentBinding\n  { portableExtraProfileId :: Text\n  , portableExtraBindingName :: Text\n  , portableExtraBindingMode :: Text\n  , portableExtraBindingType :: Text\n  , portableExtraBindingShape :: Text\n  }\n  deriving (Eq, Show)\n\ndata PortableEnvironmentRequirement = PortableEnvironmentRequirement\n  { portableRequirementProfileId :: Text\n  , portableRequirementSiteKind :: Text\n  , portableRequirementSiteName :: Text\n  , portableRequirementProposition :: Text\n  }\n  deriving (Eq, Show)\n''',
)

replace_once(
    '''environmentBindingsPath :: FilePath\nenvironmentBindingsPath = "test/fixtures/phase1-negative/environment-bindings-v1.tsv"\n''',
    '''environmentBindingsPath :: FilePath\nenvironmentBindingsPath = "test/fixtures/phase1-negative/environment-bindings-v1.tsv"\n\nenvironmentRequirementsPath :: FilePath\nenvironmentRequirementsPath = "test/fixtures/phase1-negative/environment-requirements-v1.tsv"\n''',
)

replace_once(
    '''  , "phase0.common"\n  , "phase0.incompatible-join"\n  ]\n''',
    '''  , "phase0.common"\n  , "phase0.incompatible-join"\n  , "phase0.parsed-validation-bypass"\n  , "phase0.unrelated-length"\n  , "phase0.stale-policy"\n  , "phase0.opaque-proof"\n  ]\n''',
)

replace_once(
    '''  , "P1-NEG-P0-005"\n  , "P1-NEG-P0-008"\n''',
    '''  , "P1-NEG-P0-005"\n  , "P1-NEG-P0-006"\n  , "P1-NEG-P0-007"\n  , "P1-NEG-P0-008"\n''',
)

replace_once(
    '''  , "P1-NEG-P0-016"\n  , "P1-NEG-P0-020"\n''',
    '''  , "P1-NEG-P0-016"\n  , "P1-NEG-P0-017"\n  , "P1-NEG-P0-018"\n  , "P1-NEG-P0-020"\n''',
)

replace_once(
    '''  bindings <- case parseEnvironmentBindings bindingText of\n    Left detail -> putStrLn ("FAIL: environment bindings -- " <> detail) >> exitFailure\n    Right value -> pure value\n  integrityOk <- checkIntegrity bindings profiles cases\n  results <- forM cases (replayCase bindings profiles)\n''',
    '''  bindings <- case parseEnvironmentBindings bindingText of\n    Left detail -> putStrLn ("FAIL: environment bindings -- " <> detail) >> exitFailure\n    Right value -> pure value\n  requirementText <- TextIO.readFile environmentRequirementsPath\n  requirements <- case parseEnvironmentRequirements requirementText of\n    Left detail -> putStrLn ("FAIL: environment requirements -- " <> detail) >> exitFailure\n    Right value -> pure value\n  integrityOk <- checkIntegrity requirements bindings profiles cases\n  results <- forM cases (replayCase requirements bindings profiles)\n''',
)

replace_once(
    '''parseEnvironmentBindingRow :: Text -> Either String PortableEnvironmentBinding\nparseEnvironmentBindingRow row = case Text.splitOn "\\t" row of\n  [profileId, bindingName, bindingMode, bindingType, bindingShape]\n    | any Text.null [profileId, bindingName, bindingMode, bindingType, bindingShape] ->\n        Left ("empty portable binding field: " <> Text.unpack row)\n    | otherwise -> Right PortableEnvironmentBinding\n        { portableExtraProfileId = profileId\n        , portableExtraBindingName = bindingName\n        , portableExtraBindingMode = bindingMode\n        , portableExtraBindingType = bindingType\n        , portableExtraBindingShape = bindingShape\n        }\n  _ -> Left ("invalid portable binding TSV row: " <> Text.unpack row)\n\nparseEnvironmentRow :: Text -> Either String PortableEnvironmentProfile\n''',
    '''parseEnvironmentBindingRow :: Text -> Either String PortableEnvironmentBinding\nparseEnvironmentBindingRow row = case Text.splitOn "\\t" row of\n  [profileId, bindingName, bindingMode, bindingType, bindingShape]\n    | any Text.null [profileId, bindingName, bindingMode, bindingType, bindingShape] ->\n        Left ("empty portable binding field: " <> Text.unpack row)\n    | otherwise -> Right PortableEnvironmentBinding\n        { portableExtraProfileId = profileId\n        , portableExtraBindingName = bindingName\n        , portableExtraBindingMode = bindingMode\n        , portableExtraBindingType = bindingType\n        , portableExtraBindingShape = bindingShape\n        }\n  _ -> Left ("invalid portable binding TSV row: " <> Text.unpack row)\n\nparseEnvironmentRequirements :: Text -> Either String (Map Text [PortableEnvironmentRequirement])\nparseEnvironmentRequirements input = case Text.lines input of\n  [] -> Left "empty environment requirement file"\n  header : rows\n    | header /= expectedHeader -> Left ("unexpected requirement header: " <> Text.unpack header)\n    | otherwise -> do\n        parsed <- traverse parseEnvironmentRequirementRow (filter (not . Text.null) rows)\n        Right (Map.fromListWith (++)\n          [(portableRequirementProfileId requirement, [requirement]) | requirement <- parsed])\n  where\n    expectedHeader = Text.intercalate "\\t"\n      [ "profile_id"\n      , "site_kind"\n      , "site_name"\n      , "proposition"\n      ]\n\nparseEnvironmentRequirementRow :: Text -> Either String PortableEnvironmentRequirement\nparseEnvironmentRequirementRow row = case Text.splitOn "\\t" row of\n  [profileId, siteKind, siteName, proposition]\n    | any Text.null [profileId, siteKind, siteName, proposition] ->\n        Left ("empty portable requirement field: " <> Text.unpack row)\n    | otherwise -> Right PortableEnvironmentRequirement\n        { portableRequirementProfileId = profileId\n        , portableRequirementSiteKind = siteKind\n        , portableRequirementSiteName = siteName\n        , portableRequirementProposition = proposition\n        }\n  _ -> Left ("invalid portable requirement TSV row: " <> Text.unpack row)\n\nparseEnvironmentRow :: Text -> Either String PortableEnvironmentProfile\n''',
)

replace_once(
    '''materializePortableProfile\n  :: Map Text [PortableEnvironmentBinding]\n  -> PortableEnvironmentProfile\n  -> Either Text SurfaceEnvironment\nmaterializePortableProfile extraBindings profile = do\n  bindings <- materializePortableBindings extraBindings profile\n  primitives <- parsePrimitiveBindings (portablePrimitiveBindings profile)\n  legacyReceiveFrameRaw <- parsePortableBool\n    "legacy_receive_frame_raw"\n    (portableLegacyReceiveFrameRaw profile)\n  pure (emptySurfaceEnvironment emptyStaticContext)\n    { surfaceInitialBindings = bindings\n    , surfacePrimitives = primitives\n    , surfaceLegacyReceiveFrameRaw = legacyReceiveFrameRaw\n    }\n''',
    '''materializePortableProfile\n  :: Map Text [PortableEnvironmentRequirement]\n  -> Map Text [PortableEnvironmentBinding]\n  -> PortableEnvironmentProfile\n  -> Either Text SurfaceEnvironment\nmaterializePortableProfile requirements extraBindings profile = do\n  bindings <- materializePortableBindings extraBindings profile\n  primitives <- parsePrimitiveBindings (portablePrimitiveBindings profile)\n  legacyReceiveFrameRaw <- parsePortableBool\n    "legacy_receive_frame_raw"\n    (portableLegacyReceiveFrameRaw profile)\n  (receiveExactRequirement, selectRequirements) <- materializePortableRequirements\n    (Map.findWithDefault [] (portableProfileId profile) requirements)\n  pure (emptySurfaceEnvironment emptyStaticContext)\n    { surfaceInitialBindings = bindings\n    , surfacePrimitives = primitives\n    , surfaceLegacyReceiveFrameRaw = legacyReceiveFrameRaw\n    , surfaceReceiveExactRequirement = receiveExactRequirement\n    , surfaceSelectRequirements = selectRequirements\n    }\n''',
)

replace_once(
    '''materializePortableExtraBinding\n  :: PortableEnvironmentBinding\n  -> Either Text (Text, InitialBinding)\nmaterializePortableExtraBinding binding = do\n  mode <- parsePortableMode (portableExtraBindingMode binding)\n  ty <- parsePortableBindingType (portableExtraBindingType binding)\n  shape <- case portableExtraBindingShape binding of\n    "plain" -> Right PlainShape\n    other -> Left ("unsupported portable binding shape: " <> other)\n  Right\n    ( portableExtraBindingName binding\n    , InitialBinding mode ty shape\n    )\n\nparsePortableBindingType :: Text -> Either Text Ty\nparsePortableBindingType value = case value of\n  "bool" -> Right TyBool\n  _ -> Left ("unsupported portable binding type: " <> value)\n''',
    '''materializePortableExtraBinding\n  :: PortableEnvironmentBinding\n  -> Either Text (Text, InitialBinding)\nmaterializePortableExtraBinding binding = do\n  mode <- parsePortableMode (portableExtraBindingMode binding)\n  ty <- parsePortableBindingType (portableExtraBindingType binding)\n  shape <- parsePortableBindingShape\n    (portableExtraBindingName binding)\n    ty\n    (portableExtraBindingShape binding)\n  Right\n    ( portableExtraBindingName binding\n    , InitialBinding mode ty shape\n    )\n\nparsePortableBindingType :: Text -> Either Text Ty\nparsePortableBindingType value\n  | value == "bool" = Right TyBool\n  | Just grammar <- Text.stripPrefix "frame:" value\n  , not (Text.null grammar) = Right (TyFrame (GrammarId grammar))\n  | Just rest <- Text.stripPrefix "validated:" value =\n      case Text.splitOn ":" rest of\n        [claim, context, subject]\n          | all (not . Text.null) [claim, context, subject] ->\n              Right (TyValidated claim (Name context) (Name subject))\n        _ -> Left ("invalid portable validated binding type: " <> value)\n  | Just rest <- Text.stripPrefix "opaque-sorted:" value =\n      case Text.splitOn ":" rest of\n        [name, sortEncoding] | not (Text.null name) ->\n          TyOpaqueSorted name <$> parsePortableSort sortEncoding\n        _ -> Left ("invalid portable sorted opaque binding type: " <> value)\n  | otherwise = Left ("unsupported portable binding type: " <> value)\n\nparsePortableSort :: Text -> Either Text RefSort\nparsePortableSort value\n  | value == "finite-seq-u8" = Right (SortFiniteSeq (SortUInt 8))\n  | Just name <- Text.stripPrefix "opaque-" value\n  , not (Text.null name) = Right (SortOpaque name)\n  | otherwise = Left ("unsupported portable sort: " <> value)\n\nparsePortableBindingShape :: Text -> Ty -> Text -> Either Text SurfaceShape\nparsePortableBindingShape bindingName ty value\n  | value == "plain" = Right PlainShape\n  | Just grammar <- Text.stripPrefix "record:" value =\n      case ty of\n        TyFrame (GrammarId actual) | actual == grammar -> portableRecordShape bindingName grammar\n        _ -> Left ("record shape/type mismatch for " <> bindingName)\n  | Just frame <- Text.stripPrefix "fixture-raw:" value\n  , not (Text.null frame) = Right (FixtureRawShape (FrameId frame))\n  | Just amount <- Text.stripPrefix "owned-bytes:nat:" value =\n      OwnedBytesShape . RefNat <$> parsePortableNat amount\n  | otherwise = Left ("unsupported portable binding shape: " <> value)\n\nportableRecordShape :: Text -> Text -> Either Text SurfaceShape\nportableRecordShape bindingName grammar = case grammar of\n  "Begin" -> Right (RecordShape "Begin" (Map.singleton "length" (FieldInfo\n      (TyUInt 64)\n      (SortUInt 64)\n      (Just (RefField (RefVar (Name bindingName)) "length" (SortUInt 64))))))\n  _ -> Left ("unsupported portable record shape: " <> grammar)\n\nparsePortableNat :: Text -> Either Text Integer\nparsePortableNat value = case reads (Text.unpack value) of\n  [(number, "")] | number >= 0 -> Right number\n  _ -> Left ("invalid portable natural: " <> value)\n''',
)

replace_once(
    '''parsePortableType value\n  | Just name <- Text.stripPrefix "opaque:" value\n  , not (Text.null name) = Right (TyOpaque name)\n  | Just grammar <- Text.stripPrefix "frame:" value\n  , not (Text.null grammar) = Right (TyFrame (GrammarId grammar))\n  | otherwise = Left ("unsupported portable message type: " <> value)\n''',
    '''parsePortableType value\n  | Just name <- Text.stripPrefix "opaque:" value\n  , not (Text.null name) = Right (TyOpaque name)\n  | Just grammar <- Text.stripPrefix "frame:" value\n  , not (Text.null grammar) = Right (TyFrame (GrammarId grammar))\n  | Just amount <- Text.stripPrefix "bytes:nat:" value =\n      TyBytes . RefNat <$> parsePortableNat amount\n  | Just fieldSpec <- Text.stripPrefix "bytes:toNat-field:" value =\n      case Text.splitOn ":" fieldSpec of\n        [pathSpec, "u64"] -> case Text.splitOn "." pathSpec of\n          [bindingName, fieldName]\n            | all (not . Text.null) [bindingName, fieldName] ->\n                Right (TyBytes (RefToNat (RefField\n                  (RefVar (Name bindingName))\n                  fieldName\n                  (SortUInt 64))))\n          _ -> Left ("invalid portable byte field path: " <> fieldSpec)\n        _ -> Left ("invalid portable byte-index type: " <> value)\n  | otherwise = Left ("unsupported portable message type: " <> value)\n''',
)

replace_once(
    '''requireValue :: Text -> Text -> Either Text Text\n''',
    '''materializePortableRequirements\n  :: [PortableEnvironmentRequirement]\n  -> Either Text (Maybe Proposition, Map Text [Proposition])\nmaterializePortableRequirements requirements = do\n  materialized <- traverse materializeRequirement requirements\n  let receiveRequirements = [proposition | ("receive-exact", _, proposition) <- materialized]\n      selectEntries = [(siteName, [proposition]) | ("select", siteName, proposition) <- materialized]\n      selectMap = Map.fromList selectEntries\n  if length receiveRequirements > 1\n    then Left "duplicate portable receive-exact requirement"\n    else if Map.size selectMap /= length selectEntries\n      then Left "duplicate portable select requirement site"\n      else Right\n        ( case receiveRequirements of\n            [] -> Nothing\n            [proposition] -> Just proposition\n            _ -> Nothing\n        , selectMap\n        )\n  where\n    materializeRequirement requirement = do\n      proposition <- parsePortableProposition (portableRequirementProposition requirement)\n      case portableRequirementSiteKind requirement of\n        "receive-exact" -> do\n          requireDash "receive-exact site_name" (portableRequirementSiteName requirement)\n          Right ("receive-exact", "-", proposition)\n        "select" -> do\n          siteName <- requireValue "select site_name" (portableRequirementSiteName requirement)\n          Right ("select", siteName, proposition)\n        other -> Left ("unsupported portable requirement site kind: " <> other)\n\nparsePortableProposition :: Text -> Either Text Proposition\nparsePortableProposition value = case Text.stripPrefix "atom:" value of\n  Nothing -> Left ("unsupported portable proposition: " <> value)\n  Just body ->\n    let (claim, argumentTextWithColon) = Text.breakOn ":" body\n    in case Text.stripPrefix ":" argumentTextWithColon of\n      Nothing -> Left ("portable atom requires arguments: " <> value)\n      Just argumentText\n        | Text.null claim || Text.null argumentText -> Left ("invalid portable atom: " <> value)\n        | otherwise -> Atom claim <$> traverse parseArgument (Text.splitOn "," argumentText)\n  where\n    parseArgument argument = case Text.stripPrefix "var:" argument of\n      Just name | not (Text.null name) -> Right (RefVar (Name name))\n      _ -> Left ("unsupported portable proposition argument: " <> argument)\n\nrequireValue :: Text -> Text -> Either Text Text\n''',
)

replace_once(
    '''resolveProfileEnvironment\n  :: Map Text [PortableEnvironmentBinding]\n  -> Map Text PortableEnvironmentProfile\n  -> Text\n  -> Either Text SurfaceEnvironment\nresolveProfileEnvironment bindings profiles profile =\n  case Map.lookup profile profiles of\n    Just portable -> materializePortableProfile bindings portable\n''',
    '''resolveProfileEnvironment\n  :: Map Text [PortableEnvironmentRequirement]\n  -> Map Text [PortableEnvironmentBinding]\n  -> Map Text PortableEnvironmentProfile\n  -> Text\n  -> Either Text SurfaceEnvironment\nresolveProfileEnvironment requirements bindings profiles profile =\n  case Map.lookup profile profiles of\n    Just portable -> materializePortableProfile requirements bindings portable\n''',
)

replace_once(
    '''  case profile of\n    "phase0.parsed-validation-bypass" -> legacy "06-parsed-used-as-validated.phil"\n    "phase0.unrelated-length" -> legacy "07-unrelated-payload-length.phil"\n    "phase0.premature-acceptance" -> legacy "10-accept-before-digest-check.phil"\n    "phase0.pending-commit" -> legacy "13-commit-unrelated-parsed.phil"\n    "phase0.pending-drop" -> legacy "15-drop-pending-receive.phil"\n    "phase0.stale-policy" -> legacy "17-use-evidence-wrong-context.phil"\n    "phase0.opaque-proof" -> legacy "18-prove-opaque-digest.phil"\n    "phase0.label-proof" -> legacy "19-label-does-not-transfer-proof.phil"\n''',
    '''  case profile of\n    "phase0.premature-acceptance" -> legacy "10-accept-before-digest-check.phil"\n    "phase0.pending-commit" -> legacy "13-commit-unrelated-parsed.phil"\n    "phase0.pending-drop" -> legacy "15-drop-pending-receive.phil"\n    "phase0.label-proof" -> legacy "19-label-does-not-transfer-proof.phil"\n''',
)

replace_once(
    '''checkIntegrity\n  :: Map Text [PortableEnvironmentBinding]\n  -> Map Text PortableEnvironmentProfile\n  -> [NegativeCase]\n  -> IO Bool\ncheckIntegrity bindings profiles cases = do\n''',
    '''checkIntegrity\n  :: Map Text [PortableEnvironmentRequirement]\n  -> Map Text [PortableEnvironmentBinding]\n  -> Map Text PortableEnvironmentProfile\n  -> [NegativeCase]\n  -> IO Bool\ncheckIntegrity requirements bindings profiles cases = do\n''',
)

replace_once(
    '''      bindingProfilesDeclared = Map.keysSet bindings `Set.isSubsetOf` Map.keysSet profiles\n      multibindingDomainExact = Map.keysSet bindings == Set.singleton "phase0.incompatible-join"\n      profilesResolve = all\n        (either (const False) (const True)\n          . resolveProfileEnvironment bindings profiles\n          . negativeCaseEnvironmentProfile)\n        cases\n''',
    '''      bindingProfilesDeclared = Map.keysSet bindings `Set.isSubsetOf` Map.keysSet profiles\n      requirementProfilesDeclared = Map.keysSet requirements `Set.isSubsetOf` Map.keysSet profiles\n      multibindingDomainExact = Map.keysSet bindings == Set.fromList\n        [ "phase0.incompatible-join"\n        , "phase0.parsed-validation-bypass"\n        , "phase0.unrelated-length"\n        , "phase0.stale-policy"\n        , "phase0.opaque-proof"\n        ]\n      requirementDomainExact = Map.keysSet requirements == Set.fromList\n        [ "phase0.parsed-validation-bypass"\n        , "phase0.stale-policy"\n        ]\n      profilesResolve = all\n        (either (const False) (const True)\n          . resolveProfileEnvironment requirements bindings profiles\n          . negativeCaseEnvironmentProfile)\n        cases\n''',
)

replace_once(
    '''  report "portable extra bindings reference declared profiles" bindingProfilesDeclared\n  report "portable extra-binding domain is exact for this slice" multibindingDomainExact\n  report "fixtures 001-005, 008, 009, 011, 012, 014, 016, and 020 use portable environment material" seedFixturesPortable\n''',
    '''  report "portable extra bindings reference declared profiles" bindingProfilesDeclared\n  report "portable requirements reference declared profiles" requirementProfilesDeclared\n  report "portable extra-binding domain is exact for this slice" multibindingDomainExact\n  report "portable requirement domain is exact for this slice" requirementDomainExact\n  report "fixtures 001-009, 011, 012, 014, 016-018, and 020 use portable environment material" seedFixturesPortable\n''',
)

replace_once(
    '''    , seedProfileDomainExact\n    , bindingProfilesDeclared\n    , multibindingDomainExact\n    , seedFixturesPortable\n''',
    '''    , seedProfileDomainExact\n    , bindingProfilesDeclared\n    , requirementProfilesDeclared\n    , multibindingDomainExact\n    , requirementDomainExact\n    , seedFixturesPortable\n''',
)

replace_once(
    '''replayCase\n  :: Map Text [PortableEnvironmentBinding]\n  -> Map Text PortableEnvironmentProfile\n  -> NegativeCase\n  -> IO Bool\nreplayCase bindings profiles negativeCase = do\n''',
    '''replayCase\n  :: Map Text [PortableEnvironmentRequirement]\n  -> Map Text [PortableEnvironmentBinding]\n  -> Map Text PortableEnvironmentProfile\n  -> NegativeCase\n  -> IO Bool\nreplayCase requirements bindings profiles negativeCase = do\n''',
)

replace_once(
    '''  case resolveProfileEnvironment bindings profiles (negativeCaseEnvironmentProfile negativeCase) of\n''',
    '''  case resolveProfileEnvironment requirements bindings profiles (negativeCaseEnvironmentProfile negativeCase) of\n''',
)

path.write_text(text)
