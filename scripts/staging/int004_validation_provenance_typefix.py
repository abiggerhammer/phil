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


# Keep the requirement-kind tags concrete under -Wtype-defaults.
replace_once(
    '''  where
    materializeRequirement requirement = do
''',
    '''  where
    materializeRequirement
      :: PortableEnvironmentRequirement
      -> Either Text (Text, Text, Proposition)
    materializeRequirement requirement = do
''',
)

replace_once(
    '''import Control.Monad (forM, unless, when)
''',
    '''import Control.Monad (foldM, forM, unless, when)
''',
)

replace_once(
    '''import Phil.Core.Static (emptyStaticContext)
''',
    '''import Phil.Core.Static (StaticContext, declareOpaqueClaim, emptyStaticContext)
''',
)

replace_once(
    '''data PortableEnvironmentRequirement = PortableEnvironmentRequirement
  { portableRequirementProfileId :: Text
  , portableRequirementSiteKind :: Text
  , portableRequirementSiteName :: Text
  , portableRequirementProposition :: Text
  }
  deriving (Eq, Show)
''',
    '''data PortableEnvironmentRequirement = PortableEnvironmentRequirement
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
''',
)

replace_once(
    '''environmentRequirementsPath :: FilePath
environmentRequirementsPath = "test/fixtures/phase1-negative/environment-requirements-v1.tsv"
''',
    '''environmentRequirementsPath :: FilePath
environmentRequirementsPath = "test/fixtures/phase1-negative/environment-requirements-v1.tsv"

environmentStaticClaimsPath :: FilePath
environmentStaticClaimsPath = "test/fixtures/phase1-negative/environment-static-claims-v1.tsv"
''',
)

replace_once(
    '''  requirements <- case parseEnvironmentRequirements requirementText of
    Left detail -> putStrLn ("FAIL: environment requirements -- " <> detail) >> exitFailure
    Right value -> pure value
  integrityOk <- checkIntegrity requirements bindings profiles cases
  results <- forM cases (replayCase requirements bindings profiles)
''',
    '''  requirements <- case parseEnvironmentRequirements requirementText of
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
''',
)

replace_once(
    '''parseEnvironmentRequirementRow :: Text -> Either String PortableEnvironmentRequirement
parseEnvironmentRequirementRow row = case Text.splitOn "\\t" row of
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

parseEnvironmentRow :: Text -> Either String PortableEnvironmentProfile
''',
    '''parseEnvironmentRequirementRow :: Text -> Either String PortableEnvironmentRequirement
parseEnvironmentRequirementRow row = case Text.splitOn "\\t" row of
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
    | header /= Text.intercalate "\\t" ["claim_name", "definition_kind", "parameters"] ->
        Left ("unexpected static claim header: " <> Text.unpack header)
    | otherwise -> traverse parsePortableStaticClaimRow (filter (not . Text.null) rows)

parsePortableStaticClaimRow :: Text -> Either String PortableStaticClaim
parsePortableStaticClaimRow row = case Text.splitOn "\\t" row of
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
''',
)

replace_once(
    '''materializePortableProfile
  :: Map Text [PortableEnvironmentRequirement]
  -> Map Text [PortableEnvironmentBinding]
  -> PortableEnvironmentProfile
  -> Either Text SurfaceEnvironment
materializePortableProfile requirements extraBindings profile = do
''',
    '''materializePortableProfile
  :: StaticContext
  -> Map Text [PortableEnvironmentRequirement]
  -> Map Text [PortableEnvironmentBinding]
  -> PortableEnvironmentProfile
  -> Either Text SurfaceEnvironment
materializePortableProfile staticContext requirements extraBindings profile = do
''',
)

replace_once(
    '''  pure (emptySurfaceEnvironment emptyStaticContext)
    { surfaceInitialBindings = bindings
''',
    '''  pure (emptySurfaceEnvironment staticContext)
    { surfaceInitialBindings = bindings
''',
)

replace_once(
    '''parsePortableSort value
  | value == "finite-seq-u8" = Right (SortFiniteSeq (SortUInt 8))
  | Just name <- Text.stripPrefix "opaque-" value
  , not (Text.null name) = Right (SortOpaque name)
  | otherwise = Left ("unsupported portable sort: " <> value)
''',
    '''parsePortableSort value
  | value == "finite-seq-u8" = Right (SortFiniteSeq (SortUInt 8))
  | Just name <- Text.stripPrefix "opaque-" value
  , not (Text.null name) = Right (SortOpaque name)
  | Just name <- Text.stripPrefix "stable-id-" value
  , not (Text.null name) = Right (SortStableId name)
  | otherwise = Left ("unsupported portable sort: " <> value)
''',
)

replace_once(
    '''parsePortableBindingShape :: Text -> Ty -> Text -> Either Text SurfaceShape
''',
    '''materializePortableStaticContext :: [PortableStaticClaim] -> Either Text StaticContext
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
''',
)

replace_once(
    '''resolveProfileEnvironment
  :: Map Text [PortableEnvironmentRequirement]
  -> Map Text [PortableEnvironmentBinding]
  -> Map Text PortableEnvironmentProfile
  -> Text
  -> Either Text SurfaceEnvironment
resolveProfileEnvironment requirements bindings profiles profile =
  case Map.lookup profile profiles of
    Just portable -> materializePortableProfile requirements bindings portable
''',
    '''resolveProfileEnvironment
  :: StaticContext
  -> Map Text [PortableEnvironmentRequirement]
  -> Map Text [PortableEnvironmentBinding]
  -> Map Text PortableEnvironmentProfile
  -> Text
  -> Either Text SurfaceEnvironment
resolveProfileEnvironment staticContext requirements bindings profiles profile =
  case Map.lookup profile profiles of
    Just portable -> materializePortableProfile staticContext requirements bindings portable
''',
)

replace_once(
    '''checkIntegrity
  :: Map Text [PortableEnvironmentRequirement]
  -> Map Text [PortableEnvironmentBinding]
  -> Map Text PortableEnvironmentProfile
  -> [NegativeCase]
  -> IO Bool
checkIntegrity requirements bindings profiles cases = do
''',
    '''checkIntegrity
  :: [PortableStaticClaim]
  -> Map Text [PortableEnvironmentRequirement]
  -> Map Text [PortableEnvironmentBinding]
  -> Map Text PortableEnvironmentProfile
  -> [NegativeCase]
  -> IO Bool
checkIntegrity staticClaims requirements bindings profiles cases = do
''',
)

replace_once(
    '''      requirementDomainExact = Map.keysSet requirements == Set.fromList
        [ "phase0.parsed-validation-bypass"
        , "phase0.stale-policy"
        ]
      profilesResolve = all
        (either (const False) (const True)
          . resolveProfileEnvironment requirements bindings profiles
          . negativeCaseEnvironmentProfile)
        cases
''',
    '''      requirementDomainExact = Map.keysSet requirements == Set.fromList
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
''',
)

replace_once(
    '''  report "portable requirement domain is exact for this slice" requirementDomainExact
  report "fixtures 001-009, 011, 012, 014, 016-018, and 020 use portable environment material" seedFixturesPortable
''',
    '''  report "portable requirement domain is exact for this slice" requirementDomainExact
  report "portable static claim domain is exact for frozen Phase 0" staticClaimDomainExact
  report "fixtures 001-009, 011, 012, 014, 016-018, and 020 use portable environment material" seedFixturesPortable
''',
)

replace_once(
    '''    , requirementDomainExact
    , seedFixturesPortable
''',
    '''    , requirementDomainExact
    , staticClaimDomainExact
    , seedFixturesPortable
''',
)

replace_once(
    '''replayCase
  :: Map Text [PortableEnvironmentRequirement]
  -> Map Text [PortableEnvironmentBinding]
  -> Map Text PortableEnvironmentProfile
  -> NegativeCase
  -> IO Bool
replayCase requirements bindings profiles negativeCase = do
''',
    '''replayCase
  :: StaticContext
  -> Map Text [PortableEnvironmentRequirement]
  -> Map Text [PortableEnvironmentBinding]
  -> Map Text PortableEnvironmentProfile
  -> NegativeCase
  -> IO Bool
replayCase staticContext requirements bindings profiles negativeCase = do
''',
)

replace_once(
    '''  case resolveProfileEnvironment requirements bindings profiles (negativeCaseEnvironmentProfile negativeCase) of
''',
    '''  case resolveProfileEnvironment staticContext requirements bindings profiles (negativeCaseEnvironmentProfile negativeCase) of
''',
)

path.write_text(text)
