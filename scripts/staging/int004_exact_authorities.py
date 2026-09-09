#!/usr/bin/env python3
from pathlib import Path
import sys

path = Path("test/Phase1INT004PortableNegativeManifestMain.hs")
text = path.read_text()

if "data PortableAuthority = PortableAuthority" in text:
    print("INT-004 exact authority decoder already applied")
    sys.exit(0)


def replace_once(old: str, new: str) -> None:
    global text
    if old not in text:
        raise SystemExit(f"missing staging anchor: {old[:100]!r}")
    text = text.replace(old, new, 1)


def replace_between(start: str, end: str, new: str) -> None:
    global text
    i = text.find(start)
    if i < 0:
        raise SystemExit(f"missing staging start anchor: {start!r}")
    j = text.find(end, i)
    if j < 0:
        raise SystemExit(f"missing staging end anchor: {end!r}")
    text = text[:i] + new + text[j:]

new_data = r'''data PortableAuthority = PortableAuthority
  { portableAuthorityRef :: Text
  , portableAuthorityKind :: Text
  , portableAuthorityCanonicalId :: Text
  , portableAuthorityCanonicalSource :: Text
  }
  deriving (Eq, Show)

'''
replace_once("manifestPath :: FilePath\n", new_data + "manifestPath :: FilePath\n")

new_path = r'''authorityRegistryPath :: FilePath
authorityRegistryPath = "test/fixtures/phase1-negative/authority-registry-v1.tsv"

'''
replace_once("environmentProfilesPath :: FilePath\n", new_path + "environmentProfilesPath :: FilePath\n")

replace_once(
    '''  cases <- case parseManifest manifest of
    Left detail -> putStrLn ("FAIL: manifest -- " <> detail) >> exitFailure
    Right value -> pure value
  profileText <- TextIO.readFile environmentProfilesPath
''',
    '''  cases <- case parseManifest manifest of
    Left detail -> putStrLn ("FAIL: manifest -- " <> detail) >> exitFailure
    Right value -> pure value
  authorityText <- TextIO.readFile authorityRegistryPath
  authorities <- case parseAuthorityRegistry authorityText of
    Left detail -> putStrLn ("FAIL: authority registry -- " <> detail) >> exitFailure
    Right value -> pure value
  profileText <- TextIO.readFile environmentProfilesPath
''',
)

replace_once(
    "  integrityOk <- checkIntegrity staticClaims sessions typeAliases requirements bindings profiles cases\n",
    "  integrityOk <- checkIntegrity authorities staticClaims sessions typeAliases requirements bindings profiles cases\n",
)

authority_parser = r'''parseAuthorityRegistry :: Text -> Either String (Map Text PortableAuthority)
parseAuthorityRegistry input = case Text.lines input of
  [] -> Left "empty authority registry"
  header : rows
    | header /= Text.intercalate "\t"
        [ "authority_ref", "authority_kind", "canonical_id", "canonical_source" ] ->
        Left ("unexpected authority registry header: " <> Text.unpack header)
    | otherwise -> do
        parsed <- traverse parseAuthorityRow (filter (not . Text.null) rows)
        let registry = Map.fromList [(portableAuthorityRef authority, authority) | authority <- parsed]
            ids = map portableAuthorityCanonicalId parsed
        if Map.size registry /= length parsed
          then Left "duplicate portable authority_ref"
          else if Set.size (Set.fromList ids) /= length ids
            then Left "duplicate portable canonical authority id"
            else Right registry

parseAuthorityRow :: Text -> Either String PortableAuthority
parseAuthorityRow row = case Text.splitOn "\t" row of
  [authorityRef, authorityKind, canonicalId, canonicalSource]
    | any Text.null [authorityRef, authorityKind, canonicalId, canonicalSource] ->
        Left ("empty portable authority field: " <> Text.unpack row)
    | authorityKind `notElem` ["matrix", "certified"] ->
        Left ("unknown portable authority kind: " <> Text.unpack authorityKind)
    | authorityRef /= authorityKind <> ":" <> canonicalId ->
        Left ("authority ref/kind/id mismatch: " <> Text.unpack row)
    | canonicalId == "INT-004" ->
        Left "INT-004 is a meta-level conformance case, not fixture semantic authority"
    | otherwise -> Right PortableAuthority
        { portableAuthorityRef = authorityRef
        , portableAuthorityKind = authorityKind
        , portableAuthorityCanonicalId = canonicalId
        , portableAuthorityCanonicalSource = canonicalSource
        }
  _ -> Left ("invalid portable authority TSV row: " <> Text.unpack row)

caseAuthorityRefs :: NegativeCase -> Either Text [Text]
caseAuthorityRefs negativeCase = do
  let refs = Text.splitOn ";" (negativeCaseAuthority negativeCase)
  when (null refs || any Text.null refs) $
    Left ("fixture has empty governing authority reference: " <> negativeCaseId negativeCase)
  parsed <- traverse parseRef refs
  when (Set.size (Set.fromList parsed) /= length parsed) $
    Left ("fixture repeats governing authority reference: " <> negativeCaseId negativeCase)
  Right parsed
  where
    parseRef ref = case Text.breakOn ":" ref of
      (kind, rest) -> case Text.stripPrefix ":" rest of
        Nothing -> Left ("untyped governing authority reference: " <> ref)
        Just canonicalId
          | kind `notElem` ["matrix", "certified"] ->
              Left ("unknown governing authority kind: " <> kind)
          | Text.null canonicalId -> Left ("empty governing authority id: " <> ref)
          | canonicalId == "INT-004" ->
              Left "INT-004 is a meta-level conformance case, not fixture semantic authority"
          | otherwise -> Right ref

'''
replace_once("parseManifest :: Text -> Either String [NegativeCase]\n", authority_parser + "parseManifest :: Text -> Either String [NegativeCase]\n")

new_integrity = r'''checkIntegrity
  :: Map Text PortableAuthority
  -> [PortableStaticClaim]
  -> Map Text Session
  -> Map Text [PortableTypeAlias]
  -> Map Text [PortableEnvironmentRequirement]
  -> Map Text [PortableEnvironmentBinding]
  -> Map Text PortableEnvironmentProfile
  -> [NegativeCase]
  -> IO Bool
checkIntegrity authorities staticClaims sessions aliases requirements bindings profiles cases = do
  let ids = map negativeCaseId cases
      paths = map negativeCasePath cases
      uniqueIds = Set.size (Set.fromList ids) == length ids
      uniquePaths = Set.size (Set.fromList paths) == length paths
      exactFrozenCount = length cases == 20
      layersExact = all ((== "surface-check") . negativeCaseLayer) cases
      parsedAuthorities = traverse caseAuthorityRefs cases
      authoritySyntaxValid = either (const False) (const True) parsedAuthorities
      usedAuthorityRefs = case parsedAuthorities of
        Left _ -> Set.empty
        Right refsByCase -> Set.fromList (concat refsByCase)
      authorityDomainExact = authoritySyntaxValid && usedAuthorityRefs == Map.keysSet authorities
      matrixSourcesExact = all
        (\authority -> portableAuthorityKind authority /= "matrix"
          || portableAuthorityCanonicalSource authority == "Phil Phase 1 Conformance Matrix")
        (Map.elems authorities)
      certifiedSourcesPortable = all
        (\authority -> portableAuthorityKind authority /= "certified"
          || ("proof/" `Text.isPrefixOf` portableAuthorityCanonicalSource authority
            && ".v" `Text.isSuffixOf` portableAuthorityCanonicalSource authority))
        (Map.elems authorities)
      certifiedSourcePaths =
        [ Text.unpack (portableAuthorityCanonicalSource authority)
        | authority <- Map.elems authorities
        , portableAuthorityKind authority == "certified"
        ]
      profilesNamed = all (Text.isPrefixOf "phase0." . negativeCaseEnvironmentProfile) cases
      seedProfileDomainExact = Map.keysSet profiles == seedPortableProfiles
      seedFixturesPortable = all
        (\negativeCase ->
          Set.member (negativeCaseId negativeCase) seedPortableFixtures
            && Map.member (negativeCaseEnvironmentProfile negativeCase) profiles)
        cases
      bindingProfilesDeclared = Map.keysSet bindings `Set.isSubsetOf` Map.keysSet profiles
      requirementProfilesDeclared = Map.keysSet requirements `Set.isSubsetOf` Map.keysSet profiles
      aliasProfilesDeclared = Map.keysSet aliases `Set.isSubsetOf` Map.keysSet profiles
      multibindingDomainExact = Map.keysSet bindings == Set.fromList
        [ "phase0.incompatible-join"
        , "phase0.parsed-validation-bypass"
        , "phase0.unrelated-length"
        , "phase0.premature-acceptance"
        , "phase0.pending-commit"
        , "phase0.pending-drop"
        , "phase0.stale-policy"
        , "phase0.opaque-proof"
        , "phase0.label-proof"
        ]
      requirementDomainExact = Map.keysSet requirements == Set.fromList
        [ "phase0.parsed-validation-bypass"
        , "phase0.premature-acceptance"
        , "phase0.stale-policy"
        ]
      sessionDomainExact = Map.keysSet sessions == Set.fromList
        [ "phase0.premature-acceptance"
        , "phase0.label-proof"
        , "phase0.server-upload"
        ]
      aliasDomainExact = Map.keysSet aliases == Set.fromList
        [ "phase0.pending-commit"
        , "phase0.pending-drop"
        ]
      staticClaimDomainExact = map portableStaticClaimName staticClaims == ["DigestMatches"]
      staticContextResult = materializePortableStaticContext staticClaims
      profilesResolve = case staticContextResult of
        Left _ -> False
        Right staticContext -> all
          (either (const False) (const True)
            . resolveProfileEnvironment staticContext sessions aliases requirements bindings profiles
            . negativeCaseEnvironmentProfile)
          cases
  filesPresent <- and <$> mapM doesFileExist paths
  certifiedSourcesPresent <- and <$> mapM doesFileExist certifiedSourcePaths
  report "20 frozen negative fixtures are manifest-owned" exactFrozenCount
  report "stable fixture IDs are unique" uniqueIds
  report "portable fixture paths are unique" uniquePaths
  report "every fixture names surface-check as competent layer" layersExact
  report "every fixture has typed non-meta governing authority references" authoritySyntaxValid
  report "manifest authority domain resolves exactly to portable registry" authorityDomainExact
  report "Matrix authority registry rows name the canonical Matrix source" matrixSourcesExact
  report "Certified authority registry rows name portable proof artifacts" certifiedSourcesPortable
  report "every Certified authority proof artifact exists" certifiedSourcesPresent
  report "every fixture names an explicit environment profile" profilesNamed
  report "portable environment set has exact frozen profile domain" seedProfileDomainExact
  report "portable extra bindings reference declared profiles" bindingProfilesDeclared
  report "portable requirements reference declared profiles" requirementProfilesDeclared
  report "portable aliases reference declared profiles" aliasProfilesDeclared
  report "portable extra-binding domain is exact for frozen corpus" multibindingDomainExact
  report "portable requirement domain is exact for frozen corpus" requirementDomainExact
  report "portable nested-session domain is exact for frozen corpus" sessionDomainExact
  report "portable type-alias domain is exact for frozen corpus" aliasDomainExact
  report "portable static claim domain is exact for frozen Phase 0" staticClaimDomainExact
  report "all 20 frozen fixtures use portable environment material" seedFixturesPortable
  report "every named environment profile resolves without compatibility fallback" profilesResolve
  report "every portable fixture path exists" filesPresent
  pure (and
    [ exactFrozenCount
    , uniqueIds
    , uniquePaths
    , layersExact
    , authoritySyntaxValid
    , authorityDomainExact
    , matrixSourcesExact
    , certifiedSourcesPortable
    , certifiedSourcesPresent
    , profilesNamed
    , seedProfileDomainExact
    , bindingProfilesDeclared
    , requirementProfilesDeclared
    , aliasProfilesDeclared
    , multibindingDomainExact
    , requirementDomainExact
    , sessionDomainExact
    , aliasDomainExact
    , staticClaimDomainExact
    , seedFixturesPortable
    , profilesResolve
    , filesPresent
    ])

'''
replace_between("checkIntegrity\n", "replayCase\n", new_integrity)

path.write_text(text)
print("applied INT-004 exact authority resolution decoder")
