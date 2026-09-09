from pathlib import Path

path = Path("test/Phase1INT004PortableNegativeManifestMain.hs")
text = path.read_text()


def replace_once(old: str, new: str) -> None:
    global text
    if new in text:
        return
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"expected exactly one patch site, found {count}: {old[:80]!r}")
    text = text.replace(old, new, 1)


replace_once(
    "  ( Branch (..)\n  , Mode (..)\n",
    "  ( Branch (..)\n  , GrammarId (..)\n  , Mode (..)\n",
)

replace_once(
    "  , portablePrimitiveBindings :: Text\n  }\n",
    "  , portablePrimitiveBindings :: Text\n  , portableLegacyReceiveFrameRaw :: Text\n  }\n",
)

replace_once(
    '''seedPortableProfiles = Set.fromList\n  [ "phase0.simple-receive"\n  , "phase0.wrong-order"\n  , "phase0.nonexhaustive-offer"\n  ]\n''',
    '''seedPortableProfiles = Set.fromList\n  [ "phase0.simple-receive"\n  , "phase0.wrong-order"\n  , "phase0.nonexhaustive-offer"\n  , "phase0.legacy-raw"\n  , "phase0.failure-reuse"\n  ]\n''',
)

replace_once(
    '''seedPortableFixtures = Set.fromList\n  [ "P1-NEG-P0-001"\n  , "P1-NEG-P0-002"\n  , "P1-NEG-P0-003"\n  , "P1-NEG-P0-004"\n  ]\n''',
    '''seedPortableFixtures = Set.fromList\n  [ "P1-NEG-P0-001"\n  , "P1-NEG-P0-002"\n  , "P1-NEG-P0-003"\n  , "P1-NEG-P0-004"\n  , "P1-NEG-P0-005"\n  , "P1-NEG-P0-009"\n  ]\n''',
)

replace_once(
    '''      , "primitive_bindings"\n      ]\n''',
    '''      , "primitive_bindings"\n      , "legacy_receive_frame_raw"\n      ]\n''',
)

replace_once(
    '''  [profileId, bindingName, bindingMode, sessionKind, messageName, messageType, terminalOutcome, branches, primitiveBindings]\n    | any Text.null [profileId, bindingName, bindingMode, sessionKind, messageName, messageType, terminalOutcome, branches, primitiveBindings] ->\n''',
    '''  [profileId, bindingName, bindingMode, sessionKind, messageName, messageType, terminalOutcome, branches, primitiveBindings, legacyReceiveFrameRaw]\n    | any Text.null [profileId, bindingName, bindingMode, sessionKind, messageName, messageType, terminalOutcome, branches, primitiveBindings, legacyReceiveFrameRaw] ->\n''',
)

replace_once(
    '''        , portablePrimitiveBindings = primitiveBindings\n        }\n''',
    '''        , portablePrimitiveBindings = primitiveBindings\n        , portableLegacyReceiveFrameRaw = legacyReceiveFrameRaw\n        }\n''',
)

replace_once(
    '''materializePortableProfile profile = do\n  mode <- parsePortableMode (portableBindingMode profile)\n  session <- parsePortableSession profile\n  primitives <- parsePrimitiveBindings (portablePrimitiveBindings profile)\n  let binding = InitialBinding mode (TyEndpoint session) PlainShape\n  pure (emptySurfaceEnvironment emptyStaticContext)\n    { surfaceInitialBindings = Map.singleton (portableBindingName profile) binding\n    , surfacePrimitives = primitives\n    }\n''',
    '''materializePortableProfile profile = do\n  mode <- parsePortableMode (portableBindingMode profile)\n  session <- parsePortableSession profile\n  primitives <- parsePrimitiveBindings (portablePrimitiveBindings profile)\n  legacyReceiveFrameRaw <- parsePortableBool\n    "legacy_receive_frame_raw"\n    (portableLegacyReceiveFrameRaw profile)\n  let binding = InitialBinding mode (TyEndpoint session) PlainShape\n  pure (emptySurfaceEnvironment emptyStaticContext)\n    { surfaceInitialBindings = Map.singleton (portableBindingName profile) binding\n    , surfacePrimitives = primitives\n    , surfaceLegacyReceiveFrameRaw = legacyReceiveFrameRaw\n    }\n''',
)

replace_once(
    '''parsePortableMode value = case value of\n  "linear" -> Right Linear\n  "affine" -> Right Affine\n  "unrestricted" -> Right Unrestricted\n  _ -> Left ("unknown portable binding mode: " <> value)\n\nparsePortableSession :: PortableEnvironmentProfile -> Either Text Session\n''',
    '''parsePortableMode value = case value of\n  "linear" -> Right Linear\n  "affine" -> Right Affine\n  "unrestricted" -> Right Unrestricted\n  _ -> Left ("unknown portable binding mode: " <> value)\n\nparsePortableBool :: Text -> Text -> Either Text Bool\nparsePortableBool field value = case value of\n  "true" -> Right True\n  "false" -> Right False\n  _ -> Left ("invalid portable boolean for " <> field <> ": " <> value)\n\nparsePortableSession :: PortableEnvironmentProfile -> Either Text Session\n''',
)

replace_once(
    '''parsePortableType :: Text -> Either Text Ty\nparsePortableType value = case Text.stripPrefix "opaque:" value of\n  Just name | not (Text.null name) -> Right (TyOpaque name)\n  _ -> Left ("unsupported portable message type: " <> value)\n''',
    '''parsePortableType :: Text -> Either Text Ty\nparsePortableType value\n  | Just name <- Text.stripPrefix "opaque:" value\n  , not (Text.null name) = Right (TyOpaque name)\n  | Just grammar <- Text.stripPrefix "frame:" value\n  , not (Text.null grammar) = Right (TyFrame (GrammarId grammar))\n  | otherwise = Left ("unsupported portable message type: " <> value)\n''',
)

replace_once(
    '''parsePortableBranches value\n  | value == "-" = Left "offer session requires at least one branch"\n  | otherwise = traverse parseBranch (Text.splitOn ";" value)\n  where\n    parseBranch branchText = case Text.splitOn ":" branchText of\n      [label, outcome]\n        | not (Text.null label) && not (Text.null outcome) ->\n            Right (Branch label Nothing (End (Outcome outcome)))\n      _ -> Left ("invalid portable offer branch: " <> branchText)\n''',
    '''parsePortableBranches value\n  | value == "-" = Left "offer session requires at least one branch"\n  | otherwise = do\n      branches <- traverse parseBranch (Text.splitOn ";" value)\n      let labels = [label | Branch label _ _ <- branches]\n      if Set.size (Set.fromList labels) /= length labels\n        then Left "duplicate portable offer branch label"\n        else Right branches\n  where\n    parseBranch branchText = case Text.splitOn ":" branchText of\n      [label, outcome]\n        | not (Text.null label) && not (Text.null outcome) ->\n            Right (Branch label Nothing (End (Outcome outcome)))\n      _ -> Left ("invalid portable offer branch: " <> branchText)\n''',
)

replace_once(
    '''parsePrimitiveBindings value\n  | value == "-" = Right Map.empty\n  | otherwise = Map.fromList <$> traverse parsePrimitive (Text.splitOn ";" value)\n  where\n    parsePrimitive entry = case Text.splitOn ":" entry of\n      [name, "handle-payload"] | not (Text.null name) -> Right (name, PrimitiveHandlePayload)\n      _ -> Left ("unsupported portable primitive binding: " <> entry)\n''',
    '''parsePrimitiveBindings value\n  | value == "-" = Right Map.empty\n  | otherwise = do\n      bindings <- traverse parsePrimitive (Text.splitOn ";" value)\n      let result = Map.fromList bindings\n      if Map.size result /= length bindings\n        then Left "duplicate portable primitive binding name"\n        else Right result\n  where\n    parsePrimitive entry = case Text.splitOn ":" entry of\n      [name, "handle-payload"] | not (Text.null name) -> Right (name, PrimitiveHandlePayload)\n      _ -> Left ("unsupported portable primitive binding: " <> entry)\n''',
)

replace_once(
    '''  case profile of\n    "phase0.legacy-raw" -> legacy "05-raw-field-access.phil"\n    "phase0.parsed-validation-bypass" -> legacy "06-parsed-used-as-validated.phil"\n''',
    '''  case profile of\n    "phase0.parsed-validation-bypass" -> legacy "06-parsed-used-as-validated.phil"\n''',
)

replace_once(
    '''    "phase0.incompatible-join" -> legacy "08-incompatible-branch-join.phil"\n    "phase0.failure-reuse" -> legacy "09-continue-after-fatal-recognition-failure.phil"\n    "phase0.premature-acceptance" -> legacy "10-accept-before-digest-check.phil"\n''',
    '''    "phase0.incompatible-join" -> legacy "08-incompatible-branch-join.phil"\n    "phase0.premature-acceptance" -> legacy "10-accept-before-digest-check.phil"\n''',
)

replace_once(
    '  report "fixtures 001-004 use portable environment material" seedFixturesPortable\n',
    '  report "fixtures 001-005 and 009 use portable environment material" seedFixturesPortable\n',
)

path.write_text(text)
