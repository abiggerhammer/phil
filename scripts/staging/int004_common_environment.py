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
    '''  , "phase0.failure-reuse"\n  ]\n''',
    '''  , "phase0.failure-reuse"\n  , "phase0.common"\n  ]\n''',
)

replace_once(
    '''  , "P1-NEG-P0-009"\n  ]\n''',
    '''  , "P1-NEG-P0-009"\n  , "P1-NEG-P0-011"\n  , "P1-NEG-P0-012"\n  , "P1-NEG-P0-014"\n  , "P1-NEG-P0-016"\n  , "P1-NEG-P0-020"\n  ]\n''',
)

replace_once(
    '''materializePortableProfile profile = do\n  mode <- parsePortableMode (portableBindingMode profile)\n  session <- parsePortableSession profile\n  primitives <- parsePrimitiveBindings (portablePrimitiveBindings profile)\n  legacyReceiveFrameRaw <- parsePortableBool\n    "legacy_receive_frame_raw"\n    (portableLegacyReceiveFrameRaw profile)\n  let binding = InitialBinding mode (TyEndpoint session) PlainShape\n  pure (emptySurfaceEnvironment emptyStaticContext)\n    { surfaceInitialBindings = Map.singleton (portableBindingName profile) binding\n    , surfacePrimitives = primitives\n    , surfaceLegacyReceiveFrameRaw = legacyReceiveFrameRaw\n    }\n''',
    '''materializePortableProfile profile = do\n  bindings <- materializePortableBindings profile\n  primitives <- parsePrimitiveBindings (portablePrimitiveBindings profile)\n  legacyReceiveFrameRaw <- parsePortableBool\n    "legacy_receive_frame_raw"\n    (portableLegacyReceiveFrameRaw profile)\n  pure (emptySurfaceEnvironment emptyStaticContext)\n    { surfaceInitialBindings = bindings\n    , surfacePrimitives = primitives\n    , surfaceLegacyReceiveFrameRaw = legacyReceiveFrameRaw\n    }\n\nmaterializePortableBindings\n  :: PortableEnvironmentProfile\n  -> Either Text (Map Text InitialBinding)\nmaterializePortableBindings profile =\n  case portableSessionKind profile of\n    "none" -> do\n      requireDash "binding_name" (portableBindingName profile)\n      requireDash "binding_mode" (portableBindingMode profile)\n      requireDash "message_name" (portableMessageName profile)\n      requireDash "message_type" (portableMessageType profile)\n      requireDash "terminal_outcome" (portableTerminalOutcome profile)\n      requireDash "branches" (portableBranches profile)\n      Right Map.empty\n    _ -> do\n      bindingName <- requireValue "binding_name" (portableBindingName profile)\n      mode <- parsePortableMode (portableBindingMode profile)\n      session <- parsePortableSession profile\n      let binding = InitialBinding mode (TyEndpoint session) PlainShape\n      Right (Map.singleton bindingName binding)\n''',
)

replace_once(
    '''    parsePrimitive entry = case Text.splitOn ":" entry of\n      [name, "handle-payload"] | not (Text.null name) -> Right (name, PrimitiveHandlePayload)\n      _ -> Left ("unsupported portable primitive binding: " <> entry)\n''',
    '''    parsePrimitive entry = case Text.splitOn ":" entry of\n      [name, semantic] | not (Text.null name) ->\n        case semantic of\n          "handle-payload" -> Right (name, PrimitiveHandlePayload)\n          "authorize-store" -> Right (name, PrimitiveAuthorizeStore)\n          "delegate" -> Right (name, PrimitiveDelegate)\n          "new-cancellation-scope" -> Right (name, PrimitiveNewCancellationScope)\n          "allocate-linear-buffer" -> Right (name, PrimitiveAllocateLinearBuffer)\n          "inspect" -> Right (name, PrimitiveInspect)\n          "unchecked-u32-add" -> Right (name, PrimitiveUncheckedU32Add)\n          _ -> Left ("unsupported portable primitive semantic: " <> semantic)\n      _ -> Left ("unsupported portable primitive binding: " <> entry)\n''',
)

replace_once(
    '''    "phase0.premature-acceptance" -> legacy "10-accept-before-digest-check.phil"\n    "phase0.common" -> legacy "11-copy-authority-capability.phil"\n    "phase0.pending-commit" -> legacy "13-commit-unrelated-parsed.phil"\n''',
    '''    "phase0.premature-acceptance" -> legacy "10-accept-before-digest-check.phil"\n    "phase0.pending-commit" -> legacy "13-commit-unrelated-parsed.phil"\n''',
)

replace_once(
    '  report "fixtures 001-005 and 009 use portable environment material" seedFixturesPortable\n',
    '  report "fixtures 001-005, 009, 011, 012, 014, 016, and 020 use portable environment material" seedFixturesPortable\n',
)

path.write_text(text)
