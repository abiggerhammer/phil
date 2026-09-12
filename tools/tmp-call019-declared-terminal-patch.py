from pathlib import Path


def replace(path, old, new):
    p = Path(path)
    text = p.read_text()
    if old not in text:
        if new in text:
            return
        raise SystemExit(f"missing replacement anchor in {path}: {old[:80]!r}")
    p.write_text(text.replace(old, new, 1))

# Surface neutral control carrier.
replace(
    "src/Phil/Surface/Check/Types.hs",
    "  , ProviderOutcomeSpec (..)\n  , CallableOutcomeSpec (..)\n",
    "  , ProviderOutcomeSpec (..)\n  , CallableOutcomeControlSpec (..)\n  , CallableOutcomeSpec (..)\n",
)
replace(
    "src/Phil/Surface/Check/Types.hs",
    '''-- | Neutral source-level branch shape for an already checked callable.\n-- Semantic outcome identity remains compiler-side; Surface receives only the\n-- explicit labels and typed/mode-aware payload telescope needed by `decide`.\ndata CallableOutcomeSpec = CallableOutcomeSpec\n  { callableOutcomeLabel :: Text\n  , callableOutcomePayload :: [(Mode, Ty)]\n  }\n  deriving (Eq, Ord, Show)\n''',
    '''-- | Neutral caller-control shape for an already checked callable outcome.\n-- Surface may continue ordinary checking or close with the exact declared\n-- terminal outcome. Fatal control remains outside this carrier until Core has\n-- an exact fatal `Control` constructor.\ndata CallableOutcomeControlSpec\n  = CallableOutcomeContinues\n  | CallableOutcomeCloses Outcome\n  deriving (Eq, Ord, Show)\n\n-- | Neutral source-level branch shape for an already checked callable.\n-- Semantic outcome identity remains compiler-side; Surface receives only the\n-- explicit label, typed/mode-aware payload telescope, and exact representable\n-- caller-control shape needed by `decide`.\ndata CallableOutcomeSpec = CallableOutcomeSpec\n  { callableOutcomeLabel :: Text\n  , callableOutcomePayload :: [(Mode, Ty)]\n  , callableOutcomeControl :: CallableOutcomeControlSpec\n  }\n  deriving (Eq, Ord, Show)\n''',
)

replace(
    "src/Phil/Surface/Check.hs",
    "  , ProviderOutcomeSpec (..)\n  , CallableOutcomeSpec (..)\n",
    "  , ProviderOutcomeSpec (..)\n  , CallableOutcomeControlSpec (..)\n  , CallableOutcomeSpec (..)\n",
)

# Compiler-side installation maps exact declared-terminal identity into Surface.
replace(
    "src/Phil/Compiler/CallableOutcomeDispatch.hs",
    "import Phil.Surface.Check\n  ( CallableOutcomeSpec (..)\n",
    "import Phil.Surface.Check\n  ( CallableOutcomeControlSpec (..)\n  , CallableOutcomeSpec (..)\n",
)
replace(
    "src/Phil/Compiler/CallableOutcomeDispatch.hs",
    '''  | SurfaceCallableOutcomeControlRequiresSurfaceRepresentation\n      CallableOutcomeClass\n      SurfaceCallableOutcomeControl\n  deriving (Eq, Ord, Show)\n''',
    '''  | SurfaceCallableOutcomeControlRequiresSurfaceRepresentation\n      CallableOutcomeClass\n      SurfaceCallableOutcomeControl\n  | SurfaceCallableTerminalOutcomePayloadUnsupported CallableOutcomeClass\n  | SurfaceCallableOutcomeControlMismatch\n      CallableOutcomeClass\n      SurfaceCallableOutcomeControl\n  deriving (Eq, Ord, Show)\n''',
)
replace(
    "src/Phil/Compiler/CallableOutcomeDispatch.hs",
    '''-- The current neutral Surface carrier represents only branch labels and payload\n-- telescopes, so it is competent only for branches that really continue caller\n-- checking. Declared-terminal and fatal callable outcomes must reject here until\n-- Surface has an exact terminal-control carrier; silently installing either as\n-- an ordinary decision arm would invent a continuation forbidden by CALL-019.\ninstallSurfaceCallableOutcomeDispatch\n  :: SurfaceCallableOutcomeDispatchPlan\n  -> SurfaceEnvironment\n  -> Either SurfaceCallableOutcomeDispatchError SurfaceEnvironment\ninstallSurfaceCallableOutcomeDispatch plan environment = do\n  mapM_ requireSurfaceRepresentable (surfaceOutcomeDispatchBranches plan)\n  let invocation = surfaceOutcomeDispatchInvocation plan\n      displayName = surfaceSemanticInvocationDisplayName invocation\n      declarationKey = surfaceSemanticInvocationDeclarationKey invocation\n      specs =\n        [ CallableOutcomeSpec\n            { callableOutcomeLabel = surfaceOutcomeBranchLabel branch\n            , callableOutcomePayload = surfaceOutcomeBranchPayload branch\n            }\n        | branch <- surfaceOutcomeDispatchBranches plan\n        ]\n''',
    '''-- Surface can now represent ordinary continuation and exact declared-terminal\n-- closure. Terminal outcomes cannot expose a caller payload because there is no\n-- continuation in which such a payload could be bound. Fatal outcomes still\n-- reject here: Core's current `Control` has no exact fatal constructor, so using\n-- generic `Failed` would invent a failure class and violate CALL-019.\ninstallSurfaceCallableOutcomeDispatch\n  :: SurfaceCallableOutcomeDispatchPlan\n  -> SurfaceEnvironment\n  -> Either SurfaceCallableOutcomeDispatchError SurfaceEnvironment\ninstallSurfaceCallableOutcomeDispatch plan environment = do\n  specs <- mapM surfaceSpec (surfaceOutcomeDispatchBranches plan)\n  let invocation = surfaceOutcomeDispatchInvocation plan\n      displayName = surfaceSemanticInvocationDisplayName invocation\n      declarationKey = surfaceSemanticInvocationDeclarationKey invocation\n''',
)
replace(
    "src/Phil/Compiler/CallableOutcomeDispatch.hs",
    '''requireSurfaceRepresentable\n  :: SurfaceCallableOutcomeBranch\n  -> Either SurfaceCallableOutcomeDispatchError ()\nrequireSurfaceRepresentable branch =\n  case surfaceOutcomeBranchControl branch of\n    SurfaceCallableOutcomeContinues -> Right ()\n    control -> Left\n      (SurfaceCallableOutcomeControlRequiresSurfaceRepresentation\n        (surfaceOutcomeBranchClass branch)\n        control)\n\noutcomeControl :: CallableOutcomeClass -> SurfaceCallableOutcomeControl\n''',
    '''surfaceSpec\n  :: SurfaceCallableOutcomeBranch\n  -> Either SurfaceCallableOutcomeDispatchError CallableOutcomeSpec\nsurfaceSpec branch =\n  case (surfaceOutcomeBranchControl branch, surfaceOutcomeBranchClass branch) of\n    (SurfaceCallableOutcomeContinues, CallableSuccessOutcome) ->\n      Right (continuingSpec branch)\n    (SurfaceCallableOutcomeContinues,\n        CallableNonSuccessOutcome (CallableTypedNegative _)) ->\n      Right (continuingSpec branch)\n    (SurfaceCallableOutcomeDeclaredTerminal,\n        CallableNonSuccessOutcome (CallableDeclaredTerminal outcome))\n      | null (surfaceOutcomeBranchPayload branch) ->\n          Right CallableOutcomeSpec\n            { callableOutcomeLabel = surfaceOutcomeBranchLabel branch\n            , callableOutcomePayload = []\n            , callableOutcomeControl = CallableOutcomeCloses outcome\n            }\n      | otherwise -> Left\n          (SurfaceCallableTerminalOutcomePayloadUnsupported\n            (surfaceOutcomeBranchClass branch))\n    (SurfaceCallableOutcomeFatalTerminal,\n        CallableNonSuccessOutcome (CallableFatal _)) -> Left\n          (SurfaceCallableOutcomeControlRequiresSurfaceRepresentation\n            (surfaceOutcomeBranchClass branch)\n            SurfaceCallableOutcomeFatalTerminal)\n    (control, outcomeClass) -> Left\n      (SurfaceCallableOutcomeControlMismatch outcomeClass control)\n\ncontinuingSpec :: SurfaceCallableOutcomeBranch -> CallableOutcomeSpec\ncontinuingSpec branch = CallableOutcomeSpec\n  { callableOutcomeLabel = surfaceOutcomeBranchLabel branch\n  , callableOutcomePayload = surfaceOutcomeBranchPayload branch\n  , callableOutcomeControl = CallableOutcomeContinues\n  }\n\noutcomeControl :: CallableOutcomeClass -> SurfaceCallableOutcomeControl\n''',
)

# Surface decision arms respect exact declared-terminal control.
replace(
    "src/Phil/Surface/Check/Engine.hs",
    '''checkDecisionArm environment state decision locatedArm = do\n  let pattern' = caseArmPattern (locatedValue locatedArm)\n  withBinders <- bindDecisionPattern\n    state\n    decision\n    (casePatternLabel pattern')\n    (casePatternBinders pattern')\n    locatedArm\n  checkScopedValueBlock\n    environment\n    state\n    withBinders\n    (caseArmBody (locatedValue locatedArm))\n\ndecisionLabels :: DecisionKind -> [Text]\n''',
    '''checkDecisionArm environment state decision locatedArm = do\n  let pattern' = caseArmPattern (locatedValue locatedArm)\n      label = casePatternLabel pattern'\n  case callableDecisionControl decision label of\n    Just (CallableOutcomeCloses outcome) ->\n      checkDeclaredTerminalCallableArm environment state outcome locatedArm\n    _ -> do\n      withBinders <- bindDecisionPattern\n        state\n        decision\n        label\n        (casePatternBinders pattern')\n        locatedArm\n      checkScopedValueBlock\n        environment\n        state\n        withBinders\n        (caseArmBody (locatedValue locatedArm))\n\ncallableDecisionControl :: DecisionKind -> Text -> Maybe CallableOutcomeControlSpec\ncallableDecisionControl decision label = case decision of\n  CallableDecision outcomes -> case\n      [ callableOutcomeControl outcome\n      | outcome <- outcomes\n      , callableOutcomeLabel outcome == label\n      ] of\n    [control] -> Just control\n    _ -> Nothing\n  _ -> Nothing\n\ncheckDeclaredTerminalCallableArm\n  :: SurfaceEnvironment\n  -> SurfaceState\n  -> Outcome\n  -> Located CaseArm\n  -> Either SurfaceCheckError [SurfacePath]\ncheckDeclaredTerminalCallableArm environment state outcome locatedArm = do\n  let pattern' = caseArmPattern (locatedValue locatedArm)\n      body = caseArmBody (locatedValue locatedArm)\n  unless (null (casePatternBinders pattern')) $\n    throw locatedArm TypeMismatch\n      "declared-terminal callable outcome cannot bind a caller payload"\n  unless (null (blockStatements (locatedValue body))) $\n    throw locatedArm ControlAfterTerminal\n      "declared-terminal callable outcome arm cannot continue"\n  ensureTerminalState environment (locatedSpan locatedArm) (Just outcome) state\n  Right [SurfacePath (PathClosed outcome) state Nothing]\n\ndecisionLabels :: DecisionKind -> [Text]\n''',
)
replace(
    "src/Phil/Surface/Check/Engine.hs",
    '''    (CallableDecision outcomes, callableLabel, callableBinders) ->\n      case\n        [ callableOutcomePayload outcome\n        | outcome <- outcomes\n        , callableOutcomeLabel outcome == callableLabel\n        ] of\n''',
    '''    (CallableDecision outcomes, callableLabel, callableBinders) ->\n      case\n        [ callableOutcomePayload outcome\n        | outcome <- outcomes\n        , callableOutcomeLabel outcome == callableLabel\n        , callableOutcomeControl outcome == CallableOutcomeContinues\n        ] of\n''',
)

# Update #971 boundary fixture: declared terminal is now representable; fatal remains closed.
replace(
    "test/Phase1CALL019OutcomeControlBoundaryMain.hs",
    '''import Phil.Surface.Check\n  ( SurfaceCallableSignature (..)\n''',
    '''import Phil.Surface.Check\n  ( CallableOutcomeControlSpec (..)\n  , CallableOutcomeSpec (..)\n  , SurfaceCallableSignature (..)\n''',
)
replace(
    "test/Phase1CALL019OutcomeControlBoundaryMain.hs",
    '''    , test "CALL-019 declared-terminal outcome rejects before Surface installation"\n        declaredTerminalRejects\n''',
    '''    , test "CALL-019 declared-terminal outcome installs exact close control"\n        declaredTerminalInstalls\n''',
)
start = '''declaredTerminalRejects :: Either String ()\ndeclaredTerminalRejects = do\n  let outcomes = [outcome "success" successClass, outcome "closed" terminalClass]\n      bindings = Map.fromList\n        [ (successClass, binding successClass "ok")\n        , (terminalClass, binding terminalClass "closed")\n        ]\n  plan <- mapLeft show (planSurfaceCallableOutcomeDispatch bindings (account outcomes))\n  expectControlError\n    terminalClass\n    SurfaceCallableOutcomeDeclaredTerminal\n    (installSurfaceCallableOutcomeDispatch plan environment)\n\n'''
new = '''declaredTerminalInstalls :: Either String ()\ndeclaredTerminalInstalls = do\n  let outcomes = [outcome "success" successClass, outcome "closed" terminalClass]\n      bindings = Map.fromList\n        [ (successClass, binding successClass "ok")\n        , (terminalClass, binding terminalClass "closed")\n        ]\n  plan <- mapLeft show (planSurfaceCallableOutcomeDispatch bindings (account outcomes))\n  installed <- mapLeft show (installSurfaceCallableOutcomeDispatch plan environment)\n  case Map.lookup workerKey (surfaceCallableOutcomes installed) of\n    Just [successSpec, terminalSpec]\n      | callableOutcomeControl successSpec == CallableOutcomeContinues\n          && callableOutcomeControl terminalSpec\n            == CallableOutcomeCloses (Outcome "closed") -> Right ()\n      | otherwise -> Left\n          ("wrong installed controls: "\n            <> show (callableOutcomeControl successSpec, callableOutcomeControl terminalSpec))\n    other -> Left ("unexpected installed outcomes: " <> show other)\n\n'''
replace("test/Phase1CALL019OutcomeControlBoundaryMain.hs", start, new)

print("CALL-019 declared-terminal surface-control patch applied")
