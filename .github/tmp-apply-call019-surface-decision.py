from pathlib import Path


def replace_once(path, old, new):
    p = Path(path)
    text = p.read_text()
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"expected exactly one match in {path}, got {count}")
    p.write_text(text.replace(old, new, 1))


replace_once(
    "src/Phil/Surface/Check/Types.hs",
    "  , ProviderOutcomeSpec (..)\n  , PrimitiveSemantics (..)\n",
    "  , ProviderOutcomeSpec (..)\n  , CallableOutcomeSpec (..)\n  , PrimitiveSemantics (..)\n",
)

replace_once(
    "src/Phil/Surface/Check/Types.hs",
    """data ProviderOutcomeSpec = ProviderOutcomeSpec
  { providerOutcomeLabel :: Text
  , providerOutcomePayload :: [(Mode, Ty)]
  }
  deriving (Eq, Ord, Show)

""",
    """data ProviderOutcomeSpec = ProviderOutcomeSpec
  { providerOutcomeLabel :: Text
  , providerOutcomePayload :: [(Mode, Ty)]
  }
  deriving (Eq, Ord, Show)

-- | Neutral source-level branch shape for an already checked callable.
-- Semantic outcome identity remains compiler-side; Surface receives only the
-- explicit labels and typed/mode-aware payload telescope needed by `decide`.
data CallableOutcomeSpec = CallableOutcomeSpec
  { callableOutcomeLabel :: Text
  , callableOutcomePayload :: [(Mode, Ty)]
  }
  deriving (Eq, Ord, Show)

""",
)

replace_once(
    "src/Phil/Surface/Check/Types.hs",
    "  , surfaceCallables :: Map Text SurfaceCallableSignature\n  , surfaceTypeAliases :: Map Text Ty\n",
    "  , surfaceCallables :: Map Text SurfaceCallableSignature\n  , surfaceCallableOutcomes :: Map DeclarationKey [CallableOutcomeSpec]\n  , surfaceTypeAliases :: Map Text Ty\n",
)

replace_once(
    "src/Phil/Surface/Check/Types.hs",
    "  , surfaceCallables = Map.empty\n  , surfaceTypeAliases = Map.empty\n",
    "  , surfaceCallables = Map.empty\n  , surfaceCallableOutcomes = Map.empty\n  , surfaceTypeAliases = Map.empty\n",
)

replace_once(
    "src/Phil/Surface/Check/Types.hs",
    "  | StoreDecision\n  | ProviderDecision [ProviderOutcomeSpec]\n",
    "  | StoreDecision\n  | ProviderDecision [ProviderOutcomeSpec]\n  | CallableDecision [CallableOutcomeSpec]\n",
)

replace_once(
    "src/Phil/Surface/Check.hs",
    "  , ProviderOutcomeSpec (..)\n  , PrimitiveSemantics (..)\n",
    "  , ProviderOutcomeSpec (..)\n  , CallableOutcomeSpec (..)\n  , PrimitiveSemantics (..)\n",
)

replace_once(
    "src/Phil/Surface/Check/Engine.hs",
    """      next <- foldM checkArgument state (zip parameters arguments)
      result <- callableResultValue signature
      Right [valuePath next result]
""",
    """      next <- foldM checkArgument state (zip parameters arguments)
      case Map.lookup
          (surfaceCallableDeclarationKey signature)
          (surfaceCallableOutcomes environment) of
        Nothing -> do
          result <- callableResultValue signature
          Right [valuePath next result]
        Just outcomes -> callableDecision next signature outcomes
""",
)

replace_once(
    "src/Phil/Surface/Check/Engine.hs",
    """    callableResultValue signature = case surfaceCallableResult signature of
      Nothing -> Right RuntimeUnit
      Just (mode, ty)
        | compareTypes ty TyUnit == DefinitionallyEqual ->
            if mode == Unrestricted
              then Right RuntimeUnit
              else throw located TypeMismatch
                "callable signature cannot return restricted Unit"
        | otherwise -> Right
            (RuntimeScalar (ScalarValue mode ty (shapeForType ty)))
""",
    """    callableResultValue signature = case surfaceCallableResult signature of
      Nothing -> Right RuntimeUnit
      Just (mode, ty)
        | compareTypes ty TyUnit == DefinitionallyEqual ->
            if mode == Unrestricted
              then Right RuntimeUnit
              else throw located TypeMismatch
                "callable signature cannot return restricted Unit"
        | otherwise -> Right
            (RuntimeScalar (ScalarValue mode ty (shapeForType ty)))

    callableDecision next signature outcomes = do
      when (null outcomes) $
        throw located TypeMismatch "callable decision declares no outcomes"
      let labels = map callableOutcomeLabel outcomes
      unless (Set.size (Set.fromList labels) == length labels) $
        throw located TypeMismatch "callable decision outcome labels are not unique"
      case surfaceCallableResult signature of
        Nothing -> Right
          [ valuePath next (RuntimeScalar
              (ScalarValue Unrestricted
                (TyOpaque "CallableDecision")
                (DecisionShape (CallableDecision outcomes))))
          ]
        Just _ -> throw located TypeMismatch
          "branch-dispatched callable cannot also expose one unbranched result"
""",
)

replace_once(
    "src/Phil/Surface/Check/Engine.hs",
    "  StoreDecision -> [\"failure\", \"success\"]\n  ProviderDecision outcomes -> map providerOutcomeLabel outcomes\n",
    "  StoreDecision -> [\"failure\", \"success\"]\n  ProviderDecision outcomes -> map providerOutcomeLabel outcomes\n  CallableDecision outcomes -> map callableOutcomeLabel outcomes\n",
)

replace_once(
    "src/Phil/Surface/Check/Engine.hs",
    """    (ProviderDecision outcomes, providerLabel, providerBinders) ->
      case
        [ providerOutcomePayload outcome
        | outcome <- outcomes
        , providerOutcomeLabel outcome == providerLabel
        ] of
        [payload]
          | length payload == length providerBinders ->
              foldM
                (\current (name, (mode, ty)) ->
                  insertBindingMeta (locatedSpan located) name
                    (BindingMeta mode ty (shapeForBinding name (shapeForType ty)))
                    current)
                state
                (zip providerBinders payload)
        _ -> throw located TypeMismatch
          "provider decision arm binder shape is incompatible with the declared outcome"
""",
    """    (ProviderDecision outcomes, providerLabel, providerBinders) ->
      case
        [ providerOutcomePayload outcome
        | outcome <- outcomes
        , providerOutcomeLabel outcome == providerLabel
        ] of
        [payload]
          | length payload == length providerBinders ->
              foldM
                (\current (name, (mode, ty)) ->
                  insertBindingMeta (locatedSpan located) name
                    (BindingMeta mode ty (shapeForBinding name (shapeForType ty)))
                    current)
                state
                (zip providerBinders payload)
        _ -> throw located TypeMismatch
          "provider decision arm binder shape is incompatible with the declared outcome"
    (CallableDecision outcomes, callableLabel, callableBinders) ->
      case
        [ callableOutcomePayload outcome
        | outcome <- outcomes
        , callableOutcomeLabel outcome == callableLabel
        ] of
        [payload]
          | length payload == length callableBinders ->
              foldM
                (\current (name, (mode, ty)) ->
                  insertBindingMeta (locatedSpan located) name
                    (BindingMeta mode ty (shapeForBinding name (shapeForType ty)))
                    current)
                state
                (zip callableBinders payload)
        _ -> throw located TypeMismatch
          "callable decision arm binder shape is incompatible with the declared outcome"
""",
)

replace_once(
    "src/Phil/Compiler/CallableOutcomeDispatch.hs",
    "  , planSurfaceCallableOutcomeDispatch\n",
    "  , planSurfaceCallableOutcomeDispatch\n  , installSurfaceCallableOutcomeDispatch\n",
)

replace_once(
    "src/Phil/Compiler/CallableOutcomeDispatch.hs",
    """import Phil.Core.Syntax
  ( Mode
  , Ty
  )
""",
    """import Phil.Core.Static (DeclarationKey)
import Phil.Core.Syntax
  ( Mode
  , Ty
  )
import Phil.Surface.Check
  ( CallableOutcomeSpec (..)
  , SurfaceCallableSignature (..)
  , SurfaceEnvironment (..)
  )
""",
)

replace_once(
    "src/Phil/Compiler/CallableOutcomeDispatch.hs",
    "  | SurfaceCallableDuplicateOutcomeLabel Text\n  deriving (Eq, Ord, Show)\n",
    """  | SurfaceCallableDuplicateOutcomeLabel Text
  | SurfaceCallableOutcomeUnknownSurfaceCallable Text
  | SurfaceCallableOutcomeDeclarationMismatch DeclarationKey DeclarationKey
  | SurfaceCallableOutcomeDispatchConflict DeclarationKey
  deriving (Eq, Ord, Show)
""",
)

p = Path("src/Phil/Compiler/CallableOutcomeDispatch.hs")
text = p.read_text()
insert_before = "outcomeControl :: CallableOutcomeClass -> SurfaceCallableOutcomeControl\n"
if text.count(insert_before) != 1:
    raise SystemExit("expected one outcomeControl insertion point")
addition = """-- | Install one already checked dispatch plan into the neutral Surface table.
-- The display spelling must still select the exact declaration identity retained
-- by the invocation witness. Reinstalling an identical plan is idempotent; a
-- different plan for the same declaration rejects rather than changing branch
-- meaning after checking.
installSurfaceCallableOutcomeDispatch
  :: SurfaceCallableOutcomeDispatchPlan
  -> SurfaceEnvironment
  -> Either SurfaceCallableOutcomeDispatchError SurfaceEnvironment
installSurfaceCallableOutcomeDispatch plan environment = do
  let invocation = surfaceOutcomeDispatchInvocation plan
      displayName = surfaceSemanticInvocationDisplayName invocation
      declarationKey = surfaceSemanticInvocationDeclarationKey invocation
      specs =
        [ CallableOutcomeSpec
            { callableOutcomeLabel = surfaceOutcomeBranchLabel branch
            , callableOutcomePayload = surfaceOutcomeBranchPayload branch
            }
        | branch <- surfaceOutcomeDispatchBranches plan
        ]
  signature <- maybe
    (Left (SurfaceCallableOutcomeUnknownSurfaceCallable displayName))
    Right
    (Map.lookup displayName (surfaceCallables environment))
  if surfaceCallableDeclarationKey signature == declarationKey
    then pure ()
    else Left
      (SurfaceCallableOutcomeDeclarationMismatch
        declarationKey
        (surfaceCallableDeclarationKey signature))
  case Map.lookup declarationKey (surfaceCallableOutcomes environment) of
    Nothing -> Right environment
      { surfaceCallableOutcomes =
          Map.insert declarationKey specs (surfaceCallableOutcomes environment)
      }
    Just existing
      | existing == specs -> Right environment
      | otherwise -> Left (SurfaceCallableOutcomeDispatchConflict declarationKey)

"""
p.write_text(text.replace(insert_before, addition + insert_before, 1))
