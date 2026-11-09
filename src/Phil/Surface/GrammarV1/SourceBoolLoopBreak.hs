{-# LANGUAGE OverloadedStrings #-}

-- | FSEM-01 L-1: one source-checked loop break out of the header scope,
-- followed by an actual ordinary Surface terminal return. Break has zero
-- explicit exit slots; no dynamic loop evaluation or general CFG semantics.
module Phil.Surface.GrammarV1.SourceBoolLoopBreak
  ( GrammarV1SourceBoolLoopBreakError (..)
  , GrammarV1SourceBoolLoopBreakTrace (..)
  , grammarV1CheckedSourceBoolLoopBreakTrace
  ) where

import qualified Data.Map.Strict as Map
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Static (DeclarationKey, StaticContext)
import Phil.Core.Syntax (Mode (..), Name (..), Ty (..))
import Phil.Surface.Check.Engine
  ( SourceBoolJoinInvariant (..), SourceBoolLoopBreakRun (..)
  , checkSurfaceSourceBoolLoopBreakComponent
  , traceSurfaceSourceBoolLoopBreakComponent )
import Phil.Surface.Check.LoopControl
  ( LoopControlContract (..), LoopControlError
  , LoopControlKind (BreakControl), LoopControlSyntax (ExplicitLoopControl)
  , elaborateLoopControl )
import Phil.Surface.Check.Support (emptySurfaceState, shapeForType)
import Phil.Surface.Check.Types
  ( InitialBinding (..), SurfaceCheckError, SurfaceCheckResult
  , SurfaceEnvironment (..), emptySurfaceEnvironment )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderScopeError, GrammarV1ResolvedBinder (..)
  , grammarV1FunctionParameterScope )
import Phil.Surface.GrammarV1.CheckedType (grammarV1CheckedTypeMode)
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference (..) )
import Phil.Surface.GrammarV1.LoopStateScope
  ( GrammarV1CheckedLoopBodyStep (..), GrammarV1CheckedLoopSlot (..)
  , GrammarV1CheckedLoopState (..), GrammarV1LoopStateScopeError
  , grammarV1CheckedLoopExpressionInScope )
import Phil.Surface.GrammarV1.ParameterBodyScope
  ( GrammarV1CheckedLocalValueOccurrence (..)
  , grammarV1CheckedLocalValueOccurrenceInScope )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..), GrammarV1Expression (..)
  , GrammarV1FunctionDecl (..), GrammarV1Proposition (..)
  , GrammarV1RelationOperator (..), GrammarV1StateBinding (..)
  , GrammarV1Statement (..), GrammarV1TermParam (..) )
import Phil.Surface.Syntax
  ( Block (..), Component (..), Located (..), Statement (..)
  , SurfaceExpression (..) )

data GrammarV1SourceBoolLoopBreakError
  = BoolLoopBreakBinderError GrammarV1BinderScopeError
  | BoolLoopBreakScopeError GrammarV1LoopStateScopeError
  | BoolLoopBreakArityError LoopControlError
  deriving (Eq, Show)

-- | Real source-rooted binders, actual native Core resource checkpoints,
-- and the ordinary production Return/LinearCompletion outcome.
data GrammarV1SourceBoolLoopBreakTrace = GrammarV1SourceBoolLoopBreakTrace
  { boolLoopBreakSeedBinder :: GrammarV1ResolvedBinder
  , boolLoopBreakPayloadBinder :: GrammarV1ResolvedBinder
  , boolLoopBreakDebtBinder :: Maybe GrammarV1ResolvedBinder
  , boolLoopBreakHeaderBinder :: GrammarV1ResolvedBinder
  , boolLoopBreakEntryBinder :: GrammarV1ResolvedBinder
  , boolLoopBreakSlotCheckedMode :: CheckedTypeMode
  , boolLoopBreakInvariantProof :: SourceBoolJoinInvariant
  , boolLoopBreakNativeRun :: SourceBoolLoopBreakRun
  , boolLoopBreakCheckedOutcome :: Either SurfaceCheckError SurfaceCheckResult
  } deriving (Eq, Show)

-- | Bounded fragment: exactly two parameters (Bool seed and Linear Bytes
-- payload) or a third *source-declared* Linear Bytes debt owner for an exact
-- negative terminal-control case; result type equals payload Bytes[N].
-- One explicit Bool loop header, one zero-actual break, then return payload.
-- No caller-supplied ghost resource state or fabricated normal path.
grammarV1CheckedSourceBoolLoopBreakTrace
  :: StaticContext -> DeclarationKey -> GrammarV1FunctionDecl
  -> Maybe (Either GrammarV1SourceBoolLoopBreakError GrammarV1SourceBoolLoopBreakTrace)
grammarV1CheckedSourceBoolLoopBreakTrace staticContext fnKey fn
  | grammarV1FunctionRecursive fn = Nothing
  | not (null (grammarV1FunctionGenericParams fn)) = Nothing
  | not (null (grammarV1FunctionRequirements fn)) = Nothing
  | otherwise = do
      params <- case grammarV1FunctionTermParams fn of
        [seed,payload] -> Just (seed,payload,Nothing)
        [seed,payload,debt] -> Just (seed,payload,Just debt)
        _ -> Nothing
      let (Located _ seedParam,Located _ payloadParam,maybeDebtParam) = params
      result <- grammarV1FunctionResultType fn
      checks <- mapM
        (grammarV1CheckedTypeMode staticContext emptySurfaceState . locatedValue)
        ( [ grammarV1TermParamType seedParam
          , grammarV1TermParamType payloadParam
          , result ]
          ++ maybe [] (\(Located _ param) -> [grammarV1TermParamType param])
            maybeDebtParam )
      case sequence checks of
        Right [ (CheckedTypeMode TyBool Unrestricted, _)
              , (CheckedTypeMode payloadType Linear, _)
              , (CheckedTypeMode resultType Linear, _) ]
          | TyBytes _ <- payloadType
          , resultType == payloadType -> checkedBody payloadType Nothing
        Right [ (CheckedTypeMode TyBool Unrestricted, _)
              , (CheckedTypeMode payloadType Linear, _)
              , (CheckedTypeMode resultType Linear, _)
              , (CheckedTypeMode debtType Linear, _) ]
          | TyBytes _ <- payloadType
          , TyBytes _ <- debtType
          , resultType == payloadType -> checkedBody payloadType (Just debtType)
        _ -> Nothing
  where
    checkedBody payloadType maybeDebtType = do
      [ Located _ (GrammarV1ExpressionStatement loopSource)
        , Located returnedSpan (GrammarV1ReturnStatement sourceReturn) ] <-
        pure (grammarV1BlockStatements
          (locatedValue (grammarV1FunctionBody fn)))
      GrammarV1LoopExpression [slotSource] maybeInvariant _ <-
        pure (locatedValue loopSource)
      sourceType <- grammarV1StateBindingType (locatedValue slotSource)
      checkedSlot <- grammarV1CheckedTypeMode
        staticContext emptySurfaceState (locatedValue sourceType)
      case checkedSlot of
        Right (CheckedTypeMode TyBool Unrestricted, _) ->
          case grammarV1FunctionParameterScope fnKey fn of
            Left err -> Just (Left (BoolLoopBreakBinderError err))
            Right (parameterBinders, initialScope) -> do
              (seed,payload,maybeDebt) <- case parameterBinders of
                [one,two] | maybeDebtType == Nothing -> Just (one,two,Nothing)
                [one,two,three] | maybeDebtType /= Nothing ->
                  Just (one,two,Just three)
                _ -> Nothing
              result <- grammarV1CheckedLoopExpressionInScope
                initialScope loopSource
              case result of
                Left err -> Just (Left (BoolLoopBreakScopeError err))
                Right (loopState, afterLoop) -> do
                  [slot] <- pure (grammarV1CheckedLoopSlots loopState)
                  _ <- if null (grammarV1CheckedLoopSlotTypeReferences slot)
                    then Just () else Nothing
                  let header = grammarV1CheckedLoopSlotBinder slot
                      initializer = grammarV1StateBindingInitializer
                        (locatedValue slotSource)
                  [entryRef] <- pure
                    (grammarV1CheckedLoopSlotInitializerReferences slot)
                  entryBinder <- sourceOccurrence initialScope initializer
                    [seed,payload] entryRef
                  [GrammarV1CheckedLoopBreakStep _ actuals breakRefs] <-
                    pure (grammarV1CheckedLoopBodySteps loopState)
                  _ <- if length breakRefs == length actuals
                    then Just () else Nothing
                  checkedBreak <- Just (elaborateLoopControl
                    BreakControl
                    (LoopControlContract [semanticName header] [])
                    (ExplicitLoopControl actuals))
                  case checkedBreak of
                    Left err -> Just (Left (BoolLoopBreakArityError err))
                    Right [] -> do
                      returned <- grammarV1CheckedLocalValueOccurrenceInScope
                        afterLoop sourceReturn
                      _ <- if same
                        (grammarV1CheckedLocalValueBinder returned) payload
                        then Just () else Nothing
                      invariant <- invariantEvidence loopState header maybeInvariant
                      let span' = locatedSpan (grammarV1FunctionBody fn)
                          component = Located span' (Component
                            { componentName =
                                locatedValue (grammarV1FunctionName fn)
                            , componentParameters = []
                            , componentProvides = Nothing
                            , componentBody = Located span' (Block []) })
                          actualBindings =
                            [ (semanticName seed, InitialBinding
                                Unrestricted TyBool (shapeForType TyBool))
                            , (semanticName payload, InitialBinding
                                Linear payloadType (shapeForType payloadType))
                            ] ++
                            case (maybeDebt,maybeDebtType) of
                              (Just debt,Just ty) ->
                                [(semanticName debt, InitialBinding
                                  Linear ty (shapeForType ty))]
                              _ -> []
                          env = (emptySurfaceEnvironment staticContext)
                            { surfaceInitialBindings = Map.fromList actualBindings }
                          entryBlock = Located (locatedSpan initializer)
                            (Block [ Located (locatedSpan initializer)
                              (ExpressionStatement
                                (Located (locatedSpan initializer)
                                  (VariableExpression (semanticName entryBinder)))) ])
                          returnStatement = Located returnedSpan (ReturnStatement
                            (Located (locatedSpan sourceReturn)
                              (VariableExpression (semanticName payload))))
                          run = traceSurfaceSourceBoolLoopBreakComponent
                            env component entryBlock (locatedSpan loopSource)
                            (semanticName header) invariant [returnStatement]
                          ordinary = checkSurfaceSourceBoolLoopBreakComponent
                            env component entryBlock (locatedSpan loopSource)
                            (semanticName header) invariant [returnStatement]
                      if sourceBoolLoopBreakOutcome run /= ordinary
                        then Nothing
                        else Just (Right GrammarV1SourceBoolLoopBreakTrace
                          { boolLoopBreakSeedBinder = seed
                          , boolLoopBreakPayloadBinder = payload
                          , boolLoopBreakDebtBinder = maybeDebt
                          , boolLoopBreakHeaderBinder = header
                          , boolLoopBreakEntryBinder = entryBinder
                          , boolLoopBreakSlotCheckedMode =
                              CheckedTypeMode TyBool Unrestricted
                          , boolLoopBreakInvariantProof = invariant
                          , boolLoopBreakNativeRun = run
                          , boolLoopBreakCheckedOutcome = ordinary })
                    Right _ -> Nothing
        _ -> Nothing

    -- The exact source lexical occurrence, never source spelling or a
    -- trusted caller-injected Core key, selects the entry operand.
    sourceOccurrence scope source permitted recorded = do
      occurrence <- grammarV1CheckedLocalValueOccurrenceInScope scope source
      _ <- if locatedSpan (grammarV1CheckedLexicalReferenceSource recorded)
                == locatedSpan source then Just () else Nothing
      let target = grammarV1CheckedLocalValueBinder occurrence
      _ <- if same
        target (grammarV1CheckedLexicalReferenceBinder recorded)
        then Just () else Nothing
      case filter (same target) permitted of
        [one] -> Just one
        _ -> Nothing

    invariantEvidence checkedLoop header maybeInvariant = do
      proposition <- maybeInvariant
      case locatedValue proposition of
        GrammarV1TrueProposition
          | null (grammarV1CheckedLoopInvariantReferences checkedLoop) ->
              Just SourceBoolInvariantProvenTrue
        GrammarV1FalseProposition
          | null (grammarV1CheckedLoopInvariantReferences checkedLoop) ->
              Just SourceBoolInvariantUnproved
        GrammarV1RelationProposition _ (Located _ GrammarV1EqualRelation) _ ->
          case map grammarV1CheckedLexicalReferenceBinder
                (grammarV1CheckedLoopInvariantReferences checkedLoop) of
            [left,right]
              | same left header && same right header ->
                  Just SourceBoolInvariantProvenReflexive
              | otherwise -> Just SourceBoolInvariantUnproved
            _ -> Nothing
        _ -> Nothing

    semanticName = unName . grammarV1ResolvedBinderCoreName
    same a b = grammarV1ResolvedBinderKey a ==
      grammarV1ResolvedBinderKey b
