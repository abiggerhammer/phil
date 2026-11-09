{-# LANGUAGE OverloadedStrings #-}

-- | FSEM-01 L-1: a bounded real parsed-source LoopStateScope → production
-- Surface/Core resource checkpoint bridge for a single Unrestricted Bool
-- header state and one explicit continue backedge. No runtime repetition.
module Phil.Surface.GrammarV1.SourceBoolLoopResource
  ( GrammarV1SourceBoolLoopError (..)
  , GrammarV1SourceBoolLoopTrace (..)
  , grammarV1CheckedSourceBoolLoopTrace
  ) where

import qualified Data.Map.Strict as Map
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Static (DeclarationKey, StaticContext)
import Phil.Core.Syntax (Mode (..), Name (..), Ty (..))
import Phil.Surface.Check.Engine
  ( SourceBoolJoinInvariant (..), SourceBoolLoopRun (..)
  , checkSurfaceSourceBoolLoopComponent
  , traceSurfaceSourceBoolLoopComponent )
import Phil.Surface.Check.LoopControl
  ( LoopControlContract (..), LoopControlError
  , LoopControlKind (ContinueControl)
  , LoopControlSyntax (ExplicitLoopControl), elaborateLoopControl )
import Phil.Surface.Check.Support (emptySurfaceState, shapeForType)
import Phil.Surface.Check.Types
  ( InitialBinding (..), SurfaceCheckError, SurfaceEnvironment (..)
  , emptySurfaceEnvironment )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderScopeError, GrammarV1ResolvedBinder (..)
  , grammarV1FunctionParameterScope )
import Phil.Surface.GrammarV1.CheckedType (grammarV1CheckedTypeMode)
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference (..) )
import Phil.Surface.GrammarV1.LoopStateScope
  ( GrammarV1CheckedLoopBodyStep (..)
  , GrammarV1CheckedLoopSlot (..), GrammarV1CheckedLoopState (..)
  , GrammarV1LoopStateScopeError, grammarV1CheckedLoopExpressionInScope )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..), GrammarV1Expression (..)
  , GrammarV1FunctionDecl (..), GrammarV1Proposition (..)
  , GrammarV1RelationOperator (..), GrammarV1StateBinding (..)
  , GrammarV1Statement (..), GrammarV1TermParam (..) )
import Phil.Surface.Syntax
  ( Block (..), Component (..), Located (..), Statement (..)
  , SurfaceExpression (..) )

data GrammarV1SourceBoolLoopError
  = BoolLoopBinderError GrammarV1BinderScopeError
  | BoolLoopScopeError GrammarV1LoopStateScopeError
  | BoolLoopArityError LoopControlError
  deriving (Eq, Show)

-- | Only the source-checked declaration roots determine the Core names.
-- Input/header/backedge resource contexts are actual native checker cuts.
data GrammarV1SourceBoolLoopTrace = GrammarV1SourceBoolLoopTrace
  { boolLoopSeedBinder :: GrammarV1ResolvedBinder
  , boolLoopAlternativeBinder :: GrammarV1ResolvedBinder
  , boolLoopPayloadBinder :: GrammarV1ResolvedBinder
  , boolLoopHeaderBinder :: GrammarV1ResolvedBinder
  , boolLoopEntryBinder :: GrammarV1ResolvedBinder
  , boolLoopBackedgeBinder :: GrammarV1ResolvedBinder
  , boolLoopHeaderCheckedMode :: CheckedTypeMode
  , boolLoopInvariantProof :: SourceBoolJoinInvariant
  , boolLoopNativeRun :: SourceBoolLoopRun
  , boolLoopCheckedOutcome :: Either SurfaceCheckError ()
  } deriving (Eq, Show)

-- | Admitted static fragment:
--   nonrecursive, nongeneric fn(seed:Bool, alternative:Bool,
--   payload:Bytes[N])->Unit satisfies C { loop state(cursor:Bool = seed)
--   invariant cursor==cursor { continue(alternative); }; }
-- Actual init/backedge operands may independently name either Bool parameter,
-- the new header, or the Linear spectator (which must fail TypeMismatch).
-- The sole unconditional continue has no normal terminal successor.
grammarV1CheckedSourceBoolLoopTrace
  :: StaticContext -> DeclarationKey -> GrammarV1FunctionDecl
  -> Maybe (Either GrammarV1SourceBoolLoopError GrammarV1SourceBoolLoopTrace)
grammarV1CheckedSourceBoolLoopTrace staticContext fnKey fn
  | grammarV1FunctionRecursive fn = Nothing
  | not (null (grammarV1FunctionGenericParams fn)) = Nothing
  | not (null (grammarV1FunctionRequirements fn)) = Nothing
  | otherwise = do
      [Located _ seedParam,Located _ alternativeParam,Located _ payloadParam] <-
        pure (grammarV1FunctionTermParams fn)
      resultType <- grammarV1FunctionResultType fn
      checked <- mapM
        (grammarV1CheckedTypeMode staticContext emptySurfaceState . locatedValue)
        [ grammarV1TermParamType seedParam
        , grammarV1TermParamType alternativeParam
        , grammarV1TermParamType payloadParam
        , resultType ]
      case sequence checked of
        Right [ (CheckedTypeMode TyBool Unrestricted, _)
              , (CheckedTypeMode TyBool Unrestricted, _)
              , (CheckedTypeMode payloadType Linear, _)
              , (CheckedTypeMode TyUnit Unrestricted, _) ]
          | TyBytes _ <- payloadType -> sourceLoop payloadType
        _ -> Nothing
  where
    sourceLoop payloadType = do
      [Located _ (GrammarV1ExpressionStatement loopSource)] <-
        pure (grammarV1BlockStatements
          (locatedValue (grammarV1FunctionBody fn)))
      GrammarV1LoopExpression [locatedState] invariant _ <-
        pure (locatedValue loopSource)
      typedSource <- grammarV1StateBindingType (locatedValue locatedState)
      checkedSlotTy <- grammarV1CheckedTypeMode
        staticContext emptySurfaceState (locatedValue typedSource)
      case checkedSlotTy of
        Right (CheckedTypeMode TyBool Unrestricted, _) ->
          case grammarV1FunctionParameterScope fnKey fn of
            Left err -> Just (Left (BoolLoopBinderError err))
            Right ([seed,alternative,payload],initialScope) -> do
              loopScope <- grammarV1CheckedLoopExpressionInScope
                initialScope loopSource
              case loopScope of
                Left err -> Just (Left (BoolLoopScopeError err))
                Right (checkedLoop, _afterLoop) -> do
                  [checkedSlot] <- pure (grammarV1CheckedLoopSlots checkedLoop)
                  _ <- if null (grammarV1CheckedLoopSlotTypeReferences checkedSlot)
                    then Just () else Nothing
                  let header = grammarV1CheckedLoopSlotBinder checkedSlot
                      initializer = grammarV1StateBindingInitializer
                        (locatedValue locatedState)
                  [initRef] <- pure
                    (grammarV1CheckedLoopSlotInitializerReferences checkedSlot)
                  initBinder <- exactReference [seed,alternative,payload]
                    initializer initRef
                  [GrammarV1CheckedLoopContinueStep _ actuals continueRefs] <-
                    pure (grammarV1CheckedLoopBodySteps checkedLoop)
                  actualResult <- Just (elaborateLoopControl
                    ContinueControl (LoopControlContract [semanticName header] [])
                    (ExplicitLoopControl actuals))
                  case actualResult of
                    Left err -> Just (Left (BoolLoopArityError err))
                    Right [backedgeSource] -> do
                      [backedgeRef] <- pure continueRefs
                      backedgeBinder <- exactReference
                        [seed,alternative,payload,header] backedgeSource backedgeRef
                      proof <- checkInvariant checkedLoop header invariant
                      let span' = locatedSpan (grammarV1FunctionBody fn)
                          component = Located span' (Component
                            { componentName =
                                locatedValue (grammarV1FunctionName fn)
                            , componentParameters = []
                            , componentProvides = Nothing
                            , componentBody = Located span' (Block []) })
                          env = (emptySurfaceEnvironment staticContext)
                            { surfaceInitialBindings = Map.fromList
                                [ (semanticName seed, InitialBinding
                                    Unrestricted TyBool (shapeForType TyBool))
                                , (semanticName alternative, InitialBinding
                                    Unrestricted TyBool (shapeForType TyBool))
                                , (semanticName payload, InitialBinding
                                    Linear payloadType (shapeForType payloadType))
                                ] }
                          entryBlock = sourceValueBlock initializer initBinder
                          backedgeBlock =
                            sourceValueBlock backedgeSource backedgeBinder
                          loopSpan = locatedSpan loopSource
                          native = traceSurfaceSourceBoolLoopComponent
                            env component entryBlock backedgeBlock loopSpan
                            (semanticName header) proof
                          ordinary = checkSurfaceSourceBoolLoopComponent
                            env component entryBlock backedgeBlock loopSpan
                            (semanticName header) proof
                      if sourceBoolLoopOutcome native /= ordinary
                        then Nothing
                        else Just (Right GrammarV1SourceBoolLoopTrace
                          { boolLoopSeedBinder = seed
                          , boolLoopAlternativeBinder = alternative
                          , boolLoopPayloadBinder = payload
                          , boolLoopHeaderBinder = header
                          , boolLoopEntryBinder = initBinder
                          , boolLoopBackedgeBinder = backedgeBinder
                          , boolLoopHeaderCheckedMode =
                              CheckedTypeMode TyBool Unrestricted
                          , boolLoopInvariantProof = proof
                          , boolLoopNativeRun = native
                          , boolLoopCheckedOutcome = ordinary })
                    Right _ -> Nothing
            Right _ -> Nothing
        _ -> Nothing

    sourceValueBlock source binder =
      Located (locatedSpan source) (Block
        [ Located (locatedSpan source) (ExpressionStatement
            (Located (locatedSpan source)
              (VariableExpression (semanticName binder)))) ])

    -- LoopStateScope's reference walk supplies source spans and exact
    -- declaration-rooted binders. Bare local variables alone are admitted.
    -- Static/global and unsupported source expressions are not guessed.
    exactReference permitted expression reference = do
      _ <- if locatedSpan (grammarV1CheckedLexicalReferenceSource reference)
               == locatedSpan expression then Just () else Nothing
      let target = grammarV1CheckedLexicalReferenceBinder reference
      case filter (same target) permitted of
        [binder] -> Just binder
        _ -> Nothing

    -- Lexical invariant references are resolved AFTER the header exists.
    -- Only true or the exact reflexive source header equality is justified.
    checkInvariant checkedLoop header maybeInvariant = do
      source <- maybeInvariant
      case locatedValue source of
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
