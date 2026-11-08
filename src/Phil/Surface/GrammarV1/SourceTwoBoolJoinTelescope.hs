{-# LANGUAGE OverloadedStrings #-}

-- | FSEM-01: bounded source-checked TWO-SLOT Bool join telescope. The two
-- branch tuple operands come from exact source lexical binders, are checked
-- through production Surface, and are not assumed equal on opposite arms.
module Phil.Surface.GrammarV1.SourceTwoBoolJoinTelescope
  ( GrammarV1TwoBoolJoinError (..)
  , GrammarV1TwoBoolJoinTrace (..)
  , grammarV1CheckedTwoBoolJoinTelescopeTrace
  ) where

import qualified Data.Map.Strict as Map
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Static (DeclarationKey, StaticContext)
import Phil.Core.Syntax (Mode (..), Name (..), Ty (..))
import Phil.Surface.Check.Engine
  ( SourceBoolJoinInvariant (..), SourceTwoBoolJoinRun (..)
  , checkSurfaceSourceTwoBoolJoinComponent
  , traceSurfaceSourceTwoBoolJoinComponent )
import Phil.Surface.Check.Support (emptySurfaceState, shapeForType)
import Phil.Surface.Check.Types
  ( InitialBinding (..), SurfaceCheckError, SurfaceCheckResult
  , SurfaceEnvironment (..), emptySurfaceEnvironment )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderScopeError, GrammarV1ResolvedBinder (..)
  , grammarV1FunctionParameterScope )
import Phil.Surface.GrammarV1.CheckedType (grammarV1CheckedTypeMode)
import Phil.Surface.GrammarV1.JoinStateScope
  ( GrammarV1CheckedIfBranch (..), GrammarV1CheckedJoinClause (..)
  , GrammarV1CheckedJoinExpression (..), GrammarV1CheckedJoinSlot (..)
  , GrammarV1JoinStateScopeError, grammarV1CheckedJoinExpressionInScope )
import Phil.Surface.GrammarV1.LetPatternScope
  ( GrammarV1CheckedLetScopeStep (..) )
import Phil.Surface.GrammarV1.ParameterBodyScope
  ( GrammarV1CheckedLocalValueOccurrence (..)
  , grammarV1CheckedLocalValueOccurrenceInScope )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..), GrammarV1Expression (..)
  , GrammarV1FunctionDecl (..), GrammarV1JoinClause (..)
  , GrammarV1Proposition (..), GrammarV1RelationOperator (..)
  , GrammarV1StateSlot (..), GrammarV1Statement (..)
  , GrammarV1TermParam (..) )
import Phil.Surface.Syntax
  ( Block (..), Component (..), Located (..), Statement (..)
  , SurfaceExpression (..) )

data GrammarV1TwoBoolJoinError
  = TwoBoolJoinBinderError GrammarV1BinderScopeError
  | TwoBoolJoinScopeError GrammarV1JoinStateScopeError
  deriving (Eq, Show)

-- | Source identities and real (not synthesized) native states. Each slot is
-- typed independently, and both source uses are independently scope checked.
data GrammarV1TwoBoolJoinTrace = GrammarV1TwoBoolJoinTrace
  { twoBoolJoinFlagBinder :: GrammarV1ResolvedBinder
  , twoBoolJoinAlternativeBinder :: GrammarV1ResolvedBinder
  , twoBoolJoinPayloadBinder :: GrammarV1ResolvedBinder
  , twoBoolJoinFirstSlotBinder :: GrammarV1ResolvedBinder
  , twoBoolJoinSecondSlotBinder :: GrammarV1ResolvedBinder
  , twoBoolJoinSlotCheckedModes :: [CheckedTypeMode]
  , twoBoolJoinInvariantProof :: SourceBoolJoinInvariant
  , twoBoolJoinBranchRun :: SourceTwoBoolJoinRun
  , twoBoolJoinCheckedOutcome :: Either SurfaceCheckError SurfaceCheckResult
  } deriving (Eq, Show)

-- | The bounded fragment is non-generic and nonrecursive. It has exactly
-- (Bool, Bool, Bytes[N]) parameters, two branches each ending in a flat tuple
-- of two already checked parameter occurrences, two Unrestricted Bool slots,
-- two post-join uses, and return of the Linear payload once. No dependent
-- type or runtime phi evaluation is assumed.
grammarV1CheckedTwoBoolJoinTelescopeTrace
  :: StaticContext -> DeclarationKey -> GrammarV1FunctionDecl
  -> Maybe (Either GrammarV1TwoBoolJoinError GrammarV1TwoBoolJoinTrace)
grammarV1CheckedTwoBoolJoinTelescopeTrace staticContext fnKey functionDecl
  | grammarV1FunctionRecursive functionDecl = Nothing
  | not (null (grammarV1FunctionGenericParams functionDecl)) = Nothing
  | not (null (grammarV1FunctionRequirements functionDecl)) = Nothing
  | otherwise = do
      [Located _ flagParam,Located _ alternativeParam,Located _ payloadParam] <-
        pure (grammarV1FunctionTermParams functionDecl)
      sourceResult <- grammarV1FunctionResultType functionDecl
      checked <- mapM
        (grammarV1CheckedTypeMode staticContext emptySurfaceState . locatedValue)
        [ grammarV1TermParamType flagParam
        , grammarV1TermParamType alternativeParam
        , grammarV1TermParamType payloadParam
        , sourceResult ]
      case sequence checked of
        Right
          [ (CheckedTypeMode TyBool Unrestricted, _)
          , (CheckedTypeMode TyBool Unrestricted, _)
          , (CheckedTypeMode payloadType Linear, _)
          , (CheckedTypeMode resultType Linear, _) ]
            | TyBytes _ <- payloadType
            , payloadType == resultType -> checkedSourceBody payloadType
        _ -> Nothing
  where
    checkedSourceBody payloadType = do
      [ Located _ (GrammarV1ExpressionStatement sourceIf)
        , Located useFirstSpan (GrammarV1ExpressionStatement sourceUseFirst)
        , Located useSecondSpan (GrammarV1ExpressionStatement sourceUseSecond)
        , Located returnSpan (GrammarV1ReturnStatement sourceReturn) ] <-
        pure (grammarV1BlockStatements
          (locatedValue (grammarV1FunctionBody functionDecl)))
      GrammarV1IfExpression _ (Just joinSource) _ (Just _) <-
        pure (locatedValue sourceIf)
      [firstSlot,secondSlot] <- pure
        (grammarV1JoinState (locatedValue joinSource))
      slotModes <- mapM
        (grammarV1CheckedTypeMode staticContext emptySurfaceState .
          locatedValue . grammarV1StateSlotType . locatedValue)
        [firstSlot,secondSlot]
      case sequence slotModes of
        Right [ (CheckedTypeMode TyBool Unrestricted, _)
              , (CheckedTypeMode TyBool Unrestricted, _) ] ->
          case grammarV1FunctionParameterScope fnKey functionDecl of
            Left err -> Just (Left (TwoBoolJoinBinderError err))
            Right ([flagBinder,alternativeBinder,payloadBinder],sourceScope) -> do
              checked <- grammarV1CheckedJoinExpressionInScope sourceScope sourceIf
              case checked of
                Left err -> Just (Left (TwoBoolJoinScopeError err))
                Right (GrammarV1CheckedIfJoinExpression scrutinee
                       thenSource (Just elseSource) joinClause, successorScope) -> do
                  _ <- if same
                    (grammarV1CheckedLocalValueBinder scrutinee) flagBinder
                       then Just () else Nothing
                  [checkedFirst,checkedSecond] <- pure
                    (grammarV1CheckedJoinSlots joinClause)
                  _ <- if all
                    (null . grammarV1CheckedJoinSlotTypeReferences)
                    [checkedFirst,checkedSecond]
                    then Just () else Nothing
                  let boundFirst = grammarV1CheckedJoinSlotBinder checkedFirst
                      boundSecond = grammarV1CheckedJoinSlotBinder checkedSecond
                      permitted = [flagBinder,alternativeBinder,payloadBinder]
                  leftBlock <- bridgePair permitted thenSource
                  rightBlock <- bridgePair permitted elseSource
                  useFirst <- grammarV1CheckedLocalValueOccurrenceInScope
                    successorScope sourceUseFirst
                  useSecond <- grammarV1CheckedLocalValueOccurrenceInScope
                    successorScope sourceUseSecond
                  returned <- grammarV1CheckedLocalValueOccurrenceInScope
                    successorScope sourceReturn
                  _ <- if same
                         (grammarV1CheckedLocalValueBinder useFirst) boundFirst
                     && same
                         (grammarV1CheckedLocalValueBinder useSecond) boundSecond
                     && same
                         (grammarV1CheckedLocalValueBinder returned) payloadBinder
                    then Just () else Nothing
                  invariant <- classifyInvariant successorScope
                    [boundFirst,boundSecond]
                    (grammarV1JoinInvariant (locatedValue joinSource))
                  _ <- if invariantRefsConsistent
                    (grammarV1JoinInvariant (locatedValue joinSource))
                    (grammarV1CheckedJoinInvariantReferences joinClause)
                    then Just () else Nothing
                  let span' = locatedSpan (grammarV1FunctionBody functionDecl)
                      component = Located span' (Component
                        { componentName =
                            locatedValue (grammarV1FunctionName functionDecl)
                        , componentParameters = []
                        , componentProvides = Nothing
                        , componentBody = Located span' (Block []) })
                      env = (emptySurfaceEnvironment staticContext)
                        { surfaceInitialBindings = Map.fromList
                            [ (semanticName flagBinder, InitialBinding
                                Unrestricted TyBool (shapeForType TyBool))
                            , (semanticName alternativeBinder, InitialBinding
                                Unrestricted TyBool (shapeForType TyBool))
                            , (semanticName payloadBinder, InitialBinding
                                Linear payloadType (shapeForType payloadType))
                            ]
                        }
                      postSource =
                        [ variableUse useFirstSpan sourceUseFirst boundFirst
                        , variableUse useSecondSpan sourceUseSecond boundSecond
                        , Located returnSpan (ReturnStatement
                            (Located (locatedSpan sourceReturn)
                              (VariableExpression (semanticName payloadBinder))))
                        ]
                      joinSpan = locatedSpan joinSource
                      run = traceSurfaceSourceTwoBoolJoinComponent
                        env component leftBlock rightBlock joinSpan
                        (semanticName boundFirst) (semanticName boundSecond)
                        invariant postSource
                      ordinary = checkSurfaceSourceTwoBoolJoinComponent
                        env component leftBlock rightBlock joinSpan
                        (semanticName boundFirst) (semanticName boundSecond)
                        invariant postSource
                  if sourceTwoBoolJoinOutcome run /= ordinary
                    then Nothing
                    else Just (Right GrammarV1TwoBoolJoinTrace
                      { twoBoolJoinFlagBinder = flagBinder
                      , twoBoolJoinAlternativeBinder = alternativeBinder
                      , twoBoolJoinPayloadBinder = payloadBinder
                      , twoBoolJoinFirstSlotBinder = boundFirst
                      , twoBoolJoinSecondSlotBinder = boundSecond
                      , twoBoolJoinSlotCheckedModes =
                          [CheckedTypeMode TyBool Unrestricted,
                           CheckedTypeMode TyBool Unrestricted]
                      , twoBoolJoinInvariantProof = invariant
                      , twoBoolJoinBranchRun = run
                      , twoBoolJoinCheckedOutcome = ordinary
                      })
                Right _ -> Nothing
            Right _ -> Nothing
        _ -> Nothing

    variableUse statementSpan source binder =
      Located statementSpan (ExpressionStatement
        (Located (locatedSpan source)
          (VariableExpression (semanticName binder))))

    -- Each actual source tuple occurrence was checked in its predecessor's
    -- child lexical frame, before any post-join binder exists.
    bridgePair permitted branch = do
      [ GrammarV1CheckedLetOccurrenceStep leftStatement firstOccurrence
        , GrammarV1CheckedLetOccurrenceStep rightStatement secondOccurrence
        ] <- pure (grammarV1CheckedIfBranchSteps branch)
      _ <- if leftStatement == rightStatement then Just () else Nothing
      Located statementSpan (GrammarV1ExpressionStatement sourceTuple) <-
        Just leftStatement
      GrammarV1TupleExpression [firstSource,secondSource] <-
        Just (locatedValue sourceTuple)
      _ <- if grammarV1CheckedLocalValueSource firstOccurrence == firstSource
           && grammarV1CheckedLocalValueSource secondOccurrence == secondSource
             then Just () else Nothing
      firstBinder <- findExact permitted
        (grammarV1CheckedLocalValueBinder firstOccurrence)
      secondBinder <- findExact permitted
        (grammarV1CheckedLocalValueBinder secondOccurrence)
      Just (Located (locatedSpan (grammarV1CheckedIfBranchSource branch))
        (Block [Located statementSpan (ExpressionStatement
          (Located (locatedSpan sourceTuple) (TupleExpression
            [ Located (locatedSpan firstSource)
                (VariableExpression (semanticName firstBinder))
            , Located (locatedSpan secondSource)
                (VariableExpression (semanticName secondBinder))
            ])))]))

    classifyInvariant scope slots maybeInvariant = do
      source <- maybeInvariant
      case locatedValue source of
        GrammarV1TrueProposition -> Just SourceBoolInvariantProvenTrue
        GrammarV1FalseProposition -> Just SourceBoolInvariantUnproved
        GrammarV1RelationProposition lhs (Located _ GrammarV1EqualRelation) rhs -> do
          left <- grammarV1CheckedLocalValueOccurrenceInScope scope lhs
          right <- grammarV1CheckedLocalValueOccurrenceInScope scope rhs
          let leftBinder = grammarV1CheckedLocalValueBinder left
              rightBinder = grammarV1CheckedLocalValueBinder right
          if same leftBinder rightBinder
            && any (same leftBinder) slots
            then Just SourceBoolInvariantProvenReflexive
            else Just SourceBoolInvariantUnproved
        _ -> Nothing

    -- The lexical join checker resolves references AFTER both slots exist.
    -- Only literal propositions have zero references in this bounded adapter.
    invariantRefsConsistent maybeInvariant refs =
      case fmap locatedValue maybeInvariant of
        Just GrammarV1TrueProposition -> null refs
        Just GrammarV1FalseProposition -> null refs
        Just (GrammarV1RelationProposition _ _ _) -> not (null refs)
        _ -> False

    findExact known target = case filter (same target) known of
      [one] -> Just one
      _ -> Nothing
    semanticName = unName . grammarV1ResolvedBinderCoreName
    same a b = grammarV1ResolvedBinderKey a ==
      grammarV1ResolvedBinderKey b
