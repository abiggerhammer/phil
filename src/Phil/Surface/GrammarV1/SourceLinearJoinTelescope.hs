{-# LANGUAGE OverloadedStrings #-}

-- | FSEM-01 J-5: one parsed-source Linear Bytes[N] join-state slot.
-- Both predecessor values must move the EXACT source owner through the
-- ordinary Surface resource checker before joinExclusive and insertion
-- of a fresh post-join Linear binder. Not an arbitrary-branch elaborator.
module Phil.Surface.GrammarV1.SourceLinearJoinTelescope
  ( GrammarV1LinearJoinError (..)
  , GrammarV1LinearJoinTrace (..)
  , grammarV1CheckedLinearJoinTelescopeTrace
  ) where

import qualified Data.Map.Strict as Map
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Static (DeclarationKey, StaticContext)
import Phil.Core.Syntax (Mode (..), Name (..), Ty (..))
import Phil.Surface.Check.Engine
  ( SourceBoolJoinInvariant (..), SourceLinearJoinRun (..)
  , checkSurfaceSourceLinearJoinComponent
  , traceSurfaceSourceLinearJoinComponent )
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

data GrammarV1LinearJoinError
  = LinearJoinBinderError GrammarV1BinderScopeError
  | LinearJoinScopeError GrammarV1JoinStateScopeError
  deriving (Eq, Show)

data GrammarV1LinearJoinTrace = GrammarV1LinearJoinTrace
  { linearJoinFlagBinder :: GrammarV1ResolvedBinder
  , linearJoinPayloadBinder :: GrammarV1ResolvedBinder
  , linearJoinSlotBinder :: GrammarV1ResolvedBinder
  , linearJoinThenBinder :: GrammarV1ResolvedBinder
  , linearJoinElseBinder :: GrammarV1ResolvedBinder
  , linearJoinReturnBinder :: GrammarV1ResolvedBinder
  , linearJoinSlotCheckedMode :: CheckedTypeMode
  , linearJoinInvariantProof :: SourceBoolJoinInvariant
  , linearJoinNativeRun :: SourceLinearJoinRun
  , linearJoinCheckedOutcome :: Either SurfaceCheckError SurfaceCheckResult
  } deriving (Eq, Show)

-- | Deliberately bounded nonrecursive, non-generic source fragment:
--
-- fn choose(flag:Bool,payload:Bytes[N])->Bytes[N] satisfies C {
--   if flag join state (selected:Bytes[N]) invariant true {
--     payload;
--   } else {
--     payload;
--   };
--   return selected;
-- }
--
-- Both branches have separate static resource states, yet the owner moves
-- once on EACH branch. On successful native join the prior owner is spent,
-- and a genuinely fresh Linear slot exists. The source may instead return
-- the spent payload, producing a real StructuralUse refusal. An incorrect
-- slot width or Boolean actual produces a real TypeMismatch. This adapter
-- never assumes an arbitrary invariant or produces a runtime phi.
grammarV1CheckedLinearJoinTelescopeTrace
  :: StaticContext -> DeclarationKey -> GrammarV1FunctionDecl
  -> Maybe (Either GrammarV1LinearJoinError GrammarV1LinearJoinTrace)
grammarV1CheckedLinearJoinTelescopeTrace staticContext fnKey fn
  | grammarV1FunctionRecursive fn = Nothing
  | not (null (grammarV1FunctionGenericParams fn)) = Nothing
  | not (null (grammarV1FunctionRequirements fn)) = Nothing
  | otherwise = do
      [Located _ flagParam,Located _ payloadParam] <-
        pure (grammarV1FunctionTermParams fn)
      resultSource <- grammarV1FunctionResultType fn
      checked <- mapM
        (grammarV1CheckedTypeMode staticContext emptySurfaceState . locatedValue)
        [grammarV1TermParamType flagParam,
         grammarV1TermParamType payloadParam,resultSource]
      case sequence checked of
        Right [ (CheckedTypeMode TyBool Unrestricted,_)
              , (CheckedTypeMode payloadTy Linear,_)
              , (CheckedTypeMode resultTy Linear,_) ]
          | TyBytes _ <- payloadTy
          , resultTy == payloadTy -> checkedBody payloadTy
        _ -> Nothing
  where
    checkedBody payloadTy = do
      [ Located _ (GrammarV1ExpressionStatement sourceIf)
        , Located returnSpan (GrammarV1ReturnStatement sourceReturn) ] <-
        pure (grammarV1BlockStatements
          (locatedValue (grammarV1FunctionBody fn)))
      GrammarV1IfExpression _ (Just joinSource) _ (Just _) <-
        pure (locatedValue sourceIf)
      [locatedSlot] <- pure (grammarV1JoinState (locatedValue joinSource))
      let sourceSlot = locatedValue locatedSlot
      checkedSlot <- grammarV1CheckedTypeMode
        staticContext emptySurfaceState
        (locatedValue (grammarV1StateSlotType sourceSlot))
      case checkedSlot of
        Right (CheckedTypeMode slotTy Linear,_)
          | TyBytes _ <- slotTy ->
            case grammarV1FunctionParameterScope fnKey fn of
              Left err -> Just (Left (LinearJoinBinderError err))
              Right ([flag,payload],sourceScope) -> do
                checkedJoin <- grammarV1CheckedJoinExpressionInScope
                  sourceScope sourceIf
                case checkedJoin of
                  Left err -> Just (Left (LinearJoinScopeError err))
                  Right (GrammarV1CheckedIfJoinExpression scrutinee
                         leftSource (Just rightSource) joinClause,
                         successorScope) -> do
                    _ <- if same
                       (grammarV1CheckedLocalValueBinder scrutinee) flag
                      then Just () else Nothing
                    [slot] <- pure (grammarV1CheckedJoinSlots joinClause)
                    _ <- if null (grammarV1CheckedJoinSlotTypeReferences slot)
                      then Just () else Nothing
                    let selected = grammarV1CheckedJoinSlotBinder slot
                    (leftBlock,leftBinder) <- bridgePredecessor
                      [flag,payload] leftSource
                    (rightBlock,rightBinder) <- bridgePredecessor
                      [flag,payload] rightSource
                    returned <- grammarV1CheckedLocalValueOccurrenceInScope
                      successorScope sourceReturn
                    let returnBinder = grammarV1CheckedLocalValueBinder returned
                    _ <- if same returnBinder selected
                          || same returnBinder payload
                      then Just () else Nothing
                    invariant <- checkInvariant successorScope selected
                      (grammarV1JoinInvariant (locatedValue joinSource))
                      (grammarV1CheckedJoinInvariantReferences joinClause)
                    let span' = locatedSpan (grammarV1FunctionBody fn)
                        component = Located span' (Component
                          { componentName =
                              locatedValue (grammarV1FunctionName fn)
                          , componentParameters = []
                          , componentProvides = Nothing
                          , componentBody = Located span' (Block []) })
                        env = (emptySurfaceEnvironment staticContext)
                          { surfaceInitialBindings = Map.fromList
                              [ (semanticName flag, InitialBinding
                                  Unrestricted TyBool (shapeForType TyBool))
                              , (semanticName payload, InitialBinding
                                  Linear payloadTy (shapeForType payloadTy))
                              ] }
                        postSource =
                          [Located returnSpan (ReturnStatement
                            (Located (locatedSpan sourceReturn)
                              (VariableExpression (semanticName returnBinder))))]
                        joinSpan = locatedSpan joinSource
                        replay = traceSurfaceSourceLinearJoinComponent
                          env component leftBlock rightBlock joinSpan
                          (semanticName selected) slotTy invariant postSource
                        ordinary = checkSurfaceSourceLinearJoinComponent
                          env component leftBlock rightBlock joinSpan
                          (semanticName selected) slotTy invariant postSource
                    if sourceLinearJoinOutcome replay /= ordinary
                      then Nothing
                      else Just (Right GrammarV1LinearJoinTrace
                        { linearJoinFlagBinder = flag
                        , linearJoinPayloadBinder = payload
                        , linearJoinSlotBinder = selected
                        , linearJoinThenBinder = leftBinder
                        , linearJoinElseBinder = rightBinder
                        , linearJoinReturnBinder = returnBinder
                        , linearJoinSlotCheckedMode = CheckedTypeMode slotTy Linear
                        , linearJoinInvariantProof = invariant
                        , linearJoinNativeRun = replay
                        , linearJoinCheckedOutcome = ordinary })
                  Right _ -> Nothing
              Right _ -> Nothing
        _ -> Nothing

    bridgePredecessor permitted branch = do
      [GrammarV1CheckedLetOccurrenceStep
        (Located statementSpan (GrammarV1ExpressionStatement source))
        occurrence] <- pure (grammarV1CheckedIfBranchSteps branch)
      binder <- findExact permitted
        (grammarV1CheckedLocalValueBinder occurrence)
      let body = Located
            (locatedSpan (grammarV1CheckedIfBranchSource branch))
            (Block [Located statementSpan (ExpressionStatement
              (Located (locatedSpan source)
                (VariableExpression (semanticName binder))))])
      Just (body,binder)

    -- A literal true or reflexive identity has an independently recognized
    -- proof shape; false retains MissingEvidence, not an invented discharge.
    checkInvariant scope selected maybeInvariant checkedReferences = do
      source <- maybeInvariant
      case locatedValue source of
        GrammarV1TrueProposition
          | null checkedReferences -> Just SourceBoolInvariantProvenTrue
        GrammarV1FalseProposition
          | null checkedReferences -> Just SourceBoolInvariantUnproved
        GrammarV1RelationProposition lhs (Located _ GrammarV1EqualRelation) rhs -> do
          left <- grammarV1CheckedLocalValueOccurrenceInScope scope lhs
          right <- grammarV1CheckedLocalValueOccurrenceInScope scope rhs
          if same (grammarV1CheckedLocalValueBinder left) selected
            && same (grammarV1CheckedLocalValueBinder right) selected
            then Just SourceBoolInvariantProvenReflexive
            else Just SourceBoolInvariantUnproved
        _ -> Nothing

    findExact known target =
      case filter (same target) known of
        [one] -> Just one
        _ -> Nothing

    semanticName = unName . grammarV1ResolvedBinderCoreName
    same a b = grammarV1ResolvedBinderKey a ==
      grammarV1ResolvedBinderKey b
