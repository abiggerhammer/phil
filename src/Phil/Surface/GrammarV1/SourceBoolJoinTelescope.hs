{-# LANGUAGE OverloadedStrings #-}

-- | FSEM-01: bounded parsed-source one-slot Bool join telescope. Source
-- binder authority checks both predecessor scopes before allocating the
-- post-join slot; actual predecessor Bool values and resources enter the
-- production checkValueBlock / joinContinuing / insertBindingMeta path.
module Phil.Surface.GrammarV1.SourceBoolJoinTelescope
  ( GrammarV1BoolJoinError (..)
  , GrammarV1BoolJoinTrace (..)
  , grammarV1CheckedBoolJoinTelescopeTrace
  ) where

import qualified Data.Map.Strict as Map
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Static (DeclarationKey, StaticContext)
import Phil.Core.Syntax (Mode (..), Name (..), Ty (..))
import Phil.Surface.Check.Engine
  ( SourceBoolJoinInvariant (..), SourceBoolJoinRun (..)
  , checkSurfaceSourceBoolJoinComponent
  , traceSurfaceSourceBoolJoinComponent )
import Phil.Surface.Check.Support (emptySurfaceState, shapeForType)
import Phil.Surface.Check.Types
  ( InitialBinding (..), SurfaceCheckError, SurfaceCheckResult
  , SurfaceEnvironment (..), emptySurfaceEnvironment )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderScopeError, GrammarV1ResolvedBinder (..)
  , grammarV1FunctionParameterScope )
import Phil.Surface.GrammarV1.CheckedType (grammarV1CheckedTypeMode)
import Phil.Surface.GrammarV1.JoinStateScope
  ( GrammarV1CheckedIfBranch (..)
  , GrammarV1CheckedJoinClause (..)
  , GrammarV1CheckedJoinExpression (..)
  , GrammarV1CheckedJoinSlot (..)
  , GrammarV1JoinStateScopeError
  , grammarV1CheckedJoinExpressionInScope )
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
  ( Block (..), Component (..), Located (..)
  , Statement (..), SurfaceExpression (..) )

data GrammarV1BoolJoinError
  = BoolJoinBinderError GrammarV1BinderScopeError
  | BoolJoinScopeError GrammarV1JoinStateScopeError
  deriving (Eq, Show)

-- | A test-observable, source-checked record. The source declaration
-- determines every Core identity and type; predecessor values and resource
-- maps come only from ordinary production checking, not synthetic fixtures.
data GrammarV1BoolJoinTrace = GrammarV1BoolJoinTrace
  { boolJoinFlagBinder :: GrammarV1ResolvedBinder
  , boolJoinOtherBinder :: GrammarV1ResolvedBinder
  , boolJoinPayloadBinder :: GrammarV1ResolvedBinder
  , boolJoinSlotBinder :: GrammarV1ResolvedBinder
  , boolJoinSlotCheckedMode :: CheckedTypeMode
  , boolJoinInvariantProof :: SourceBoolJoinInvariant
  , boolJoinBranchRun :: SourceBoolJoinRun
  , boolJoinCheckedOutcome :: Either SurfaceCheckError SurfaceCheckResult
  } deriving (Eq, Show)

-- | The one-slot fragment is deliberately NON-GENERIC and nonrecursive:
-- fn(flag:Bool,other:Bool,payload:Bytes[N])->Bytes[N], one two-arm if
-- with source "join state (selected : Bool)" and an explicit invariant.
-- Each predecessor's final value MUST be an existing checked source
-- parameter occurrence. The successor uses the exact new selected binder,
-- then returns the exact original linear payload.
--
-- No arbitrary invariant is trusted: literal true and reflexive equality
-- of the same checked selected binder have finite syntactic proof.
-- False or non-reflexive checked equalities carry an unproved marker,
-- which the production checker rejects as MissingEvidence.
grammarV1CheckedBoolJoinTelescopeTrace
  :: StaticContext -> DeclarationKey -> GrammarV1FunctionDecl
  -> Maybe (Either GrammarV1BoolJoinError GrammarV1BoolJoinTrace)
grammarV1CheckedBoolJoinTelescopeTrace staticContext fnKey functionDecl
  | grammarV1FunctionRecursive functionDecl = Nothing
  | not (null (grammarV1FunctionGenericParams functionDecl)) = Nothing
  | not (null (grammarV1FunctionRequirements functionDecl)) = Nothing
  | otherwise = do
      [Located _ flagParam,Located _ otherParam,Located _ payloadParam] <-
        pure (grammarV1FunctionTermParams functionDecl)
      sourceResult <- grammarV1FunctionResultType functionDecl
      checked <- mapM
        (grammarV1CheckedTypeMode staticContext emptySurfaceState . locatedValue)
        [ grammarV1TermParamType flagParam
        , grammarV1TermParamType otherParam
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
        , Located useSpan (GrammarV1ExpressionStatement sourceUse)
        , Located returnSpan (GrammarV1ReturnStatement sourceReturn) ] <-
        pure (grammarV1BlockStatements
          (locatedValue (grammarV1FunctionBody functionDecl)))
      GrammarV1IfExpression _ (Just joinSource) _ (Just _) <-
        pure (locatedValue sourceIf)
      [locatedSlot] <- pure
        (grammarV1JoinState (locatedValue joinSource))
      let sourceSlot = locatedValue locatedSlot
      checkedSlotType <- grammarV1CheckedTypeMode
        staticContext emptySurfaceState
        (locatedValue (grammarV1StateSlotType sourceSlot))
      case checkedSlotType of
        Right (CheckedTypeMode TyBool Unrestricted, _) -> do
          case grammarV1FunctionParameterScope fnKey functionDecl of
            Left err -> Just (Left (BoolJoinBinderError err))
            Right ([flagBinder,otherBinder,payloadBinder],sourceScope) -> do
              checked <- grammarV1CheckedJoinExpressionInScope sourceScope sourceIf
              case checked of
                Left err -> Just (Left (BoolJoinScopeError err))
                Right (GrammarV1CheckedIfJoinExpression scrutinee
                       thenSource (Just elseSource) joinClause, successorScope) -> do
                  _ <- if same
                    (grammarV1CheckedLocalValueBinder scrutinee) flagBinder
                       then Just () else Nothing
                  [checkedSlot] <- pure (grammarV1CheckedJoinSlots joinClause)
                  let selectedBinder = grammarV1CheckedJoinSlotBinder checkedSlot
                  _ <- if null (grammarV1CheckedJoinSlotTypeReferences checkedSlot)
                    && null (grammarV1CheckedJoinInvariantReferences joinClause)
                    == noInvariantRefs (grammarV1JoinInvariant (locatedValue joinSource))
                    then Just () else Nothing
                  (leftBlock,_) <- bridgePredecessor
                    [flagBinder,otherBinder,payloadBinder] thenSource
                  (rightBlock,_) <- bridgePredecessor
                    [flagBinder,otherBinder,payloadBinder] elseSource
                  useOccurrence <- grammarV1CheckedLocalValueOccurrenceInScope
                    successorScope sourceUse
                  returnOccurrence <- grammarV1CheckedLocalValueOccurrenceInScope
                    successorScope sourceReturn
                  _ <- if same
                      (grammarV1CheckedLocalValueBinder useOccurrence) selectedBinder
                    && same
                      (grammarV1CheckedLocalValueBinder returnOccurrence)
                      payloadBinder then Just () else Nothing
                  proof <- checkInvariant successorScope selectedBinder
                    (grammarV1JoinInvariant (locatedValue joinSource))
                  let flagName = semanticName flagBinder
                      otherName = semanticName otherBinder
                      payloadName = semanticName payloadBinder
                      selectedName = semanticName selectedBinder
                      span' = locatedSpan (grammarV1FunctionBody functionDecl)
                      component = Located span' (Component
                        { componentName =
                            locatedValue (grammarV1FunctionName functionDecl)
                        , componentParameters = []
                        , componentProvides = Nothing
                        , componentBody = Located span' (Block []) })
                      env = (emptySurfaceEnvironment staticContext)
                        { surfaceInitialBindings = Map.fromList
                            [ (flagName, InitialBinding Unrestricted TyBool
                                (shapeForType TyBool))
                            , (otherName, InitialBinding Unrestricted TyBool
                                (shapeForType TyBool))
                            , (payloadName, InitialBinding Linear payloadType
                                (shapeForType payloadType))
                            ]
                        }
                      postSource =
                        [ Located useSpan (ExpressionStatement
                            (Located (locatedSpan sourceUse)
                              (VariableExpression selectedName)))
                        , Located returnSpan (ReturnStatement
                            (Located (locatedSpan sourceReturn)
                              (VariableExpression payloadName))) ]
                      spanJoin = locatedSpan joinSource
                      run = traceSurfaceSourceBoolJoinComponent
                        env component leftBlock rightBlock spanJoin selectedName
                        proof postSource
                      ordinary = checkSurfaceSourceBoolJoinComponent
                        env component leftBlock rightBlock spanJoin selectedName
                        proof postSource
                  if sourceBoolJoinOutcome run /= ordinary
                    then Nothing
                    else Just (Right GrammarV1BoolJoinTrace
                      { boolJoinFlagBinder = flagBinder
                      , boolJoinOtherBinder = otherBinder
                      , boolJoinPayloadBinder = payloadBinder
                      , boolJoinSlotBinder = selectedBinder
                      , boolJoinSlotCheckedMode =
                          CheckedTypeMode TyBool Unrestricted
                      , boolJoinInvariantProof = proof
                      , boolJoinBranchRun = run
                      , boolJoinCheckedOutcome = ordinary
                      })
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

    -- This predicate checks the *logical form* the slot scope authority
    -- has already traversed. Non-reflexive equalities remain UNPROVED.
    checkInvariant scope selected maybeInvariant = do
      source <- maybeInvariant
      case locatedValue source of
        GrammarV1TrueProposition -> Just SourceBoolInvariantProvenTrue
        GrammarV1FalseProposition -> Just SourceBoolInvariantUnproved
        GrammarV1RelationProposition lhs (Located _ GrammarV1EqualRelation) rhs -> do
          lhsOccurrence <- grammarV1CheckedLocalValueOccurrenceInScope scope lhs
          rhsOccurrence <- grammarV1CheckedLocalValueOccurrenceInScope scope rhs
          if same
              (grammarV1CheckedLocalValueBinder lhsOccurrence) selected
             && same
              (grammarV1CheckedLocalValueBinder rhsOccurrence) selected
            then Just SourceBoolInvariantProvenReflexive
            else Just SourceBoolInvariantUnproved
        _ -> Nothing

    noInvariantRefs maybeInvariant =
      case fmap locatedValue maybeInvariant of
        Just GrammarV1TrueProposition -> True
        Just GrammarV1FalseProposition -> True
        Nothing -> True
        _ -> False

    findExact known target =
      case filter (same target) known of
        [one] -> Just one
        _ -> Nothing

    semanticName = unName . grammarV1ResolvedBinderCoreName
    same a b = grammarV1ResolvedBinderKey a ==
      grammarV1ResolvedBinderKey b
