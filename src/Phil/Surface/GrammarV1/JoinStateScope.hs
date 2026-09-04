module Phil.Surface.GrammarV1.JoinStateScope
  ( GrammarV1CheckedJoinReference (..)
  , GrammarV1CheckedJoinSlot (..)
  , GrammarV1CheckedJoinClause (..)
  , GrammarV1CheckedIfBranch (..)
  , GrammarV1CheckedJoinExpression (..)
  , GrammarV1JoinStateScopeError (..)
  , grammarV1CheckedJoinExpressionInScope
  ) where

import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKind (GrammarV1JoinStateBinder)
  , GrammarV1BinderScopeError (..)
  , GrammarV1LexicalScope
  , GrammarV1ResolvedBinder
  , grammarV1BindLocal
  , grammarV1EnterLexicalScope
  , grammarV1LeaveLexicalScope
  , grammarV1ResolveLocal
  )
import Phil.Surface.GrammarV1.CaseArmScope
  ( GrammarV1CaseArmScopeError
  , GrammarV1CheckedCaseExpression
  , grammarV1CheckedCaseExpressionInScope
  )
import Phil.Surface.GrammarV1.LetPatternScope
  ( GrammarV1CheckedLetScopeStep
  , GrammarV1LetPatternScopeError
  , grammarV1CheckedLetPatternBlockInScope
  )
import Phil.Surface.GrammarV1.ParameterBodyScope
  ( GrammarV1CheckedLocalValueOccurrence
  , grammarV1CheckedLocalValueOccurrenceInScope
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block
  , GrammarV1Expression (..)
  , GrammarV1Fallback (..)
  , GrammarV1FailureTarget (..)
  , GrammarV1JoinClause (..)
  , GrammarV1Proposition (..)
  , GrammarV1QualifiedName (..)
  , GrammarV1StateSlot (..)
  , GrammarV1StaticReference (..)
  , GrammarV1Type (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | One term-level source occurrence in a join slot type or logical invariant
-- that resolves to an already-active lexical binder. Static/global names are not
-- reclassified as locals merely because they are syntactically bare.
data GrammarV1CheckedJoinReference = GrammarV1CheckedJoinReference
  { grammarV1CheckedJoinReferenceSource :: Located Text
  , grammarV1CheckedJoinReferenceBinder :: GrammarV1ResolvedBinder
  }
  deriving (Eq, Show)

-- | One post-join state slot after lexical identity allocation. The slot's type
-- dependencies are checked before the slot itself is introduced, so a later slot
-- may depend on earlier state while self/forward references fail closed.
data GrammarV1CheckedJoinSlot = GrammarV1CheckedJoinSlot
  { grammarV1CheckedJoinSlotSource :: Located GrammarV1StateSlot
  , grammarV1CheckedJoinSlotBinder :: GrammarV1ResolvedBinder
  , grammarV1CheckedJoinSlotTypeReferences :: [GrammarV1CheckedJoinReference]
  }
  deriving (Eq, Show)

-- | Exact lexical result for one author-declared post-join state telescope. The
-- invariant is checked only after all state-slot binders have been established.
data GrammarV1CheckedJoinClause = GrammarV1CheckedJoinClause
  { grammarV1CheckedJoinSlots :: [GrammarV1CheckedJoinSlot]
  , grammarV1CheckedJoinInvariantReferences :: [GrammarV1CheckedJoinReference]
  }
  deriving (Eq, Show)

-- | One if predecessor's lexical body. Its child frame is discarded before the
-- sibling predecessor or post-join telescope is checked.
data GrammarV1CheckedIfBranch = GrammarV1CheckedIfBranch
  { grammarV1CheckedIfBranchSource :: Located GrammarV1Block
  , grammarV1CheckedIfBranchSteps :: [GrammarV1CheckedLetScopeStep]
  }
  deriving (Eq, Show)

-- | Bounded lexical result for the two Grammar-v1 forms that expose join state.
-- Match arms are delegated to the shared case-arm authority from SURF-009 slice
-- 4; if branches use the same child-frame/ordinal discipline directly.
data GrammarV1CheckedJoinExpression
  = GrammarV1CheckedMatchJoinExpression
      GrammarV1CheckedCaseExpression
      GrammarV1CheckedJoinClause
  | GrammarV1CheckedIfJoinExpression
      GrammarV1CheckedLocalValueOccurrence
      GrammarV1CheckedIfBranch
      (Maybe GrammarV1CheckedIfBranch)
      GrammarV1CheckedJoinClause
  deriving (Eq, Show)

data GrammarV1JoinStateScopeError
  = GrammarV1JoinStateBinderError GrammarV1BinderScopeError
  | GrammarV1JoinStateCaseArmError GrammarV1CaseArmScopeError
  | GrammarV1JoinStateBranchBodyError GrammarV1LetPatternScopeError
  | GrammarV1JoinStateForwardReference (Located Text)
  deriving (Eq, Show)

-- | Check the bounded lexical surface of an explicit Grammar-v1 join. Join-state
-- names are post-join binding occurrences: predecessor arms/branches do not see
-- them, while the returned successor scope does. Resource-state projection and
-- proof of the logical invariant remain with the Resource State/Join checker.
grammarV1CheckedJoinExpressionInScope
  :: GrammarV1LexicalScope
  -> Located GrammarV1Expression
  -> Maybe
      (Either
        GrammarV1JoinStateScopeError
        (GrammarV1CheckedJoinExpression, GrammarV1LexicalScope))
grammarV1CheckedJoinExpressionInScope scope (Located sourceSpan expression) =
  case expression of
    GrammarV1MatchExpression scrutinee (Just joinClause) arms -> do
      let withoutJoin = Located sourceSpan
            (GrammarV1MatchExpression scrutinee Nothing arms)
      armResult <- grammarV1CheckedCaseExpressionInScope scope withoutJoin
      case armResult of
        Left armError -> Just (Left (GrammarV1JoinStateCaseArmError armError))
        Right (checkedCase, afterArms) -> do
          joinResult <- checkedJoinClause joinClause afterArms
          Just $ fmap
            (\(checkedJoin, finalScope) ->
              (GrammarV1CheckedMatchJoinExpression checkedCase checkedJoin, finalScope))
            joinResult
    GrammarV1IfExpression condition (Just joinClause) trueBranch falseBranch -> do
      checkedCondition <- grammarV1CheckedLocalValueOccurrenceInScope scope condition
      trueResult <- checkedIfBranch scope trueBranch
      case trueResult of
        Left branchError -> Just (Left branchError)
        Right (checkedTrue, afterTrue) -> do
          falseResult <- case falseBranch of
            Nothing -> Just (Right (Nothing, afterTrue))
            Just branch -> do
              branchResult <- checkedIfBranch afterTrue branch
              Just $ fmap
                (\(checkedFalse, afterFalse) -> (Just checkedFalse, afterFalse))
                branchResult
          case falseResult of
            Left branchError -> Just (Left branchError)
            Right (checkedFalse, afterBranches) -> do
              joinResult <- checkedJoinClause joinClause afterBranches
              Just $ fmap
                (\(checkedJoin, finalScope) ->
                  ( GrammarV1CheckedIfJoinExpression
                      checkedCondition checkedTrue checkedFalse checkedJoin
                  , finalScope
                  ))
                joinResult
    _ -> Nothing

checkedIfBranch
  :: GrammarV1LexicalScope
  -> Located GrammarV1Block
  -> Maybe
      (Either
        GrammarV1JoinStateScopeError
        (GrammarV1CheckedIfBranch, GrammarV1LexicalScope))
checkedIfBranch parentScope source = do
  bodyResult <- grammarV1CheckedLetPatternBlockInScope
    (grammarV1EnterLexicalScope parentScope)
    source
  case bodyResult of
    Left bodyError -> Just (Left (GrammarV1JoinStateBranchBodyError bodyError))
    Right (steps, finalChildScope) ->
      case grammarV1LeaveLexicalScope finalChildScope of
        Left scopeError -> Just (Left (GrammarV1JoinStateBinderError scopeError))
        Right nextParent -> Just (Right
          ( GrammarV1CheckedIfBranch
              { grammarV1CheckedIfBranchSource = source
              , grammarV1CheckedIfBranchSteps = steps
              }
          , nextParent
          ))

checkedJoinClause
  :: Located GrammarV1JoinClause
  -> GrammarV1LexicalScope
  -> Maybe
      (Either
        GrammarV1JoinStateScopeError
        (GrammarV1CheckedJoinClause, GrammarV1LexicalScope))
checkedJoinClause (Located _ joinClause) scope = do
  slotResult <- checkedJoinSlots
    (map (locatedValue . grammarV1StateSlotName . locatedValue)
      (grammarV1JoinState joinClause))
    scope
    (grammarV1JoinState joinClause)
  case slotResult of
    Left scopeError -> Just (Left scopeError)
    Right (checkedSlots, finalScope) -> do
      invariantResult <- case grammarV1JoinInvariant joinClause of
        Nothing -> Just (Right [])
        Just invariant -> checkedPropositionReferences Set.empty finalScope invariant
      Just $ fmap
        (\invariantReferences ->
          ( GrammarV1CheckedJoinClause
              { grammarV1CheckedJoinSlots = checkedSlots
              , grammarV1CheckedJoinInvariantReferences = invariantReferences
              }
          , finalScope
          ))
        invariantResult

checkedJoinSlots
  :: [Text]
  -> GrammarV1LexicalScope
  -> [Located GrammarV1StateSlot]
  -> Maybe
      (Either
        GrammarV1JoinStateScopeError
        ([GrammarV1CheckedJoinSlot], GrammarV1LexicalScope))
checkedJoinSlots _ scope [] = Just (Right ([], scope))
checkedJoinSlots pendingNames scope (source@(Located _ slot) : rest) = do
  typeReferencesResult <- checkedTypeReferences
    (Set.fromList pendingNames)
    scope
    (grammarV1StateSlotType slot)
  case typeReferencesResult of
    Left scopeError -> Just (Left scopeError)
    Right typeReferences ->
      case grammarV1BindLocal
          GrammarV1JoinStateBinder
          (grammarV1StateSlotName slot)
          scope of
        Left scopeError -> Just (Left (GrammarV1JoinStateBinderError scopeError))
        Right (binder, nextScope) -> do
          remainder <- checkedJoinSlots (drop 1 pendingNames) nextScope rest
          Just $ fmap
            (\(checkedRest, finalScope) ->
              ( GrammarV1CheckedJoinSlot
                  { grammarV1CheckedJoinSlotSource = source
                  , grammarV1CheckedJoinSlotBinder = binder
                  , grammarV1CheckedJoinSlotTypeReferences = typeReferences
                  }
                : checkedRest
              , finalScope
              ))
            remainder

checkedTypeReferences
  :: Set.Set Text
  -> GrammarV1LexicalScope
  -> Located GrammarV1Type
  -> Maybe (Either GrammarV1JoinStateScopeError [GrammarV1CheckedJoinReference])
checkedTypeReferences pending scope (Located _ ty) = case ty of
  GrammarV1UnitType -> Just (Right [])
  GrammarV1BoolType -> Just (Right [])
  GrammarV1UnsignedType _ -> Just (Right [])
  GrammarV1BytesType expression -> checkedExpressionReferences pending scope expression
  GrammarV1FrameType _ -> Just (Right [])
  GrammarV1ProofType proposition -> checkedPropositionReferences pending scope proposition
  GrammarV1ValidatedType _ context subject ->
    combineChecked
      (checkedExpressionReferences pending scope context)
      (checkedExpressionReferences pending scope subject)
  GrammarV1RefinementType _ _ _ -> Nothing
  GrammarV1TupleType elements -> checkedMany
    (map (checkedTypeReferences pending scope) elements)
  GrammarV1NamedType _ -> Just (Right [])

checkedPropositionReferences
  :: Set.Set Text
  -> GrammarV1LexicalScope
  -> Located GrammarV1Proposition
  -> Maybe (Either GrammarV1JoinStateScopeError [GrammarV1CheckedJoinReference])
checkedPropositionReferences pending scope (Located _ proposition) = case proposition of
  GrammarV1TrueProposition -> Just (Right [])
  GrammarV1FalseProposition -> Just (Right [])
  GrammarV1RelationProposition left _ right -> combineChecked
    (checkedExpressionReferences pending scope left)
    (checkedExpressionReferences pending scope right)
  GrammarV1ClaimApplicationProposition _ arguments -> checkedMany
    (map (checkedExpressionReferences pending scope) arguments)
  GrammarV1NotProposition inner -> checkedPropositionReferences pending scope inner
  GrammarV1AndProposition left right -> combineChecked
    (checkedPropositionReferences pending scope left)
    (checkedPropositionReferences pending scope right)
  GrammarV1OrProposition left right -> combineChecked
    (checkedPropositionReferences pending scope left)
    (checkedPropositionReferences pending scope right)

checkedExpressionReferences
  :: Set.Set Text
  -> GrammarV1LexicalScope
  -> Located GrammarV1Expression
  -> Maybe (Either GrammarV1JoinStateScopeError [GrammarV1CheckedJoinReference])
checkedExpressionReferences pending scope (Located sourceSpan expression) =
  case expression of
    GrammarV1NameExpression reference arguments
      | null arguments
      , null (grammarV1StaticReferenceArguments reference)
      , [displayName] <- grammarV1QualifiedNameParts
          (grammarV1StaticReferenceName reference) ->
          let sourceName = Located sourceSpan displayName
          in case grammarV1ResolveLocal sourceName scope of
              Right binder -> Just (Right
                [GrammarV1CheckedJoinReference sourceName binder])
              Left (GrammarV1BinderNotInScope _)
                | Set.member displayName pending ->
                    Just (Left (GrammarV1JoinStateForwardReference sourceName))
                | otherwise -> Just (Right [])
              Left scopeError -> Just (Left (GrammarV1JoinStateBinderError scopeError))
    GrammarV1NameExpression _ arguments -> checkedMany
      (map (checkedExpressionReferences pending scope) arguments)
    GrammarV1BoolExpression _ -> Just (Right [])
    GrammarV1UnitExpression -> Just (Right [])
    GrammarV1IntegerExpression _ -> Just (Right [])
    GrammarV1ProjectionExpression receiver _ ->
      checkedExpressionReferences pending scope receiver
    GrammarV1BinaryExpression left _ right -> combineChecked
      (checkedExpressionReferences pending scope left)
      (checkedExpressionReferences pending scope right)
    GrammarV1FallbackExpression primary fallback -> combineChecked
      (checkedExpressionReferences pending scope primary)
      (checkedFallbackReferences pending scope fallback)
    GrammarV1TupleExpression elements -> checkedMany
      (map (checkedExpressionReferences pending scope) elements)
    GrammarV1ParenthesizedExpression inner ->
      checkedExpressionReferences pending scope inner
    _ -> Nothing

checkedFallbackReferences
  :: Set.Set Text
  -> GrammarV1LexicalScope
  -> Located GrammarV1Fallback
  -> Maybe (Either GrammarV1JoinStateScopeError [GrammarV1CheckedJoinReference])
checkedFallbackReferences pending scope (Located _ fallback) = case fallback of
  GrammarV1FailFallback (Located _ target) -> checkedMany
    (map (checkedExpressionReferences pending scope)
      (grammarV1FailureTargetArguments target))
  GrammarV1RejectFallback expression ->
    checkedExpressionReferences pending scope expression

combineChecked
  :: Maybe (Either e [a])
  -> Maybe (Either e [a])
  -> Maybe (Either e [a])
combineChecked left right = do
  leftResult <- left
  rightResult <- right
  Just $ do
    leftValues <- leftResult
    rightValues <- rightResult
    Right (leftValues <> rightValues)

checkedMany :: [Maybe (Either e [a])] -> Maybe (Either e [a])
checkedMany = foldr combineChecked (Just (Right []))
