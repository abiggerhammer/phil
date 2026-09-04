module Phil.Surface.GrammarV1.LoopStateScope
  ( GrammarV1CheckedLoopSlot (..)
  , GrammarV1CheckedLoopBodyStep (..)
  , GrammarV1CheckedLoopState (..)
  , GrammarV1LoopStateScopeError (..)
  , grammarV1CheckedLoopExpressionInScope
  ) where

import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKind
      ( GrammarV1LetPatternBinder
      , GrammarV1LoopStateBinder
      )
  , GrammarV1BinderScopeError
  , GrammarV1LexicalScope
  , GrammarV1ResolvedBinder
  , grammarV1BindLocal
  , grammarV1EnterLexicalScope
  , grammarV1LeaveLexicalScope
  )
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference
  , GrammarV1LexicalReferenceError
  , grammarV1CheckedExpressionReferences
  , grammarV1CheckedPropositionReferences
  , grammarV1CheckedTypeReferences
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..)
  , GrammarV1Expression (..)
  , GrammarV1StateBinding (..)
  , GrammarV1Statement (..)
  )
import Phil.Surface.GrammarV1.PatternBinderScope (grammarV1BindPattern)
import Phil.Surface.Syntax (Located (..))

-- | One loop-header state binding after the entry-edge initializer has been
-- reference-checked and the header occurrence has received semantic identity.
-- Initializer references are resolved in the parent/pre-loop scope. Type
-- references are resolved in the left-to-right header telescope, so a later slot
-- may depend on an earlier header slot but not on itself or a future slot.
data GrammarV1CheckedLoopSlot = GrammarV1CheckedLoopSlot
  { grammarV1CheckedLoopSlotSource :: Located GrammarV1StateBinding
  , grammarV1CheckedLoopSlotBinder :: GrammarV1ResolvedBinder
  , grammarV1CheckedLoopSlotInitializerReferences ::
      [GrammarV1CheckedLexicalReference]
  , grammarV1CheckedLoopSlotTypeReferences :: [GrammarV1CheckedLexicalReference]
  }
  deriving (Eq, Show)

-- | Bounded lexical trace for the loop body. Continue/break retain their exact
-- explicit actual syntax and the lexical references occurring in those actuals;
-- an empty actual list therefore stays empty rather than capturing loop state.
data GrammarV1CheckedLoopBodyStep
  = GrammarV1CheckedLoopBodyLetStep
      (Located GrammarV1Statement)
      [GrammarV1CheckedLexicalReference]
      [GrammarV1ResolvedBinder]
  | GrammarV1CheckedLoopBodyOccurrenceStep
      (Located GrammarV1Statement)
      [GrammarV1CheckedLexicalReference]
  | GrammarV1CheckedLoopContinueStep
      (Located GrammarV1Statement)
      [Located GrammarV1Expression]
      [GrammarV1CheckedLexicalReference]
  | GrammarV1CheckedLoopBreakStep
      (Located GrammarV1Statement)
      [Located GrammarV1Expression]
      [GrammarV1CheckedLexicalReference]
  deriving (Eq, Show)

-- | Exact lexical result for one bounded Grammar-v1 loop. The returned outer
-- scope has already left both the body and loop-header regions, so loop-state and
-- body-local binders no longer resolve while the declaration-wide fresh ordinal
-- remains advanced.
data GrammarV1CheckedLoopState = GrammarV1CheckedLoopState
  { grammarV1CheckedLoopSlots :: [GrammarV1CheckedLoopSlot]
  , grammarV1CheckedLoopInvariantReferences :: [GrammarV1CheckedLexicalReference]
  , grammarV1CheckedLoopBodySteps :: [GrammarV1CheckedLoopBodyStep]
  }
  deriving (Eq, Show)

data GrammarV1LoopStateScopeError
  = GrammarV1LoopStateBinderError GrammarV1BinderScopeError
  | GrammarV1LoopStateReferenceError GrammarV1LexicalReferenceError
  deriving (Eq, Show)

-- | Check lexical identity/visibility for one Grammar-v1 loop. Every state
-- initializer is an initial-entry actual and is therefore checked in the parent
-- scope before any loop-header binder exists. The state telescope is then bound
-- left-to-right in a child scope; the invariant sees the complete telescope; the
-- body receives a nested child scope. Resource-state projection, continue/break
-- arity, and backedge admissibility remain owned by the LoopContract checker.
grammarV1CheckedLoopExpressionInScope
  :: GrammarV1LexicalScope
  -> Located GrammarV1Expression
  -> Maybe
      (Either
        GrammarV1LoopStateScopeError
        (GrammarV1CheckedLoopState, GrammarV1LexicalScope))
grammarV1CheckedLoopExpressionInScope parentScope (Located _ expression) =
  case expression of
    GrammarV1LoopExpression stateBindings invariant body -> do
      let stateNames = map
            (locatedValue . grammarV1StateBindingName . locatedValue)
            stateBindings
          pendingAll = Set.fromList stateNames
      initializerResult <- checkedInitializers pendingAll parentScope stateBindings
      case initializerResult of
        Left scopeError -> Just (Left scopeError)
        Right initializerReferences -> do
          slotResult <- checkedLoopSlots
            stateNames
            (grammarV1EnterLexicalScope parentScope)
            stateBindings
            initializerReferences
          case slotResult of
            Left scopeError -> Just (Left scopeError)
            Right (checkedSlots, headerScope) -> do
              invariantResult <- case invariant of
                Nothing -> Just (Right [])
                Just proposition -> loopReferences
                  (grammarV1CheckedPropositionReferences
                    Set.empty headerScope proposition)
              case invariantResult of
                Left scopeError -> Just (Left scopeError)
                Right invariantReferences -> do
                  bodyResult <- checkedLoopBody
                    (grammarV1EnterLexicalScope headerScope)
                    body
                  case bodyResult of
                    Left scopeError -> Just (Left scopeError)
                    Right (bodySteps, finalBodyScope) ->
                      case grammarV1LeaveLexicalScope finalBodyScope of
                        Left scopeError -> Just
                          (Left (GrammarV1LoopStateBinderError scopeError))
                        Right afterBody ->
                          case grammarV1LeaveLexicalScope afterBody of
                            Left scopeError -> Just
                              (Left (GrammarV1LoopStateBinderError scopeError))
                            Right finalOuter -> Just (Right
                              ( GrammarV1CheckedLoopState
                                  { grammarV1CheckedLoopSlots = checkedSlots
                                  , grammarV1CheckedLoopInvariantReferences =
                                      invariantReferences
                                  , grammarV1CheckedLoopBodySteps = bodySteps
                                  }
                              , finalOuter
                              ))
    _ -> Nothing

checkedInitializers
  :: Set.Set Text
  -> GrammarV1LexicalScope
  -> [Located GrammarV1StateBinding]
  -> Maybe
      (Either
        GrammarV1LoopStateScopeError
        [[GrammarV1CheckedLexicalReference]])
checkedInitializers pending parentScope = checkedMany . map checkedInitializer
  where
    checkedInitializer (Located _ binding) = loopReferences
      (grammarV1CheckedExpressionReferences
        pending parentScope (grammarV1StateBindingInitializer binding))

checkedLoopSlots
  :: [Text]
  -> GrammarV1LexicalScope
  -> [Located GrammarV1StateBinding]
  -> [[GrammarV1CheckedLexicalReference]]
  -> Maybe
      (Either
        GrammarV1LoopStateScopeError
        ([GrammarV1CheckedLoopSlot], GrammarV1LexicalScope))
checkedLoopSlots _ scope [] [] = Just (Right ([], scope))
checkedLoopSlots pendingNames scope
    (source@(Located _ binding) : rest)
    (initializerReferences : restInitializers) = do
  typeReferencesResult <- case grammarV1StateBindingType binding of
    Nothing -> Just (Right [])
    Just sourceType -> loopReferences
      (grammarV1CheckedTypeReferences
        (Set.fromList pendingNames) scope sourceType)
  case typeReferencesResult of
    Left scopeError -> Just (Left scopeError)
    Right typeReferences ->
      case grammarV1BindLocal
          GrammarV1LoopStateBinder
          (grammarV1StateBindingName binding)
          scope of
        Left scopeError -> Just (Left (GrammarV1LoopStateBinderError scopeError))
        Right (binder, nextScope) -> do
          remainder <- checkedLoopSlots
            (drop 1 pendingNames)
            nextScope
            rest
            restInitializers
          Just $ fmap
            (\(checkedRest, finalScope) ->
              ( GrammarV1CheckedLoopSlot
                  { grammarV1CheckedLoopSlotSource = source
                  , grammarV1CheckedLoopSlotBinder = binder
                  , grammarV1CheckedLoopSlotInitializerReferences =
                      initializerReferences
                  , grammarV1CheckedLoopSlotTypeReferences = typeReferences
                  }
                : checkedRest
              , finalScope
              ))
            remainder
checkedLoopSlots _ _ _ _ = Nothing

checkedLoopBody
  :: GrammarV1LexicalScope
  -> Located GrammarV1Block
  -> Maybe
      (Either
        GrammarV1LoopStateScopeError
        ([GrammarV1CheckedLoopBodyStep], GrammarV1LexicalScope))
checkedLoopBody scope (Located _ (GrammarV1Block statements)) =
  checkedLoopStatements scope statements

checkedLoopStatements
  :: GrammarV1LexicalScope
  -> [Located GrammarV1Statement]
  -> Maybe
      (Either
        GrammarV1LoopStateScopeError
        ([GrammarV1CheckedLoopBodyStep], GrammarV1LexicalScope))
checkedLoopStatements scope [] = Just (Right ([], scope))
checkedLoopStatements scope (source@(Located _ statement) : rest) =
  case statement of
    GrammarV1LetStatement patternValue initializer -> do
      initializerResult <- loopReferences
        (grammarV1CheckedExpressionReferences Set.empty scope initializer)
      case initializerResult of
        Left scopeError -> Just (Left scopeError)
        Right initializerReferences ->
          case grammarV1BindPattern
              GrammarV1LetPatternBinder patternValue scope of
            Left scopeError -> Just
              (Left (GrammarV1LoopStateBinderError scopeError))
            Right (binders, nextScope) -> do
              remainder <- checkedLoopStatements nextScope rest
              Just $ fmap
                (\(steps, finalScope) ->
                  ( GrammarV1CheckedLoopBodyLetStep
                      source initializerReferences binders
                    : steps
                  , finalScope
                  ))
                remainder
    GrammarV1ReturnStatement returned -> do
      referencesResult <- loopReferences
        (grammarV1CheckedExpressionReferences Set.empty scope returned)
      case referencesResult of
        Left scopeError -> Just (Left scopeError)
        Right references
          | null rest -> Just (Right
              ([GrammarV1CheckedLoopBodyOccurrenceStep source references], scope))
          | otherwise -> Nothing
    GrammarV1ExpressionStatement expressionSource@(Located _ bodyExpression) ->
      case bodyExpression of
        GrammarV1ContinueExpression actuals
          | null rest -> checkedTerminalControl
              GrammarV1CheckedLoopContinueStep source scope actuals
          | otherwise -> Nothing
        GrammarV1BreakExpression actuals
          | null rest -> checkedTerminalControl
              GrammarV1CheckedLoopBreakStep source scope actuals
          | otherwise -> Nothing
        _ -> do
          referencesResult <- loopReferences
            (grammarV1CheckedExpressionReferences
              Set.empty scope expressionSource)
          case referencesResult of
            Left scopeError -> Just (Left scopeError)
            Right references -> do
              remainder <- checkedLoopStatements scope rest
              Just $ fmap
                (\(steps, finalScope) ->
                  ( GrammarV1CheckedLoopBodyOccurrenceStep source references : steps
                  , finalScope
                  ))
                remainder

checkedTerminalControl
  :: (Located GrammarV1Statement
      -> [Located GrammarV1Expression]
      -> [GrammarV1CheckedLexicalReference]
      -> GrammarV1CheckedLoopBodyStep)
  -> Located GrammarV1Statement
  -> GrammarV1LexicalScope
  -> [Located GrammarV1Expression]
  -> Maybe
      (Either
        GrammarV1LoopStateScopeError
        ([GrammarV1CheckedLoopBodyStep], GrammarV1LexicalScope))
checkedTerminalControl constructor source scope actuals = do
  referencesResult <- checkedExpressions scope actuals
  Just $ fmap
    (\references -> ([constructor source actuals references], scope))
    referencesResult

checkedExpressions
  :: GrammarV1LexicalScope
  -> [Located GrammarV1Expression]
  -> Maybe
      (Either
        GrammarV1LoopStateScopeError
        [GrammarV1CheckedLexicalReference])
checkedExpressions scope = checkedMany . map
  (loopReferences . grammarV1CheckedExpressionReferences Set.empty scope)

loopReferences
  :: Maybe
      (Either
        GrammarV1LexicalReferenceError
        [GrammarV1CheckedLexicalReference])
  -> Maybe
      (Either
        GrammarV1LoopStateScopeError
        [GrammarV1CheckedLexicalReference])
loopReferences = fmap $ either
  (Left . GrammarV1LoopStateReferenceError)
  Right

checkedMany
  :: [Maybe (Either e [a])]
  -> Maybe (Either e [[a]])
checkedMany [] = Just (Right [])
checkedMany (current : rest) = do
  currentResult <- current
  restResult <- checkedMany rest
  Just $ do
    currentValues <- currentResult
    restValues <- restResult
    Right (currentValues : restValues)
