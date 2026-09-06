module Phil.Surface.GrammarV1.SequentialExecution
  ( GrammarV1ExecutionEvent (..)
  , GrammarV1ExecutionChoice (..)
  , GrammarV1ExecutionControl (..)
  , GrammarV1SequentialExecutionError (..)
  , grammarV1SequentialExecutionTrace
  ) where

import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..)
  , GrammarV1BranchValue (..)
  , GrammarV1Expression (..)
  , GrammarV1FailureTarget (..)
  , GrammarV1Fallback (..)
  , GrammarV1MatchArm (..)
  , GrammarV1MatchArmBody (..)
  , GrammarV1StateBinding (..)
  , GrammarV1Statement (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Source-semantic execution events for the bounded Grammar-v1 local evaluator.
-- Start/completion are separate deliberately: if a strict child terminates, the
-- parent expression has started but has not completed.  This lets downstream
-- effect/resource observers distinguish operand evaluation from invocation or
-- value formation without treating Haskell traversal order as the authority.
data GrammarV1ExecutionEvent
  = GrammarV1StatementStarted (Located GrammarV1Statement)
  | GrammarV1StatementCompleted (Located GrammarV1Statement)
  | GrammarV1ExpressionStarted (Located GrammarV1Expression)
  | GrammarV1ExpressionCompleted (Located GrammarV1Expression)
  | GrammarV1BranchSelected (Located GrammarV1Expression) Int
  | GrammarV1FallbackSelected (Located GrammarV1Expression) Bool
  deriving (Eq, Ord, Show)

-- | Exact occurrence-bound runtime branch evidence.  Source spelling and source
-- position are not converted into semantic branch identity: the complete Located
-- expression occurrence must match the expression being executed.  Arm indices
-- are zero based and refer to source arm order.
data GrammarV1ExecutionChoice
  = GrammarV1IfChoice (Located GrammarV1Expression) Bool
  | GrammarV1ArmChoice (Located GrammarV1Expression) Int
  | GrammarV1FallbackChoice (Located GrammarV1Expression) Bool
  deriving (Eq, Ord, Show)

-- | Control leaving the currently executed block/path.
data GrammarV1ExecutionControl
  = GrammarV1ExecutionContinues
  | GrammarV1ExecutionReturns
  | GrammarV1ExecutionBreaks
  | GrammarV1ExecutionContinuesLoop
  | GrammarV1ExecutionTerminates
  deriving (Eq, Ord, Show)

data GrammarV1SequentialExecutionError
  = GrammarV1MissingExecutionChoice (Located GrammarV1Expression)
  | GrammarV1DuplicateExecutionChoice (Located GrammarV1Expression)
  | GrammarV1ExecutionChoiceKindMismatch (Located GrammarV1Expression)
  | GrammarV1ExecutionArmIndexOutOfRange
      (Located GrammarV1Expression)
      Int
      Int
  | GrammarV1UnexpectedExecutionChoice GrammarV1ExecutionChoice
  | GrammarV1DuplicateTerminalEvidence (Located GrammarV1Expression)
  | GrammarV1UnexpectedTerminalEvidence (Located GrammarV1Expression)
  | GrammarV1LoopExecutionRequiresLoopAuthority (Located GrammarV1Expression)
  deriving (Eq, Show)

data ExecutionState = ExecutionState
  { executionChoices :: [GrammarV1ExecutionChoice]
  , executionTerminalEvidence :: [Located GrammarV1Expression]
  , executionEventsRev :: [GrammarV1ExecutionEvent]
  }

-- | Produce the exact local source trace for one block under competent runtime
-- branch/outcome evidence.
--
-- The driver owns only deterministic sequencing.  It does not decide conditions,
-- match labels, or whether an ordinary operation has a terminal runtime outcome;
-- those facts are supplied as exact occurrence-bound evidence by the competent
-- evaluator.  It does enforce:
--
-- * statements in source textual order;
-- * strict runtime children left-to-right;
-- * condition/scrutinee before branch selection;
-- * exactly one selected arm, with untaken arms absent from the trace;
-- * no later statement after return or terminal control; and
-- * no silently ignored branch/outcome evidence.
--
-- General loop iteration is deliberately fail-closed in this first EXEC slice:
-- loop backedge/state succession already has a separate authority and will be
-- composed with this local trace relation rather than approximated by a finite
-- Haskell walk.
grammarV1SequentialExecutionTrace
  :: [GrammarV1ExecutionChoice]
  -> [Located GrammarV1Expression]
  -> Located GrammarV1Block
  -> Either
      GrammarV1SequentialExecutionError
      ([GrammarV1ExecutionEvent], GrammarV1ExecutionControl)
grammarV1SequentialExecutionTrace choices terminalEvidence block = do
  ensureUniqueTerminalEvidence terminalEvidence
  let initial = ExecutionState choices terminalEvidence []
  (control, final) <- executeBlock block initial
  case executionChoices final of
    extra : _ -> Left (GrammarV1UnexpectedExecutionChoice extra)
    [] -> case executionTerminalEvidence final of
      extra : _ -> Left (GrammarV1UnexpectedTerminalEvidence extra)
      [] -> Right (reverse (executionEventsRev final), control)

executeBlock
  :: Located GrammarV1Block
  -> ExecutionState
  -> Either
      GrammarV1SequentialExecutionError
      (GrammarV1ExecutionControl, ExecutionState)
executeBlock (Located _ (GrammarV1Block statements)) = executeStatements statements

executeStatements
  :: [Located GrammarV1Statement]
  -> ExecutionState
  -> Either
      GrammarV1SequentialExecutionError
      (GrammarV1ExecutionControl, ExecutionState)
executeStatements [] state = Right (GrammarV1ExecutionContinues, state)
executeStatements (statement : rest) state = do
  let started = emit (GrammarV1StatementStarted statement) state
  (control, afterStatement) <- executeStatement statement started
  case control of
    GrammarV1ExecutionContinues ->
      executeStatements rest (emit (GrammarV1StatementCompleted statement) afterStatement)
    _ -> Right (control, afterStatement)

executeStatement
  :: Located GrammarV1Statement
  -> ExecutionState
  -> Either
      GrammarV1SequentialExecutionError
      (GrammarV1ExecutionControl, ExecutionState)
executeStatement (Located _ statement) state = case statement of
  GrammarV1LetStatement _ initializer -> executeExpression initializer state
  GrammarV1ExpressionStatement expression -> executeExpression expression state
  GrammarV1ReturnStatement expression -> do
    (control, next) <- executeExpression expression state
    case control of
      GrammarV1ExecutionContinues ->
        Right (GrammarV1ExecutionReturns, next)
      _ -> Right (control, next)

executeExpression
  :: Located GrammarV1Expression
  -> ExecutionState
  -> Either
      GrammarV1SequentialExecutionError
      (GrammarV1ExecutionControl, ExecutionState)
executeExpression source@(Located _ expression) state0 = do
  let state = emit (GrammarV1ExpressionStarted source) state0
  case expression of
    GrammarV1NameExpression _ arguments ->
      finishAfterChildren source arguments state
    GrammarV1BoolExpression _ -> finishExpression source state
    GrammarV1UnitExpression -> finishExpression source state
    GrammarV1IntegerExpression _ -> finishExpression source state
    GrammarV1ProjectionExpression base _ ->
      finishAfterChildren source [base] state
    GrammarV1BinaryExpression left _ right ->
      finishAfterChildren source [left, right] state
    GrammarV1FallbackExpression base fallback ->
      executeFallback source base fallback state
    GrammarV1ConstructExpression _ fields ->
      finishAfterChildren source (map snd fields) state
    GrammarV1BorrowExpression borrowed _ body -> do
      (borrowControl, afterBorrow) <- executeExpression borrowed state
      case borrowControl of
        GrammarV1ExecutionContinues -> do
          (bodyControl, afterBody) <- executeBlock body afterBorrow
          case bodyControl of
            GrammarV1ExecutionContinues -> finishExpression source afterBody
            _ -> Right (bodyControl, afterBody)
        _ -> Right (borrowControl, afterBorrow)
    GrammarV1MatchExpression scrutinee _ arms ->
      executeArmChoice source scrutinee arms state
    GrammarV1DecideExpression scrutinee arms ->
      executeArmChoice source scrutinee arms state
    GrammarV1BreakExpression values -> do
      (control, next) <- executeExpressions values state
      case control of
        GrammarV1ExecutionContinues -> do
          (_, completed) <- finishExpression source next
          Right (GrammarV1ExecutionBreaks, completed)
        _ -> Right (control, next)
    GrammarV1ReceiveFrameExpression input ->
      finishAfterChildren source [input] state
    GrammarV1ReceiveExactExpression first second third ->
      finishAfterChildren source ([first, second] <> maybe [] pure third) state
    GrammarV1ReceiveExpression _ input ->
      finishAfterChildren source [input] state
    GrammarV1RecognizeExpression _ input ->
      finishAfterChildren source [input] state
    GrammarV1ValidateExpression _ context input ->
      finishAfterChildren source (maybe [] pure context <> [input]) state
    GrammarV1SendExactExpression first second ->
      finishAfterChildren source [first, second] state
    GrammarV1SendExpression first second ->
      finishAfterChildren source [first, second] state
    GrammarV1SelectExpression branch endpoint boundary ->
      finishAfterChildren source
        ( grammarV1BranchValueArguments (locatedValue branch)
          <> [endpoint]
          <> maybe [] pure boundary
        )
        state
    GrammarV1CommitReceiveExpression first second ->
      finishAfterChildren source [first, second] state
    GrammarV1FailExpression target reason -> do
      (control, afterChildren) <- executeExpressions
        (grammarV1FailureTargetArguments (locatedValue target) <> [reason])
        state
      case control of
        GrammarV1ExecutionContinues -> do
          (_, completed) <- finishExpression source afterChildren
          Right (GrammarV1ExecutionTerminates, completed)
        _ -> Right (control, afterChildren)
    GrammarV1CloseExpression endpoint ->
      finishAfterChildren source [endpoint] state
    GrammarV1ReleaseExpression value ->
      finishAfterChildren source [value] state
    GrammarV1ConvertExpression value _ ->
      finishAfterChildren source [value] state
    GrammarV1AcceptExpression value _ ->
      finishAfterChildren source [value] state
    GrammarV1ProveExpression _ -> finishExpression source state
    GrammarV1TransportExpression value _ evidence ->
      finishAfterChildren source [value, evidence] state
    GrammarV1TupleExpression values ->
      finishAfterChildren source values state
    GrammarV1ParenthesizedExpression value ->
      finishAfterChildren source [value] state
    GrammarV1OfferExpression scrutinee arms ->
      executeArmChoice source scrutinee arms state
    GrammarV1IfExpression condition _ trueBlock falseBlock ->
      executeIfChoice source condition trueBlock falseBlock state
    GrammarV1LoopExpression bindings _ _ -> do
      (control, afterInitializers) <- executeExpressions
        (map (grammarV1StateBindingInitializer . locatedValue) bindings)
        state
      case control of
        GrammarV1ExecutionContinues ->
          Left (GrammarV1LoopExecutionRequiresLoopAuthority source)
        _ -> Right (control, afterInitializers)
    GrammarV1ContinueExpression values -> do
      (control, next) <- executeExpressions values state
      case control of
        GrammarV1ExecutionContinues -> do
          (_, completed) <- finishExpression source next
          Right (GrammarV1ExecutionContinuesLoop, completed)
        _ -> Right (control, next)
    GrammarV1ClosureExpression _closure ->
      -- Constructing a closure does not execute its body.
      finishExpression source state
    GrammarV1RejectExpression value -> do
      (control, afterValue) <- executeExpression value state
      case control of
        GrammarV1ExecutionContinues -> do
          (_, completed) <- finishExpression source afterValue
          Right (GrammarV1ExecutionTerminates, completed)
        _ -> Right (control, afterValue)

finishAfterChildren
  :: Located GrammarV1Expression
  -> [Located GrammarV1Expression]
  -> ExecutionState
  -> Either
      GrammarV1SequentialExecutionError
      (GrammarV1ExecutionControl, ExecutionState)
finishAfterChildren source children state = do
  (control, next) <- executeExpressions children state
  case control of
    GrammarV1ExecutionContinues -> finishExpression source next
    _ -> Right (control, next)

executeExpressions
  :: [Located GrammarV1Expression]
  -> ExecutionState
  -> Either
      GrammarV1SequentialExecutionError
      (GrammarV1ExecutionControl, ExecutionState)
executeExpressions [] state = Right (GrammarV1ExecutionContinues, state)
executeExpressions (expression : rest) state = do
  (control, next) <- executeExpression expression state
  case control of
    GrammarV1ExecutionContinues -> executeExpressions rest next
    _ -> Right (control, next)

finishExpression
  :: Located GrammarV1Expression
  -> ExecutionState
  -> Either
      GrammarV1SequentialExecutionError
      (GrammarV1ExecutionControl, ExecutionState)
finishExpression source state = do
  (isTerminal, next) <- consumeTerminalEvidence source state
  let completed = emit (GrammarV1ExpressionCompleted source) next
  Right
    ( if isTerminal
        then GrammarV1ExecutionTerminates
        else GrammarV1ExecutionContinues
    , completed
    )

executeIfChoice
  :: Located GrammarV1Expression
  -> Located GrammarV1Expression
  -> Located GrammarV1Block
  -> Maybe (Located GrammarV1Block)
  -> ExecutionState
  -> Either
      GrammarV1SequentialExecutionError
      (GrammarV1ExecutionControl, ExecutionState)
executeIfChoice source condition trueBlock falseBlock state = do
  (conditionControl, afterCondition) <- executeExpression condition state
  case conditionControl of
    GrammarV1ExecutionContinues -> do
      (takeTrue, selectedState) <- consumeIfChoice source afterCondition
      let withSelection = emit
            (GrammarV1BranchSelected source (if takeTrue then 0 else 1))
            selectedState
      if takeTrue
        then finishSelectedBlock source trueBlock withSelection
        else case falseBlock of
          Nothing -> finishExpression source withSelection
          Just block -> finishSelectedBlock source block withSelection
    _ -> Right (conditionControl, afterCondition)

executeArmChoice
  :: Located GrammarV1Expression
  -> Located GrammarV1Expression
  -> [Located GrammarV1MatchArm]
  -> ExecutionState
  -> Either
      GrammarV1SequentialExecutionError
      (GrammarV1ExecutionControl, ExecutionState)
executeArmChoice source scrutinee arms state = do
  (scrutineeControl, afterScrutinee) <- executeExpression scrutinee state
  case scrutineeControl of
    GrammarV1ExecutionContinues -> do
      (index, selectedState) <- consumeArmChoice source afterScrutinee
      arm <- maybe
        (Left (GrammarV1ExecutionArmIndexOutOfRange source index (length arms)))
        Right
        (atMay index arms)
      let withSelection = emit (GrammarV1BranchSelected source index) selectedState
      (armControl, afterArm) <- executeMatchArm arm withSelection
      case armControl of
        GrammarV1ExecutionContinues -> finishExpression source afterArm
        _ -> Right (armControl, afterArm)
    _ -> Right (scrutineeControl, afterScrutinee)

executeMatchArm
  :: Located GrammarV1MatchArm
  -> ExecutionState
  -> Either
      GrammarV1SequentialExecutionError
      (GrammarV1ExecutionControl, ExecutionState)
executeMatchArm (Located _ arm) state =
  case grammarV1MatchArmBody arm of
    GrammarV1MatchArmBlock block -> executeBlock block state
    GrammarV1MatchArmStatement statement -> do
      let started = emit (GrammarV1StatementStarted statement) state
      (control, next) <- executeStatement statement started
      case control of
        GrammarV1ExecutionContinues -> Right
          ( GrammarV1ExecutionContinues
          , emit (GrammarV1StatementCompleted statement) next
          )
        _ -> Right (control, next)

executeFallback
  :: Located GrammarV1Expression
  -> Located GrammarV1Expression
  -> Located GrammarV1Fallback
  -> ExecutionState
  -> Either
      GrammarV1SequentialExecutionError
      (GrammarV1ExecutionControl, ExecutionState)
executeFallback source base fallback state = do
  (baseControl, afterBase) <- executeExpression base state
  (takeFallback, selectedState) <- consumeFallbackChoice source afterBase
  let withSelection = emit (GrammarV1FallbackSelected source takeFallback) selectedState
  if not takeFallback
    then case baseControl of
      GrammarV1ExecutionContinues -> finishExpression source withSelection
      _ -> Right (baseControl, withSelection)
    else do
      (fallbackControl, afterFallback) <- executeFallbackPayload fallback withSelection
      case fallbackControl of
        GrammarV1ExecutionContinues -> finishExpression source afterFallback
        _ -> Right (fallbackControl, afterFallback)

executeFallbackPayload
  :: Located GrammarV1Fallback
  -> ExecutionState
  -> Either
      GrammarV1SequentialExecutionError
      (GrammarV1ExecutionControl, ExecutionState)
executeFallbackPayload (Located _ fallback) state = case fallback of
  GrammarV1FailFallback target -> do
    (control, next) <- executeExpressions
      (grammarV1FailureTargetArguments (locatedValue target))
      state
    case control of
      GrammarV1ExecutionContinues ->
        Right (GrammarV1ExecutionTerminates, next)
      _ -> Right (control, next)
  GrammarV1RejectFallback expression -> executeExpression expression state

finishSelectedBlock
  :: Located GrammarV1Expression
  -> Located GrammarV1Block
  -> ExecutionState
  -> Either
      GrammarV1SequentialExecutionError
      (GrammarV1ExecutionControl, ExecutionState)
finishSelectedBlock source block state = do
  (control, next) <- executeBlock block state
  case control of
    GrammarV1ExecutionContinues -> finishExpression source next
    _ -> Right (control, next)

consumeIfChoice
  :: Located GrammarV1Expression
  -> ExecutionState
  -> Either GrammarV1SequentialExecutionError (Bool, ExecutionState)
consumeIfChoice source state =
  case matchingChoices source (executionChoices state) of
    [] -> Left (GrammarV1MissingExecutionChoice source)
    [choice@(GrammarV1IfChoice _ selected)] ->
      Right (selected, state { executionChoices = removeFirst choice (executionChoices state) })
    [_] -> Left (GrammarV1ExecutionChoiceKindMismatch source)
    _ -> Left (GrammarV1DuplicateExecutionChoice source)

consumeArmChoice
  :: Located GrammarV1Expression
  -> ExecutionState
  -> Either GrammarV1SequentialExecutionError (Int, ExecutionState)
consumeArmChoice source state =
  case matchingChoices source (executionChoices state) of
    [] -> Left (GrammarV1MissingExecutionChoice source)
    [choice@(GrammarV1ArmChoice _ selected)] ->
      Right (selected, state { executionChoices = removeFirst choice (executionChoices state) })
    [_] -> Left (GrammarV1ExecutionChoiceKindMismatch source)
    _ -> Left (GrammarV1DuplicateExecutionChoice source)

consumeFallbackChoice
  :: Located GrammarV1Expression
  -> ExecutionState
  -> Either GrammarV1SequentialExecutionError (Bool, ExecutionState)
consumeFallbackChoice source state =
  case matchingChoices source (executionChoices state) of
    [] -> Left (GrammarV1MissingExecutionChoice source)
    [choice@(GrammarV1FallbackChoice _ selected)] ->
      Right (selected, state { executionChoices = removeFirst choice (executionChoices state) })
    [_] -> Left (GrammarV1ExecutionChoiceKindMismatch source)
    _ -> Left (GrammarV1DuplicateExecutionChoice source)

matchingChoices
  :: Located GrammarV1Expression
  -> [GrammarV1ExecutionChoice]
  -> [GrammarV1ExecutionChoice]
matchingChoices source = filter ((== source) . choiceSource)

choiceSource :: GrammarV1ExecutionChoice -> Located GrammarV1Expression
choiceSource choice = case choice of
  GrammarV1IfChoice source _ -> source
  GrammarV1ArmChoice source _ -> source
  GrammarV1FallbackChoice source _ -> source

consumeTerminalEvidence
  :: Located GrammarV1Expression
  -> ExecutionState
  -> Either GrammarV1SequentialExecutionError (Bool, ExecutionState)
consumeTerminalEvidence source state =
  case filter (== source) (executionTerminalEvidence state) of
    [] -> Right (False, state)
    [_] -> Right
      ( True
      , state
          { executionTerminalEvidence = removeFirst source (executionTerminalEvidence state)
          }
      )
    _ -> Left (GrammarV1DuplicateTerminalEvidence source)

ensureUniqueTerminalEvidence
  :: [Located GrammarV1Expression]
  -> Either GrammarV1SequentialExecutionError ()
ensureUniqueTerminalEvidence [] = Right ()
ensureUniqueTerminalEvidence (first : rest)
  | first `elem` rest = Left (GrammarV1DuplicateTerminalEvidence first)
  | otherwise = ensureUniqueTerminalEvidence rest

emit :: GrammarV1ExecutionEvent -> ExecutionState -> ExecutionState
emit event state = state { executionEventsRev = event : executionEventsRev state }

removeFirst :: Eq a => a -> [a] -> [a]
removeFirst _ [] = []
removeFirst target (value : rest)
  | target == value = rest
  | otherwise = value : removeFirst target rest

atMay :: Int -> [a] -> Maybe a
atMay index values
  | index < 0 = Nothing
  | otherwise = go index values
  where
    go _ [] = Nothing
    go 0 (value : _) = Just value
    go remaining (_ : rest) = go (remaining - 1) rest