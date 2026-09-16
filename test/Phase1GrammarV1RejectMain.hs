{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Assurance.Types (Digest (..))
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.SequentialExecution
  ( GrammarV1ExecutionChoice (..)
  , GrammarV1ExecutionControl (..)
  , GrammarV1ExecutionEvent (..)
  , GrammarV1SequentialExecutionError (..)
  , grammarV1SequentialExecutionTrace
  )
import Phil.Surface.Syntax
  ( Located (..)
  , SourcePoint (..)
  , SourceSpan (..)
  )
import Phil.Systems.IR (StageContract (..))
import Phil.Systems.SequentialTrace
  ( CheckedSequentialTraceRefinement (..)
  , SequentialCommutation (..)
  , SequentialEventKey (..)
  , SequentialTraceRefinement (..)
  , SequentialTraceRefinementError (..)
  , checkSequentialTraceRefinement
  , renderSequentialCommutationRelation
  , renderSequentialTraceRelation
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ testIO "SURF-002 standalone reject fixture preserves exact operand"
        expectStandaloneReject
    , testIO "SURF-003 reject missing operand rejects at syntax"
        (expectFixtureReject "rejected/20-reject-missing-expression.phil")
    , test "SURF-002 nested reject remains structurally parseable"
        nestedRejectPreserved
    , test "SURF-002 reject fallback composes with standalone reject parsing"
        rejectFallbackPreserved
    , test "EXEC-001 statements follow textual order and terminal/return cut off the suffix"
        sequentialStatementOrder
    , test "EXEC-002 strict runtime operands execute left to right"
        strictOperandOrder
    , test "EXEC-003 only the selected branch/fallback arm executes"
        untakenBranchesDoNotExecute
    , test "EXEC sequencing fails closed rather than inventing finite loop semantics"
        loopExecutionNeedsLoopAuthority
    , test "EXEC-001 StageContract rejects unproved reorder and accepts exact commuting refinement"
        stageTraceRefinementPreservesSourceOrder
    , test "EXEC-003 StageContract rejects speculative untaken-arm events"
        stageTraceRejectsSpeculativeUntakenArm
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

testIO :: String -> IO (Either String ()) -> IO Bool
testIO label action = action >>= test label

expectStandaloneReject :: IO (Either String ())
expectStandaloneReject = do
  parsed <- parseFixture "accepted/25-standalone-reject.phil"
  pure $ do
    expression <- singleComponentExpression =<< mapLeft show parsed
    case expression of
      GrammarV1RejectExpression operand -> assertSimpleName "x" operand
      other -> Left ("expected reject expression, got " <> show other)

nestedRejectPreserved :: Either String ()
nestedRejectPreserved = do
  expression <- singleComponentExpression =<< mapLeft show
    (parseGrammarV1StructuralSource "nested-reject" source)
  case expression of
    GrammarV1RejectExpression outer -> case locatedValue outer of
      GrammarV1RejectExpression inner -> assertSimpleName "x" inner
      other -> Left ("expected nested reject operand, got " <> show other)
    other -> Left ("expected outer reject expression, got " <> show other)
  where
    source = Text.unlines
      [ "component C(x : U32) {"
      , "  reject reject x;"
      , "}"
      ]

rejectFallbackPreserved :: Either String ()
rejectFallbackPreserved = do
  expression <- singleComponentExpression =<< mapLeft show
    (parseGrammarV1StructuralSource "reject-fallback" source)
  case expression of
    GrammarV1FallbackExpression base (Located _ fallback) -> do
      assertSimpleName "x" base
      case fallback of
        GrammarV1RejectFallback value -> assertSimpleName "y" value
        other -> Left ("expected reject fallback, got " <> show other)
    other -> Left ("expected fallback expression, got " <> show other)
  where
    source = "component C(x : U32, y : U32) { x or reject y; }"

sequentialStatementOrder :: Either String ()
sequentialStatementOrder = do
  let first = callAt 100 "first" []
      second = callAt 101 "second" []
      third = callAt 102 "third" []
      terminalBlock = blockAt 110
        [ expressionStatementAt 100 first
        , expressionStatementAt 101 second
        , expressionStatementAt 102 third
        ]
  (terminalTrace, terminalControl) <- mapLeft show
    (grammarV1SequentialExecutionTrace [] [second] terminalBlock)
  assert
    (completedCallNames terminalTrace == ["first", "second"])
    "terminal second statement did not cut off the later source statement"
  assert (terminalControl == GrammarV1ExecutionTerminates)
    "terminal outcome did not leave the block terminal"

  let returnBlock = blockAt 120
        [ expressionStatementAt 120 first
        , locatedAt 121 (GrammarV1ReturnStatement second)
        , expressionStatementAt 122 third
        ]
  (returnTrace, returnControl) <- mapLeft show
    (grammarV1SequentialExecutionTrace [] [] returnBlock)
  assert
    (completedCallNames returnTrace == ["first", "second"])
    "return did not cut off the later source statement"
  assert (returnControl == GrammarV1ExecutionReturns)
    "return statement did not leave the block through return control"

strictOperandOrder :: Either String ()
strictOperandOrder = do
  let left = callAt 200 "left" []
      right = callAt 201 "right" []
      outer = callAt 202 "outer" [left, right]
      tupleLeft = callAt 203 "tupleLeft" []
      tupleRight = callAt 204 "tupleRight" []
      tupleValue = locatedAt 205 (GrammarV1TupleExpression [tupleLeft, tupleRight])
      ctorFirst = callAt 206 "ctorFirst" []
      ctorSecond = callAt 207 "ctorSecond" []
      constructorValue = locatedAt 208
        (GrammarV1ConstructExpression
          (locatedAt 208 (staticReference "Pair"))
          [ (locatedAt 208 "z", ctorFirst)
          , (locatedAt 208 "a", ctorSecond)
          ])
      binaryLeft = callAt 209 "binaryLeft" []
      binaryRight = callAt 210 "binaryRight" []
      binaryValue = locatedAt 211
        (GrammarV1BinaryExpression
          binaryLeft
          (locatedAt 211 GrammarV1Add)
          binaryRight)
      sourceBlock = blockAt 212
        [ expressionStatementAt 202 outer
        , expressionStatementAt 205 tupleValue
        , expressionStatementAt 208 constructorValue
        , expressionStatementAt 211 binaryValue
        ]
  (trace, control) <- mapLeft show
    (grammarV1SequentialExecutionTrace [] [] sourceBlock)
  assert (control == GrammarV1ExecutionContinues)
    "strict-order fixture unexpectedly terminated"
  assert
    ( completedCallNames trace
        == [ "left", "right", "outer"
           , "tupleLeft", "tupleRight"
           , "ctorFirst", "ctorSecond"
           , "binaryLeft", "binaryRight"
           ]
    )
    "call/tuple/constructor/binary children did not execute in source left-to-right order"

untakenBranchesDoNotExecute :: Either String ()
untakenBranchesDoNotExecute = do
  let condition = callAt 300 "condition" []
      taken = callAt 301 "taken" []
      untaken = callAt 302 "untaken" []
      ifExpression = locatedAt 303
        (GrammarV1IfExpression
          condition
          Nothing
          (blockAt 304 [expressionStatementAt 301 taken])
          (Just (blockAt 305 [expressionStatementAt 302 untaken])))

      scrutinee = callAt 310 "scrutinee" []
      leftArmValue = callAt 311 "leftArm" []
      rightArmValue = callAt 312 "rightArm" []
      matchExpression = locatedAt 313
        (GrammarV1MatchExpression
          scrutinee
          Nothing
          [ matchArmAt 314 "Left" leftArmValue
          , matchArmAt 315 "Right" rightArmValue
          ])

      base = callAt 320 "base" []
      fallbackValue = callAt 321 "fallback" []
      fallbackExpression = locatedAt 322
        (GrammarV1FallbackExpression
          base
          (locatedAt 322 (GrammarV1RejectFallback fallbackValue)))

      sourceBlock = blockAt 330
        [ expressionStatementAt 303 ifExpression
        , expressionStatementAt 313 matchExpression
        , expressionStatementAt 322 fallbackExpression
        ]
      choices =
        [ GrammarV1IfChoice ifExpression True
        , GrammarV1ArmChoice matchExpression 1
        , GrammarV1FallbackChoice fallbackExpression False
        ]
  (trace, control) <- mapLeft show
    (grammarV1SequentialExecutionTrace choices [] sourceBlock)
  assert (control == GrammarV1ExecutionContinues)
    "selected-branch fixture unexpectedly terminated"
  assert
    (completedCallNames trace ==
      ["condition", "taken", "scrutinee", "rightArm", "base"])
    "untaken if/match/fallback code appeared in the source execution trace"

loopExecutionNeedsLoopAuthority :: Either String ()
loopExecutionNeedsLoopAuthority = do
  let loopExpression = locatedAt 400
        (GrammarV1LoopExpression [] Nothing (blockAt 401 []))
      sourceBlock = blockAt 402 [expressionStatementAt 400 loopExpression]
  case grammarV1SequentialExecutionTrace [] [] sourceBlock of
    Left (GrammarV1LoopExecutionRequiresLoopAuthority actual) ->
      assert (actual == loopExpression)
        "loop fail-closed diagnostic lost the exact source occurrence"
    other -> Left ("general loop was approximated by the local sequential driver: " <> show other)

stageTraceRefinementPreservesSourceOrder :: Either String ()
stageTraceRefinementPreservesSourceOrder = do
  let first = callAt 500 "effectFirst" []
      second = callAt 501 "effectSecond" []
      sourceBlock = blockAt 502
        [ expressionStatementAt 500 first
        , expressionStatementAt 501 second
        ]
  (trace, control) <- mapLeft show
    (grammarV1SequentialExecutionTrace [] [] sourceBlock)
  assert (control == GrammarV1ExecutionContinues)
    "StageContract source-order fixture unexpectedly terminated"
  let sourceOrder = map eventKey (completedCallNames trace)
      exact = baseSequentialRefinement sourceOrder sourceOrder Set.empty
      exactContract = contractForSequentialRefinement exact []
  checkedExact <- mapLeft show (checkSequentialTraceRefinement exactContract exact)
  assert (Set.null (checkedSequentialTraceUsedCommutations checkedExact))
    "exact source order unexpectedly required a commutation"

  let reversedOrder = reverse sourceOrder
      unproved = baseSequentialRefinement sourceOrder reversedOrder Set.empty
      unprovedContract = contractForSequentialRefinement unproved []
  case checkSequentialTraceRefinement unprovedContract unproved of
    Left (SequentialOrderViolation _ _) -> Right ()
    other -> Left ("unproved observable reorder was not rejected: " <> show other)

  case sourceOrder of
    [firstKey, secondKey] -> do
      let commute = SequentialCommutation
            { sequentialCommutationLeft = firstKey
            , sequentialCommutationRight = secondKey
            , sequentialCommutationEvidence = "proof.exec.commute.effectFirst.effectSecond"
            }
          proved = baseSequentialRefinement
            sourceOrder
            reversedOrder
            (Set.singleton commute)
          provedContract = contractForSequentialRefinement proved [commute]
      checked <- mapLeft show (checkSequentialTraceRefinement provedContract proved)
      assert
        (checkedSequentialTraceUsedCommutations checked == Set.singleton commute)
        "accepted reorder did not retain its exact commuting evidence"
    other -> Left ("unexpected source event projection " <> show other)

stageTraceRejectsSpeculativeUntakenArm :: Either String ()
stageTraceRejectsSpeculativeUntakenArm = do
  let condition = callAt 520 "condition" []
      taken = callAt 521 "taken" []
      untaken = callAt 522 "untaken" []
      ifExpression = locatedAt 523
        (GrammarV1IfExpression
          condition
          Nothing
          (blockAt 524 [expressionStatementAt 521 taken])
          (Just (blockAt 525 [expressionStatementAt 522 untaken])))
      sourceBlock = blockAt 526 [expressionStatementAt 523 ifExpression]
  (trace, _) <- mapLeft show
    (grammarV1SequentialExecutionTrace
      [GrammarV1IfChoice ifExpression True]
      []
      sourceBlock)
  let sourceOrder = map eventKey (completedCallNames trace)
      speculativeTarget = sourceOrder <> [eventKey "untaken"]
      refinement = baseSequentialRefinement sourceOrder speculativeTarget Set.empty
      contract = contractForSequentialRefinement refinement []
  case checkSequentialTraceRefinement contract refinement of
    Left (SequentialTraceEventSetMismatch actualSource actualTarget) -> do
      assert (actualSource == sourceOrder)
        "speculation diagnostic changed the exact source projection"
      assert (actualTarget == speculativeTarget)
        "speculation diagnostic changed the exact target projection"
    other -> Left ("speculative untaken-arm event was accepted: " <> show other)

baseSequentialRefinement
  :: [SequentialEventKey]
  -> [SequentialEventKey]
  -> Set.Set SequentialCommutation
  -> SequentialTraceRefinement
baseSequentialRefinement source target commutations = SequentialTraceRefinement
  { sequentialTraceStageContractId = "stage.exec.order.v1"
  , sequentialTraceSourceDigest = Digest "source.exec.order.v1"
  , sequentialTraceTargetDigest = Digest "target.exec.order.v1"
  , sequentialTraceSourceOrder = source
  , sequentialTraceTargetProjection = target
  , sequentialTraceCommutations = commutations
  }

contractForSequentialRefinement
  :: SequentialTraceRefinement
  -> [SequentialCommutation]
  -> StageContract
contractForSequentialRefinement refinement commutations = StageContract
  { stageContractId = sequentialTraceStageContractId refinement
  , stageSourceArtifactDigest = sequentialTraceSourceDigest refinement
  , stageTargetArtifactDigest = sequentialTraceTargetDigest refinement
  , stageFacts = []
  , stageInvariants = Map.empty
  , stageRequiredEdges = []
  , stageDerivedObligations = []
  , stageAssumptions = []
  , stageTraceRelation =
      renderSequentialTraceRelation refinement
        : map renderSequentialCommutationRelation commutations
  , stageResourceFailureRelation = []
  }

eventKey :: Text.Text -> SequentialEventKey
eventKey = SequentialEventKey . ("event." <>)

completedCallNames :: [GrammarV1ExecutionEvent] -> [Text.Text]
completedCallNames events =
  [ Text.intercalate "." (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference))
  | GrammarV1ExpressionCompleted (Located _ expression) <- events
  , GrammarV1NameExpression reference _ <- [expression]
  ]

matchArmAt
  :: Int
  -> Text.Text
  -> Located GrammarV1Expression
  -> Located GrammarV1MatchArm
matchArmAt line label value = locatedAt line GrammarV1MatchArm
  { grammarV1MatchArmPattern = locatedAt line GrammarV1CasePattern
      { grammarV1CasePatternName = locatedAt line (GrammarV1QualifiedName [label])
      , grammarV1CasePatternBinders = Nothing
      }
  , grammarV1MatchArmBody = GrammarV1MatchArmStatement
      (expressionStatementAt line value)
  }

callAt :: Int -> Text.Text -> [Located GrammarV1Expression] -> Located GrammarV1Expression
callAt line name arguments = locatedAt line
  (GrammarV1NameExpression (staticReference name) arguments)

staticReference :: Text.Text -> GrammarV1StaticReference
staticReference name = GrammarV1StaticReference
  { grammarV1StaticReferenceName = GrammarV1QualifiedName [name]
  , grammarV1StaticReferenceArguments = []
  }

expressionStatementAt
  :: Int
  -> Located GrammarV1Expression
  -> Located GrammarV1Statement
expressionStatementAt line expression = locatedAt line
  (GrammarV1ExpressionStatement expression)

blockAt :: Int -> [Located GrammarV1Statement] -> Located GrammarV1Block
blockAt line statements = locatedAt line (GrammarV1Block statements)

locatedAt :: Int -> a -> Located a
locatedAt line = Located (spanAt line)

spanAt :: Int -> SourceSpan
spanAt line = SourceSpan point point
  where
    point = SourcePoint
      { sourcePointFile = "sequential-execution"
      , sourcePointLine = line
      , sourcePointColumn = 1
      , sourcePointOffset = line * 10
      }

singleComponentExpression :: GrammarV1SourceFile -> Either String GrammarV1Expression
singleComponentExpression sourceFile =
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ComponentDeclaration componentDecl ->
        case grammarV1BlockStatements (locatedValue (grammarV1ComponentBody componentDecl)) of
          [Located _ (GrammarV1ExpressionStatement expression)] -> Right (locatedValue expression)
          statements -> Left ("expected one expression statement, got " <> show statements)
      other -> Left ("expected component declaration, got " <> show other)
    declarations -> Left ("expected one top-level declaration, got " <> show (length declarations))

assertSimpleName :: Text.Text -> Located GrammarV1Expression -> Either String ()
assertSimpleName expected (Located _ expression) = case expression of
  GrammarV1NameExpression reference arguments -> do
    assert
      (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == [expected])
      ("expected simple name " <> Text.unpack expected)
    assert (null (grammarV1StaticReferenceArguments reference))
      "simple name unexpectedly had static arguments"
    assert (null arguments) "simple name unexpectedly had term arguments"
  other -> Left ("expected simple name expression, got " <> show other)

expectFixtureReject :: FilePath -> IO (Either String ())
expectFixtureReject relativePath = do
  parsed <- parseFixture relativePath
  pure $ case parsed of
    Left _ -> Right ()
    Right value -> Left ("expected syntax rejection, parsed " <> show value)

parseFixture
  :: FilePath
  -> IO (Either GrammarV1ParseDiagnostic GrammarV1SourceFile)
parseFixture relativePath = do
  let path = "test/fixtures/phase1-surface/" <> relativePath
  source <- TextIO.readFile path
  pure (parseGrammarV1StructuralSource (Text.pack relativePath) source)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
