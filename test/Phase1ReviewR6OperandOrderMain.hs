{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.SequentialExecution
  ( GrammarV1ExecutionControl (..)
  , GrammarV1ExecutionEvent (..)
  , GrammarV1SequentialExecutionError
  , grammarV1SequentialExecutionTrace
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "REVIEW-R06 receive_exact evaluates using before later on"
        receiveExactUsingOrder
    , test "REVIEW-R06 receive_exact without using preserves amount/on order"
        receiveExactWithoutUsingOrder
    , test "REVIEW-R06 terminal receive_exact using suppresses later on operand"
        receiveExactTerminalUsing
    , test "REVIEW-R06 select evaluates using before later on"
        selectUsingOrder
    , test "REVIEW-R06 select without using preserves branch-argument/on order"
        selectWithoutUsingOrder
    , test "REVIEW-R06 terminal select using suppresses later on operand"
        selectTerminalUsing
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

receiveExactUsingOrder :: Either String ()
receiveExactUsingOrder =
  expectOrder
    "receive-exact-using"
    "receive_exact amount() using evidence() on endpoint()"
    ["amount", "evidence", "endpoint"]

receiveExactWithoutUsingOrder :: Either String ()
receiveExactWithoutUsingOrder =
  expectOrder
    "receive-exact-no-using"
    "receive_exact amount() on endpoint()"
    ["amount", "endpoint"]

receiveExactTerminalUsing :: Either String ()
receiveExactTerminalUsing = do
  expression <- parseExpression
    "receive-exact-terminal-using"
    "receive_exact amount() using evidence() on endpoint()"
  evidence <- case locatedValue expression of
    GrammarV1ReceiveExactExpression _ _ (Just actual) -> Right actual
    other -> Left ("expected receive_exact with using operand, got " <> show other)
  (events, control) <- mapLeft show
    (traceExpression [evidence] expression)
  assert (control == GrammarV1ExecutionTerminates)
    "terminal receive_exact using operand did not terminate the expression"
  assert
    (startedCallNames events == ["amount", "evidence"])
    "later receive_exact on operand started despite terminal using operand"
  assert
    (completedCallNames events == ["amount", "evidence"])
    "later receive_exact on operand completed despite terminal using operand"

selectUsingOrder :: Either String ()
selectUsingOrder =
  expectOrder
    "select-using"
    "select Go(payload()) using boundaryArg() on endpoint()"
    ["payload", "boundaryArg", "endpoint"]

selectWithoutUsingOrder :: Either String ()
selectWithoutUsingOrder =
  expectOrder
    "select-no-using"
    "select Go(payload()) on endpoint()"
    ["payload", "endpoint"]

selectTerminalUsing :: Either String ()
selectTerminalUsing = do
  expression <- parseExpression
    "select-terminal-using"
    "select Go(payload()) using boundaryArg() on endpoint()"
  boundary <- case locatedValue expression of
    GrammarV1SelectExpression _ _ (Just actual) -> Right actual
    other -> Left ("expected select with using operand, got " <> show other)
  (events, control) <- mapLeft show
    (traceExpression [boundary] expression)
  assert (control == GrammarV1ExecutionTerminates)
    "terminal select using operand did not terminate the expression"
  assert
    (startedCallNames events == ["payload", "boundaryArg"])
    "later select on operand started despite terminal using operand"
  assert
    (completedCallNames events == ["payload", "boundaryArg"])
    "later select on operand completed despite terminal using operand"

expectOrder :: Text.Text -> Text.Text -> [Text.Text] -> Either String ()
expectOrder label source expected = do
  expression <- parseExpression label source
  (events, control) <- mapLeft show (traceExpression [] expression)
  assert (control == GrammarV1ExecutionContinues)
    "operand-order control unexpectedly terminated"
  assert
    (startedCallNames events == expected)
    ("started child order mismatch: " <> show (startedCallNames events))
  assert
    (completedCallNames events == expected)
    ("completed child order mismatch: " <> show (completedCallNames events))

parseExpression
  :: Text.Text
  -> Text.Text
  -> Either String (Located GrammarV1Expression)
parseExpression label source = do
  parsed <- mapLeft show
    (parseGrammarV1StructuralSource label
      ("component C() { " <> source <> "; }"))
  case grammarV1TopLevelDecls parsed of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ComponentDeclaration componentDecl ->
        case grammarV1BlockStatements
          (locatedValue (grammarV1ComponentBody componentDecl)) of
          [Located _ (GrammarV1ExpressionStatement expression)] -> Right expression
          statements -> Left
            ("expected one expression statement, got " <> show statements)
      other -> Left ("expected component declaration, got " <> show other)
    declarations -> Left
      ("expected one top-level declaration, got " <> show (length declarations))

traceExpression
  :: [Located GrammarV1Expression]
  -> Located GrammarV1Expression
  -> Either
      GrammarV1SequentialExecutionError
      ([GrammarV1ExecutionEvent], GrammarV1ExecutionControl)
traceExpression terminalEvidence expression =
  grammarV1SequentialExecutionTrace
    []
    terminalEvidence
    ( Located (locatedSpan expression)
        (GrammarV1Block
          [ Located (locatedSpan expression)
              (GrammarV1ExpressionStatement expression)
          ])
    )

startedCallNames :: [GrammarV1ExecutionEvent] -> [Text.Text]
startedCallNames events =
  [ renderReference reference
  | GrammarV1ExpressionStarted (Located _ expression) <- events
  , GrammarV1NameExpression reference _ <- [expression]
  ]

completedCallNames :: [GrammarV1ExecutionEvent] -> [Text.Text]
completedCallNames events =
  [ renderReference reference
  | GrammarV1ExpressionCompleted (Located _ expression) <- events
  , GrammarV1NameExpression reference _ <- [expression]
  ]

renderReference :: GrammarV1StaticReference -> Text.Text
renderReference =
  Text.intercalate "."
    . grammarV1QualifiedNameParts
    . grammarV1StaticReferenceName

assert :: Bool -> String -> Either String ()
assert condition detail = if condition then Right () else Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f result = case result of
  Left err -> Left (f err)
  Right value -> Right value
