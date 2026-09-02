{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Callable
  ( CalleeTransition (..)
  )
import Phil.Surface.GrammarV1.CallableCalleeTransition
  ( grammarV1CalleeTransition
  , grammarV1CallableCalleeTransitions
  , grammarV1OutcomeCalleeTransitions
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  result <- test
    "SURF-008 callable and outcome callee transitions preserve exact Core lifecycle choices"
    calleeTransitionsRouteExactly
  if result then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

calleeTransitionsRouteExactly :: Either String ()
calleeTransitionsRouteExactly = do
  assert
    (grammarV1CalleeTransition GrammarV1CalleePreserve == Just PreserveCallee)
    "preserve did not map exactly to Core PreserveCallee"
  assert
    (grammarV1CalleeTransition GrammarV1CalleeConsume == Just ConsumeCallee)
    "consume did not map exactly to Core ConsumeCallee"

  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "surf008-callee-transitions" source
  declarations <- mapM callableDeclaration (grammarV1TopLevelDecls sourceFile)
  case declarations of
    [ordered, replaceTop, replaceResidue, absent] -> do
      assert
        (grammarV1CallableCalleeTransitions ordered
          == Just [PreserveCallee, ConsumeCallee])
        "top-level preserve/consume transitions lost source order or Core identity"
      orderedResidue <- onlyResidue ordered
      assert
        (grammarV1OutcomeCalleeTransitions orderedResidue
          == Just [PreserveCallee, ConsumeCallee])
        "outcome preserve/consume transitions lost source order or Core identity"

      assert
        (grammarV1CallableCalleeTransitions replaceTop == Nothing)
        "replace transition invented an InterfaceRevision or state identity"

      replacementResidue <- onlyResidue replaceResidue
      assert
        (grammarV1OutcomeCalleeTransitions replacementResidue == Nothing)
        "outcome replace transition invented an InterfaceRevision or state identity"

      assert
        (grammarV1CallableCalleeTransitions absent == Just [])
        "absent callable callee category did not remain exact empty"
    other -> Left
      ("expected four callable declarations, got " <> show (length other))

callableDeclaration
  :: Located GrammarV1TopLevelDecl
  -> Either String GrammarV1CallableContractDecl
callableDeclaration (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1CallableContractDeclaration declaration -> Right declaration
    other -> Left ("expected callable declaration, got " <> show other)

onlyResidue
  :: GrammarV1CallableContractDecl
  -> Either String GrammarV1OutcomeResidue
onlyResidue callable =
  case
    [ locatedValue residue
    | Located _ (GrammarV1CallableOutcomeResidue residue) <-
        grammarV1CallableClauses callable
    ] of
    [residue] -> Right residue
    residues -> Left
      ("expected exactly one outcome residue, got " <> show (length residues))

source :: Text.Text
source = Text.unlines
  [ "callable Ordered(x : U8) -> U8 {"
  , "  outcomes { success U8 };"
  , "  callee preserve;"
  , "  callee consume;"
  , "  outcome success U8 {"
  , "    state ();"
  , "    callee preserve;"
  , "    callee consume;"
  , "  }"
  , "}"
  , "callable ReplaceTop(x : U8) -> U8 {"
  , "  callee replace with NextCallable state x;"
  , "}"
  , "callable ReplaceResidue(x : U8) -> U8 {"
  , "  outcomes { success U8 };"
  , "  outcome success U8 {"
  , "    state ();"
  , "    callee replace with NextCallable state x;"
  , "  }"
  , "}"
  , "callable Absent(x : U8) -> U8 {}"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
