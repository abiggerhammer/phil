{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Syntax
  ( Name (..)
  , Ty (..)
  )
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.GrammarV1.CallableOutcomeState
  ( grammarV1CallableOutcomeStateTelescopes
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 callable outcome state preserves branch and telescope structure"
        primitiveOutcomeStateTelescopes
    , test "SURF-008 repeated outcome state clauses remain distinct"
        repeatedStateClausesRemainDistinct
    , test "SURF-008 duplicate outcome state slots fail closed"
        duplicateStateSlotsReject
    , test "SURF-008 nonprimitive outcome state slots remain outside competence"
        nonprimitiveStateSlotsReject
    , test "SURF-008 generic callable outcome state remains outside primitive scope"
        genericCallableStateRejects
    , test "SURF-008 callable without outcome residues has exact empty projection"
        absentOutcomeResiduesAreEmpty
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

primitiveOutcomeStateTelescopes :: Either String ()
primitiveOutcomeStateTelescopes = do
  callable <- onlyCallable $ Text.unlines
    [ "callable Run(x : U32) -> Unit {"
    , "  outcomes { success Done, negative Retry, terminal Closed, fatal Crashed };"
    , "  outcome success Done { state (x_next : U32); }"
    , "  outcome negative Retry { state (retry : U8, flag : Bool); }"
    , "  outcome terminal Closed { state (); }"
    , "  outcome fatal Crashed {}"
    , "}"
    ]
  assert
    ( grammarV1CallableOutcomeStateTelescopes emptySurfaceState callable ==
        Just
          [ (GrammarV1SuccessOutcome, [[(Name "x_next", TyUInt 32)]])
          , ( GrammarV1NegativeOutcome
            , [[(Name "retry", TyUInt 8), (Name "flag", TyBool)]]
            )
          , (GrammarV1TerminalOutcome, [[]])
          , (GrammarV1FatalOutcome, [])
          ]
    )
    "outcome kind, slot order/type, empty state, or absent-state distinction changed"

repeatedStateClausesRemainDistinct :: Either String ()
repeatedStateClausesRemainDistinct = do
  callable <- onlyCallable $ Text.unlines
    [ "callable RepeatedState() -> Unit {"
    , "  outcome success Done {"
    , "    state (a : U8);"
    , "    state (b : Bool);"
    , "  }"
    , "}"
    ]
  assert
    ( grammarV1CallableOutcomeStateTelescopes emptySurfaceState callable ==
        Just
          [ ( GrammarV1SuccessOutcome
            , [[(Name "a", TyUInt 8)], [(Name "b", TyBool)]]
            )
          ]
    )
    "repeated state clauses were merged, reordered, or dropped"

duplicateStateSlotsReject :: Either String ()
duplicateStateSlotsReject = do
  callable <- onlyCallable
    "callable DuplicateState() -> Unit { outcome success Done { state (x : U8, x : Bool); } }"
  assert
    (grammarV1CallableOutcomeStateTelescopes emptySurfaceState callable == Nothing)
    "duplicate state-slot names escaped the ordinary binding authority"

nonprimitiveStateSlotsReject :: Either String ()
nonprimitiveStateSlotsReject = do
  callable <- onlyCallable
    "callable NamedState() -> Unit { outcome success Done { state (blob : Blob); } }"
  assert
    (grammarV1CallableOutcomeStateTelescopes emptySurfaceState callable == Nothing)
    "named state type acquired an invented unrestricted structural mode"

genericCallableStateRejects :: Either String ()
genericCallableStateRejects = do
  callable <- onlyCallable
    "callable GenericState[T : Type]() -> Unit { outcome success Done { state (x : U8); } }"
  assert
    (grammarV1CallableOutcomeStateTelescopes emptySurfaceState callable == Nothing)
    "generic callable bypassed the shared primitive parameter-scope competence wall"

absentOutcomeResiduesAreEmpty :: Either String ()
absentOutcomeResiduesAreEmpty = do
  callable <- onlyCallable
    "callable NoResidues() -> Unit { outcomes { success Done }; }"
  assert
    (grammarV1CallableOutcomeStateTelescopes emptySurfaceState callable == Just [])
    "callable without outcome residues did not preserve exact absence"

onlyCallable :: Text.Text -> Either String GrammarV1CallableContractDecl
onlyCallable source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "callable-outcome-state" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1CallableContractDeclaration callable -> Right callable
      other -> Left ("expected callable declaration, got " <> show other)
    declarations -> Left ("expected one declaration, got " <> show (length declarations))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
