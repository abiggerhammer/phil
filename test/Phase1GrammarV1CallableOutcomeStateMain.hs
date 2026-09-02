{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Focusing (FocusingError (..))
import Phil.Core.Static
  ( StaticContext
  , declareOpaqueClaim
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Name (..)
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  , Ty (..)
  )
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.GrammarV1.CallableOutcomePropositions
  ( grammarV1CallableOutcomeEnsures
  , grammarV1CallableOutcomeObligations
  )
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
    , test "SURF-008 outcome propositions use exact parameter plus branch-state scope"
        checkedOutcomePropositionsUseBranchScope
    , test "SURF-008 outcome propositions reject unresolved branch-state names structurally"
        missingOutcomeStateBindingRejects
    , test "SURF-008 repeated outcome state is ambiguous for proposition scope"
        repeatedOutcomeStateScopeRejects
    , test "SURF-008 outcome proposition Core failures remain distinct"
        outcomePropositionCoreFailurePreserved
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
  context <- checkedContext
  assert
    (grammarV1CallableOutcomeEnsures context emptySurfaceState callable == Just (Right []))
    "outcome ensures projection did not preserve exact absence"
  assert
    (grammarV1CallableOutcomeObligations context emptySurfaceState callable == Just (Right []))
    "outcome obligation projection did not preserve exact absence"

checkedOutcomePropositionsUseBranchScope :: Either String ()
checkedOutcomePropositionsUseBranchScope = do
  context <- checkedContext
  callable <- onlyCallable $ Text.unlines
    [ "callable CheckedOutcome(x : U32) -> Unit {"
    , "  outcome success Done {"
    , "    state (s : U8);"
    , "    ensures PairOk(x, s);"
    , "    obligation PairOk(x, s);"
    , "    ensures ParamOk(x);"
    , "  }"
    , "  outcome negative Retry {"
    , "    ensures ParamOk(x);"
    , "  }"
    , "}"
    ]
  case
      ( grammarV1CallableOutcomeEnsures context emptySurfaceState callable
      , grammarV1CallableOutcomeObligations context emptySurfaceState callable
      ) of
    (Just (Right ensured), Just (Right obligations)) -> do
      let x = RefVar (Name "x")
          s = RefVar (Name "s")
          pair = Atom "PairOk" [x, s]
          parameterOnly = Atom "ParamOk" [x]
      assert
        (stripSteps ensured ==
          [ (GrammarV1SuccessOutcome, [pair, parameterOnly])
          , (GrammarV1NegativeOutcome, [parameterOnly])
          ])
        ("outcome ensures lost branch scope/category/order: " <> show ensured)
      assert
        (stripSteps obligations ==
          [ (GrammarV1SuccessOutcome, [pair])
          , (GrammarV1NegativeOutcome, [])
          ])
        ("outcome obligations were reclassified or lost branch scope: " <> show obligations)
    other -> Left
      ("checked outcome propositions did not preserve branch scope/categories: " <> show other)

missingOutcomeStateBindingRejects :: Either String ()
missingOutcomeStateBindingRejects = do
  context <- checkedContext
  callable <- onlyCallable $ Text.unlines
    [ "callable MissingState(x : U32) -> Unit {"
    , "  outcome success Done {"
    , "    ensures PairOk(x, s);"
    , "  }"
    , "}"
    ]
  assert
    (grammarV1CallableOutcomeEnsures context emptySurfaceState callable == Nothing)
    "unbound branch-state name reached Core focusing or acquired an ambient meaning"

repeatedOutcomeStateScopeRejects :: Either String ()
repeatedOutcomeStateScopeRejects = do
  context <- checkedContext
  callable <- onlyCallable $ Text.unlines
    [ "callable AmbiguousState(x : U32) -> Unit {"
    , "  outcome success Done {"
    , "    state (a : U8);"
    , "    state (b : U8);"
    , "    ensures ParamOk(x);"
    , "  }"
    , "}"
    ]
  assert
    (grammarV1CallableOutcomeEnsures context emptySurfaceState callable == Nothing)
    "checked proposition routing arbitrarily selected one of several state scopes"

outcomePropositionCoreFailurePreserved :: Either String ()
outcomePropositionCoreFailurePreserved = do
  context <- checkedContext
  callable <- onlyCallable $ Text.unlines
    [ "callable CoreReject(x : U32) -> Unit {"
    , "  outcome success Done {"
    , "    state (s : U8);"
    , "    ensures Missing(x);"
    , "  }"
    , "}"
    ]
  case grammarV1CallableOutcomeEnsures context emptySurfaceState callable of
    Just (Left (UnknownClaim "Missing")) -> Right ()
    other -> Left ("Core UnknownClaim was collapsed or changed: " <> show other)

checkedContext :: Either String StaticContext
checkedContext = do
  context1 <- mapLeft show $
    declareOpaqueClaim
      "PairOk"
      [(Name "x", SortUInt 32), (Name "s", SortUInt 8)]
      emptyStaticContext
  mapLeft show $
    declareOpaqueClaim "ParamOk" [(Name "x", SortUInt 32)] context1

stripSteps
  :: [(GrammarV1OutcomeKind, [(Proposition, steps)])]
  -> [(GrammarV1OutcomeKind, [Proposition])]
stripSteps = map (\(kind, propositions) -> (kind, map fst propositions))

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
