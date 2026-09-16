{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Compiler.CallableInvocationSemantics
  ( SurfaceCallableInvocationSemanticAccount (..)
  )
import Phil.Compiler.CallableOutcomeDispatch
  ( SurfaceCallableOutcomeBinding (..)
  , SurfaceCallableOutcomeBranch (..)
  , SurfaceCallableOutcomeControl (..)
  , SurfaceCallableOutcomeDispatchError (..)
  , SurfaceCallableOutcomeDispatchPlan (..)
  , planSurfaceCallableOutcomeDispatch
  )
import Phil.Core.Callable
  ( CalleeTransition (..)
  , SemanticEffect (..)
  )
import Phil.Core.CallableOutcome
  ( CallableOutcomeAtom (..)
  , CallableOutcomeClass (..)
  , CallableOutcomeContract (..)
  , CallableOutcomeState (..)
  )
import Phil.Core.CallableRefinement
  ( CallableAuthorityRequirement (..)
  , CallableFailure (..)
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Outcome (..)
  , Ty (..)
  )
import Phil.Surface.Syntax
  ( SourcePoint (..)
  , SourceSpan (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CALL-019 outcome dispatch preserves semantic branch order and categories"
        exactDispatchPreserved
    , test "CALL-019 typed-negative continues while terminal/fatal outcomes stop"
        outcomeControlPreserved
    , test "CALL-019 outcome dispatch rejects missing source branch binding"
        missingBindingRejects
    , test "CALL-019 outcome dispatch rejects callable outcome key substitution"
        bindingKeyMismatchRejects
    , test "CALL-019 outcome dispatch rejects duplicate source branch labels"
        duplicateLabelRejects
    , test "CALL-019 outcome dispatch rejects empty source branch labels"
        emptyLabelRejects
    , test "CALL-019 outcome dispatch rejects duplicate semantic outcome classes"
        duplicateSemanticClassRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

span1 :: SourceSpan
span1 = SourceSpan
  (SourcePoint "call019-outcome-dispatch" 1 1 0)
  (SourcePoint "call019-outcome-dispatch" 1 20 19)

negativeFailure, terminalFailure, fatalFailure :: CallableFailure
negativeFailure = CallableTypedNegative (Outcome "not-found")
terminalFailure = CallableDeclaredTerminal (Outcome "closed")
fatalFailure = CallableFatal "panic"

successClass, negativeClass, terminalClass, fatalClass :: CallableOutcomeClass
successClass = CallableSuccessOutcome
negativeClass = CallableNonSuccessOutcome negativeFailure
terminalClass = CallableNonSuccessOutcome terminalFailure
fatalClass = CallableNonSuccessOutcome fatalFailure

successOutcome, negativeOutcome, terminalOutcome, fatalOutcome :: CallableOutcomeContract
successOutcome = outcome successClass "success" PreserveCallee "post:success" "residual:success"
negativeOutcome = outcome negativeClass "negative" PreserveCallee "post:negative" "residual:negative"
terminalOutcome = outcome terminalClass "terminal" ConsumeCallee "post:terminal" "residual:terminal"
fatalOutcome = outcome fatalClass "fatal" ConsumeCallee "post:fatal" "residual:fatal"

outcome
  :: CallableOutcomeClass
  -> Text
  -> CalleeTransition
  -> Text
  -> Text
  -> CallableOutcomeContract
outcome outcomeClass state transition post residual = CallableOutcomeContract
  { callableOutcomeClass = outcomeClass
  , callableOutcomeState = CallableOutcomeState state
  , callableOutcomeCalleeTransition = transition
  , callableOutcomePostconditions = Set.singleton (CallableOutcomeAtom post)
  , callableOutcomeResidualObligations = Set.singleton (CallableOutcomeAtom residual)
  , callableOutcomeAssumptions = Set.singleton (CallableOutcomeAtom ("assume:" <> state))
  , callableOutcomeEffects = Set.singleton (CallableOutcomeAtom ("effect:" <> state))
  , callableOutcomeDischargedFacts = Set.singleton (CallableOutcomeAtom ("fact:" <> state))
  }

invocation :: [CallableOutcomeContract] -> SurfaceCallableInvocationSemanticAccount
invocation outcomes = SurfaceCallableInvocationSemanticAccount
  { surfaceSemanticInvocationSpan = span1
  , surfaceSemanticInvocationDisplayName = "Lookup"
  , surfaceSemanticInvocationDeclarationKey = DeclarationKey "decl.lookup"
  , surfaceSemanticInvocationCallerAuthority =
      Set.singleton (CallableAuthorityRequirement "authority:lookup")
  , surfaceSemanticInvocationPublicEffectBound =
      Set.singleton (SemanticEffect "effect:lookup")
  , surfaceSemanticInvocationCalleeTransition = PreserveCallee
  , surfaceSemanticInvocationModeledFailures =
      Set.fromList [negativeFailure, terminalFailure, fatalFailure]
  , surfaceSemanticInvocationOutcomes = outcomes
  }

binding
  :: CallableOutcomeClass
  -> Text
  -> [(Mode, Ty)]
  -> SurfaceCallableOutcomeBinding
binding outcomeClass label payload = SurfaceCallableOutcomeBinding
  { surfaceOutcomeBindingClass = outcomeClass
  , surfaceOutcomeBindingLabel = label
  , surfaceOutcomeBindingPayload = payload
  }

bindings :: Map.Map CallableOutcomeClass SurfaceCallableOutcomeBinding
bindings = Map.fromList
  [ (successClass, binding successClass "ok" [(Linear, TyOpaque "Blob")])
  , (negativeClass, binding negativeClass "missing" [(Unrestricted, TyOpaque "Reason")])
  , (terminalClass, binding terminalClass "closed" [])
  , (fatalClass, binding fatalClass "fatal" [])
  ]

allOutcomes :: [CallableOutcomeContract]
allOutcomes = [successOutcome, negativeOutcome, terminalOutcome, fatalOutcome]

exactDispatchPreserved :: Either String ()
exactDispatchPreserved = do
  plan <- mapLeft show $
    planSurfaceCallableOutcomeDispatch bindings (invocation allOutcomes)
  let branches = surfaceOutcomeDispatchBranches plan
  assert
    (map surfaceOutcomeBranchClass branches
      == [successClass, negativeClass, terminalClass, fatalClass])
    "dispatch reordered semantic outcome classes"
  assert
    (map surfaceOutcomeBranchLabel branches == ["ok", "missing", "closed", "fatal"])
    "dispatch lost explicit source branch labels"
  assert
    (map surfaceOutcomeBranchPayload branches
      == [ [(Linear, TyOpaque "Blob")]
         , [(Unrestricted, TyOpaque "Reason")]
         , []
         , []
         ])
    "dispatch lost typed source branch payloads"
  assert
    (map surfaceOutcomeBranchContract branches == allOutcomes)
    "dispatch weakened or reconstructed branch-local semantic contracts"

outcomeControlPreserved :: Either String ()
outcomeControlPreserved = do
  plan <- mapLeft show $
    planSurfaceCallableOutcomeDispatch bindings (invocation allOutcomes)
  assert
    (map surfaceOutcomeBranchControl (surfaceOutcomeDispatchBranches plan)
      == [ SurfaceCallableOutcomeContinues
         , SurfaceCallableOutcomeContinues
         , SurfaceCallableOutcomeDeclaredTerminal
         , SurfaceCallableOutcomeFatalTerminal
         ])
    "outcome continuation/terminal classification was collapsed"

missingBindingRejects :: Either String ()
missingBindingRejects =
  expectError
    (\err -> case err of
      SurfaceCallableOutcomeBindingDomainMismatch expected actual ->
        Set.member fatalClass expected && not (Set.member fatalClass actual)
      _ -> False)
    (Map.delete fatalClass bindings)
    (invocation allOutcomes)
    "missing source branch binding"

bindingKeyMismatchRejects :: Either String ()
bindingKeyMismatchRejects =
  let substituted = (bindings Map.! successClass)
        { surfaceOutcomeBindingClass = negativeClass }
  in expectError
      (\err -> case err of
        SurfaceCallableOutcomeBindingKeyMismatch expected actual ->
          expected == successClass && actual == negativeClass
        _ -> False)
      (Map.insert successClass substituted bindings)
      (invocation allOutcomes)
      "outcome binding key substitution"

duplicateLabelRejects :: Either String ()
duplicateLabelRejects =
  let duplicated = (bindings Map.! negativeClass)
        { surfaceOutcomeBindingLabel = "ok" }
  in expectError
      (\err -> case err of
        SurfaceCallableDuplicateOutcomeLabel "ok" -> True
        _ -> False)
      (Map.insert negativeClass duplicated bindings)
      (invocation allOutcomes)
      "duplicate source branch label"

emptyLabelRejects :: Either String ()
emptyLabelRejects =
  let empty = (bindings Map.! terminalClass)
        { surfaceOutcomeBindingLabel = "" }
  in expectError
      (\err -> case err of
        SurfaceCallableOutcomeEmptyLabel outcomeClass -> outcomeClass == terminalClass
        _ -> False)
      (Map.insert terminalClass empty bindings)
      (invocation allOutcomes)
      "empty source branch label"

duplicateSemanticClassRejects :: Either String ()
duplicateSemanticClassRejects =
  expectError
    (\err -> case err of
      SurfaceCallableDuplicateOutcomeClass outcomeClass -> outcomeClass == successClass
      _ -> False)
    bindings
    (invocation (successOutcome : allOutcomes))
    "duplicate semantic outcome class"

expectError
  :: (SurfaceCallableOutcomeDispatchError -> Bool)
  -> Map.Map CallableOutcomeClass SurfaceCallableOutcomeBinding
  -> SurfaceCallableInvocationSemanticAccount
  -> String
  -> Either String ()
expectError predicate catalog account label =
  case planSurfaceCallableOutcomeDispatch catalog account of
    Left err | predicate err -> Right ()
    Left err -> Left ("unexpected " <> label <> " error: " <> show err)
    Right plan -> Left ("expected " <> label <> " rejection, got " <> show plan)

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
