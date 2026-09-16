{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Compiler.CallableInvocationContext
  ( CheckedSurfaceCallableInvocationContext (..)
  , SurfaceCallableCallerContext (..)
  , SurfaceCallableInvocationContextError (..)
  , checkSurfaceCallableInvocationSummary
  , checkSurfaceCallableInvocationSummaryWithOutcomeBranches
  )
import Phil.Compiler.CallableInvocationSemantics
  ( SurfaceCallableInvocationSemanticAccount (..)
  , SurfaceCallableSemanticSummary (..)
  )
import Phil.Compiler.CallableOutcomeBranchSemantics
  ( SurfaceCallableOutcomeArmSemanticWitness (..)
  )
import Phil.Compiler.CallableOutcomeDispatch
  ( SurfaceCallableOutcomeControl (..)
  )
import Phil.Core.Callable
  ( CalleeTransition (..)
  , CallableContract (..)
  )
import Phil.Core.CallableOutcome
  ( CallableOutcomeAtom (..)
  , CallableOutcomeClass (..)
  , CallableOutcomeContract (..)
  , CallableOutcomeState (..)
  )
import Phil.Core.CallableRefinement
  ( CallableFailure (..)
  , CallableMachineShape (..)
  , CallableRefinementSurface (..)
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  , InterfaceRevision (..)
  )
import Phil.Core.Syntax
  ( Outcome (..)
  )
import Phil.Surface.Syntax
  ( SourcePoint (..)
  , SourceSpan (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CALL-019 legacy invocation context remains fail-closed for branch outcomes"
        legacyStillRejects
    , test "CALL-019 exact branch witnesses admit branch-sensitive direct invocation"
        exactWitnessesAccept
    , test "CALL-019 branch-aware context requires witnesses for branch-sensitive invocation"
        missingWitnessesReject
    , test "CALL-019 branch-aware context requires exact witness domain"
        partialWitnessDomainRejects
    , test "CALL-019 branch-aware context rejects complete-contract substitution"
        contractSubstitutionRejects
    , test "CALL-019 branch-aware context rejects duplicate semantic branch witness"
        duplicateWitnessRejects
    , test "CALL-019 branch-aware context rejects branch-control substitution"
        controlSubstitutionRejects
    , test "CALL-019 branch-aware context rejects witness from another declaration"
        unownedWitnessRejects
    , test "CALL-019 branch-aware context still checks branch-local callee transition"
        branchTransitionMismatchRejects
    , test "CALL-019 hand-constructed fatal branch witness cannot bypass Surface fatal seam"
        fatalWitnessRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

branchKey, otherKey :: DeclarationKey
branchKey = DeclarationKey "decl.branch"
otherKey = DeclarationKey "decl.other"

invocationSpan, successArmSpan, negativeArmSpan, fatalArmSpan :: SourceSpan
invocationSpan = spanAt 1 10
successArmSpan = spanAt 20 30
negativeArmSpan = spanAt 31 42
fatalArmSpan = spanAt 43 51

spanAt :: Int -> Int -> SourceSpan
spanAt start end = SourceSpan
  (SourcePoint "call019-branch-context" 1 start (start - 1))
  (SourcePoint "call019-branch-context" 1 end (end - 1))

negativeFailure, fatalFailure :: CallableFailure
negativeFailure = CallableTypedNegative (Outcome "negative")
fatalFailure = CallableFatal "fatal:branch"

successClass, negativeClass, fatalClass :: CallableOutcomeClass
successClass = CallableSuccessOutcome
negativeClass = CallableNonSuccessOutcome negativeFailure
fatalClass = CallableNonSuccessOutcome fatalFailure

atom :: Text -> CallableOutcomeAtom
atom = CallableOutcomeAtom

outcome
  :: CallableOutcomeClass
  -> Text
  -> CalleeTransition
  -> Text
  -> CallableOutcomeContract
outcome outcomeClass state transition suffix = CallableOutcomeContract
  { callableOutcomeClass = outcomeClass
  , callableOutcomeState = CallableOutcomeState state
  , callableOutcomeCalleeTransition = transition
  , callableOutcomePostconditions = Set.singleton (atom ("post:" <> suffix))
  , callableOutcomeResidualObligations = Set.singleton (atom ("residual:" <> suffix))
  , callableOutcomeAssumptions = Set.singleton (atom ("assume:" <> suffix))
  , callableOutcomeEffects = Set.singleton (atom ("effect:" <> suffix))
  , callableOutcomeDischargedFacts = Set.singleton (atom ("fact:" <> suffix))
  }

successOutcome, negativeOutcome, fatalOutcome :: CallableOutcomeContract
successOutcome = outcome successClass "branch.success" PreserveCallee "success"
negativeOutcome = outcome negativeClass "branch.negative" PreserveCallee "negative"
fatalOutcome = outcome fatalClass "branch.fatal" PreserveCallee "fatal"

accountWith
  :: Set.Set CallableFailure
  -> [CallableOutcomeContract]
  -> SurfaceCallableInvocationSemanticAccount
accountWith failures outcomes = SurfaceCallableInvocationSemanticAccount
  { surfaceSemanticInvocationSpan = invocationSpan
  , surfaceSemanticInvocationDisplayName = "Branch"
  , surfaceSemanticInvocationDeclarationKey = branchKey
  , surfaceSemanticInvocationCallerAuthority = Set.empty
  , surfaceSemanticInvocationPublicEffectBound = Set.empty
  , surfaceSemanticInvocationCalleeTransition = PreserveCallee
  , surfaceSemanticInvocationModeledFailures = failures
  , surfaceSemanticInvocationOutcomes = outcomes
  }

branchAccount :: SurfaceCallableInvocationSemanticAccount
branchAccount = accountWith (Set.singleton negativeFailure)
  [successOutcome, negativeOutcome]

summaryWith
  :: SurfaceCallableInvocationSemanticAccount
  -> Set.Set CallableFailure
  -> SurfaceCallableSemanticSummary
summaryWith account failures = SurfaceCallableSemanticSummary
  { surfaceCallableSemanticAccounts = [account]
  , surfaceReachableCallableEffects = Set.empty
  , surfaceRequiredCallerAuthority = Set.empty
  , surfaceReachableCallableFailures = failures
  }

branchSummary :: SurfaceCallableSemanticSummary
branchSummary = summaryWith branchAccount (Set.singleton negativeFailure)

callerSurface :: Set.Set CallableFailure -> CallableRefinementSurface
callerSurface failures = CallableRefinementSurface
  { callableRefinementMachineShape = CallableMachineShape "Caller"
  , callableRefinementContract = CallableContract
      { callableContractInterfaceRevision = InterfaceRevision "caller.v1"
      , callableContractCalleeTransition = PreserveCallee
      , callableContractEffectBound = Set.empty
      }
  , callableRefinementCallerAuthority = Set.empty
  , callableRefinementFailures = failures
  }

callerContextWith :: Set.Set CallableFailure -> SurfaceCallableCallerContext
callerContextWith failures = SurfaceCallableCallerContext
  { surfaceCallerAvailableAuthority = Set.empty
  , surfaceCallerPublicContract = callerSurface failures
  }

branchContext :: SurfaceCallableCallerContext
branchContext = callerContextWith (Set.singleton negativeFailure)

witness
  :: SourceSpan
  -> Text
  -> SurfaceCallableOutcomeControl
  -> CallableOutcomeContract
  -> SurfaceCallableOutcomeArmSemanticWitness
witness armSpan label control contract = SurfaceCallableOutcomeArmSemanticWitness
  { surfaceOutcomeArmInvocationSpan = invocationSpan
  , surfaceOutcomeArmSpan = armSpan
  , surfaceOutcomeArmDeclarationKey = branchKey
  , surfaceOutcomeArmSourceLabel = label
  , surfaceOutcomeArmPayload = []
  , surfaceOutcomeArmControl = control
  , surfaceOutcomeArmContract = contract
  }

successWitness, negativeWitness, fatalWitness :: SurfaceCallableOutcomeArmSemanticWitness
successWitness = witness successArmSpan "ok" SurfaceCallableOutcomeContinues successOutcome
negativeWitness = witness negativeArmSpan "negative" SurfaceCallableOutcomeContinues negativeOutcome
fatalWitness = witness fatalArmSpan "fatal" SurfaceCallableOutcomeFatalTerminal fatalOutcome

legacyStillRejects :: Either String ()
legacyStillRejects =
  case checkSurfaceCallableInvocationSummary branchContext branchSummary of
    Left (SurfaceInvocationOutcomeShapeUnsupported actualSpan classes)
      | actualSpan == invocationSpan
          && classes == [successClass, negativeClass] -> Right ()
    Left other -> Left ("wrong legacy rejection: " <> show other)
    Right checked -> Left ("legacy context unexpectedly accepted branches: " <> show checked)

exactWitnessesAccept :: Either String ()
exactWitnessesAccept = do
  checked <- mapLeft show $
    checkSurfaceCallableInvocationSummaryWithOutcomeBranches
      [negativeWitness, successWitness]
      branchContext
      branchSummary
  assert
    (checkedInvocationSemanticSummary checked == branchSummary)
    "accepted branch-aware context changed semantic summary"

missingWitnessesReject :: Either String ()
missingWitnessesReject =
  expectError
    (\err -> case err of
      SurfaceInvocationOutcomeWitnessMissing actualSpan key ->
        actualSpan == invocationSpan && key == branchKey
      _ -> False)
    []
    branchContext
    branchSummary
    "missing branch witness"

partialWitnessDomainRejects :: Either String ()
partialWitnessDomainRejects =
  expectError
    (\err -> case err of
      SurfaceInvocationOutcomeWitnessDomainMismatch actualSpan expected actual ->
        actualSpan == invocationSpan
          && expected == Set.fromList [successClass, negativeClass]
          && actual == Set.singleton successClass
      _ -> False)
    [successWitness]
    branchContext
    branchSummary
    "partial witness domain"

contractSubstitutionRejects :: Either String ()
contractSubstitutionRejects =
  let substitutedContract = negativeOutcome
        { callableOutcomePostconditions = Set.singleton (atom "post:substituted") }
      substitutedWitness = negativeWitness
        { surfaceOutcomeArmContract = substitutedContract }
  in expectError
      (\err -> case err of
        SurfaceInvocationOutcomeWitnessContractMismatch actualSpan outcomeClass ->
          actualSpan == invocationSpan && outcomeClass == negativeClass
        _ -> False)
      [successWitness, substitutedWitness]
      branchContext
      branchSummary
      "contract substitution"

duplicateWitnessRejects :: Either String ()
duplicateWitnessRejects =
  expectError
    (\err -> case err of
      SurfaceInvocationOutcomeWitnessDuplicateClass actualSpan outcomeClass ->
        actualSpan == invocationSpan && outcomeClass == successClass
      _ -> False)
    [successWitness, successWitness, negativeWitness]
    branchContext
    branchSummary
    "duplicate witness"

controlSubstitutionRejects :: Either String ()
controlSubstitutionRejects =
  let substitutedWitness = negativeWitness
        { surfaceOutcomeArmControl = SurfaceCallableOutcomeDeclaredTerminal }
  in expectError
      (\err -> case err of
        SurfaceInvocationOutcomeWitnessControlMismatch actualSpan outcomeClass ->
          actualSpan == invocationSpan && outcomeClass == negativeClass
        _ -> False)
      [successWitness, substitutedWitness]
      branchContext
      branchSummary
      "control substitution"

unownedWitnessRejects :: Either String ()
unownedWitnessRejects =
  let foreignWitness = negativeWitness
        { surfaceOutcomeArmDeclarationKey = otherKey }
  in expectError
      (\err -> case err of
        SurfaceInvocationOutcomeWitnessUnowned actualSpan key ->
          actualSpan == invocationSpan && key == otherKey
        _ -> False)
      [successWitness, negativeWitness, foreignWitness]
      branchContext
      branchSummary
      "unowned witness"

branchTransitionMismatchRejects :: Either String ()
branchTransitionMismatchRejects =
  let consumingNegative = negativeOutcome
        { callableOutcomeCalleeTransition = ConsumeCallee }
      consumingAccount = accountWith (Set.singleton negativeFailure)
        [successOutcome, consumingNegative]
      consumingSummary = summaryWith consumingAccount (Set.singleton negativeFailure)
      consumingWitness = negativeWitness
        { surfaceOutcomeArmContract = consumingNegative }
  in expectError
      (\err -> case err of
        SurfaceInvocationOutcomeTransitionMismatch actualSpan PreserveCallee ConsumeCallee ->
          actualSpan == invocationSpan
        _ -> False)
      [successWitness, consumingWitness]
      branchContext
      consumingSummary
      "branch transition mismatch"

fatalWitnessRejects :: Either String ()
fatalWitnessRejects =
  let fatalAccount = accountWith (Set.singleton fatalFailure)
        [successOutcome, fatalOutcome]
      fatalSummary = summaryWith fatalAccount (Set.singleton fatalFailure)
      fatalContext = callerContextWith (Set.singleton fatalFailure)
  in expectError
      (\err -> case err of
        SurfaceInvocationOutcomeWitnessControlMismatch actualSpan outcomeClass ->
          actualSpan == invocationSpan && outcomeClass == fatalClass
        _ -> False)
      [successWitness, fatalWitness]
      fatalContext
      fatalSummary
      "fatal witness"

expectError
  :: (SurfaceCallableInvocationContextError -> Bool)
  -> [SurfaceCallableOutcomeArmSemanticWitness]
  -> SurfaceCallableCallerContext
  -> SurfaceCallableSemanticSummary
  -> String
  -> Either String ()
expectError predicate witnesses context summary label =
  case checkSurfaceCallableInvocationSummaryWithOutcomeBranches witnesses context summary of
    Left err | predicate err -> Right ()
    Left err -> Left ("unexpected " <> label <> " error: " <> show err)
    Right checked -> Left ("expected " <> label <> " rejection, got " <> show checked)

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
