{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Compiler.CallableInvocationContext
  ( CheckedSurfaceCallableInvocationContext (..)
  , SurfaceCallableCallerContext (..)
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
import Phil.Compiler.CallableOutcomeContinuation
  ( SurfaceCallableOutcomeContinuation (..)
  , SurfaceCallableOutcomeContinuationDisposition (..)
  , SurfaceCallableOutcomeContinuationError (..)
  , composeSurfaceCallableOutcomeContinuations
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
    [ test "CALL-019 branch-aware admission exposes exact outcome continuation state"
        exactContinuationState
    , test "CALL-019 outcome continuation order follows source arm order"
        sourceOrderPreserved
    , test "CALL-019 declared-terminal outcome does not become caller continuation"
        declaredTerminalDisposition
    , test "CALL-019 continuation semantic buckets remain distinct"
        semanticBucketsRemainDistinct
    , test "CALL-019 legacy scalar context exposes no invented branch continuation"
        legacyScalarHasNoBranchContinuation
    , test "CALL-019 continuation composer rejects fatal control"
        fatalContinuationRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

branchKey :: DeclarationKey
branchKey = DeclarationKey "decl.branch"

invocationSpan, successSpan, negativeSpan, terminalSpan, fatalSpan :: SourceSpan
invocationSpan = spanAt 1 10
successSpan = spanAt 20 29
negativeSpan = spanAt 30 41
terminalSpan = spanAt 42 51
fatalSpan = spanAt 52 60

spanAt :: Int -> Int -> SourceSpan
spanAt start end = SourceSpan
  (SourcePoint "call019-continuation-state" 1 start (start - 1))
  (SourcePoint "call019-continuation-state" 1 end (end - 1))

negativeFailure, terminalFailure, fatalFailure :: CallableFailure
negativeFailure = CallableTypedNegative (Outcome "negative")
terminalFailure = CallableDeclaredTerminal (Outcome "closed")
fatalFailure = CallableFatal "fatal:branch"

successClass, negativeClass, terminalClass, fatalClass :: CallableOutcomeClass
successClass = CallableSuccessOutcome
negativeClass = CallableNonSuccessOutcome negativeFailure
terminalClass = CallableNonSuccessOutcome terminalFailure
fatalClass = CallableNonSuccessOutcome fatalFailure

atom :: Text -> CallableOutcomeAtom
atom = CallableOutcomeAtom

outcome
  :: CallableOutcomeClass
  -> Text
  -> Text
  -> CallableOutcomeContract
outcome outcomeClass state suffix = CallableOutcomeContract
  { callableOutcomeClass = outcomeClass
  , callableOutcomeState = CallableOutcomeState state
  , callableOutcomeCalleeTransition = PreserveCallee
  , callableOutcomePostconditions = Set.singleton (atom ("post:" <> suffix))
  , callableOutcomeResidualObligations = Set.singleton (atom ("residual:" <> suffix))
  , callableOutcomeAssumptions = Set.singleton (atom ("assume:" <> suffix))
  , callableOutcomeEffects = Set.singleton (atom ("effect:" <> suffix))
  , callableOutcomeDischargedFacts = Set.singleton (atom ("fact:" <> suffix))
  }

successOutcome, negativeOutcome, terminalOutcome, fatalOutcome :: CallableOutcomeContract
successOutcome = outcome successClass "branch.success" "success"
negativeOutcome = outcome negativeClass "branch.negative" "negative"
terminalOutcome = outcome terminalClass "branch.closed" "closed"
fatalOutcome = outcome fatalClass "branch.fatal" "fatal"

branchAccount :: SurfaceCallableInvocationSemanticAccount
branchAccount = SurfaceCallableInvocationSemanticAccount
  { surfaceSemanticInvocationSpan = invocationSpan
  , surfaceSemanticInvocationDisplayName = "Branch"
  , surfaceSemanticInvocationDeclarationKey = branchKey
  , surfaceSemanticInvocationCallerAuthority = Set.empty
  , surfaceSemanticInvocationPublicEffectBound = Set.empty
  , surfaceSemanticInvocationCalleeTransition = PreserveCallee
  , surfaceSemanticInvocationModeledFailures =
      Set.fromList [negativeFailure, terminalFailure]
  , surfaceSemanticInvocationOutcomes =
      [successOutcome, negativeOutcome, terminalOutcome]
  }

branchSummary :: SurfaceCallableSemanticSummary
branchSummary = SurfaceCallableSemanticSummary
  { surfaceCallableSemanticAccounts = [branchAccount]
  , surfaceReachableCallableEffects = Set.empty
  , surfaceRequiredCallerAuthority = Set.empty
  , surfaceReachableCallableFailures = Set.fromList [negativeFailure, terminalFailure]
  }

callerContext :: SurfaceCallableCallerContext
callerContext = SurfaceCallableCallerContext
  { surfaceCallerAvailableAuthority = Set.empty
  , surfaceCallerPublicContract = CallableRefinementSurface
      { callableRefinementMachineShape = CallableMachineShape "Caller"
      , callableRefinementContract = CallableContract
          { callableContractInterfaceRevision = InterfaceRevision "caller.v1"
          , callableContractCalleeTransition = PreserveCallee
          , callableContractEffectBound = Set.empty
          }
      , callableRefinementCallerAuthority = Set.empty
      , callableRefinementFailures = Set.fromList [negativeFailure, terminalFailure]
      }
  }

witness
  :: SourceSpan
  -> Text
  -> [(Mode, Ty)]
  -> SurfaceCallableOutcomeControl
  -> CallableOutcomeContract
  -> SurfaceCallableOutcomeArmSemanticWitness
witness armSpan label payload control contract = SurfaceCallableOutcomeArmSemanticWitness
  { surfaceOutcomeArmInvocationSpan = invocationSpan
  , surfaceOutcomeArmSpan = armSpan
  , surfaceOutcomeArmDeclarationKey = branchKey
  , surfaceOutcomeArmSourceLabel = label
  , surfaceOutcomeArmPayload = payload
  , surfaceOutcomeArmControl = control
  , surfaceOutcomeArmContract = contract
  }

successWitness, negativeWitness, terminalWitness, fatalWitness
  :: SurfaceCallableOutcomeArmSemanticWitness
successWitness = witness successSpan "ok" [] SurfaceCallableOutcomeContinues successOutcome
negativeWitness = witness negativeSpan "negative"
  [(Unrestricted, TyOpaque "Reason")]
  SurfaceCallableOutcomeContinues
  negativeOutcome
terminalWitness = witness terminalSpan "closed" []
  SurfaceCallableOutcomeDeclaredTerminal
  terminalOutcome
fatalWitness = witness fatalSpan "fatal" [] SurfaceCallableOutcomeFatalTerminal fatalOutcome

sourceOrderedWitnesses :: [SurfaceCallableOutcomeArmSemanticWitness]
sourceOrderedWitnesses = [negativeWitness, terminalWitness, successWitness]

checkedBranchContext :: Either String CheckedSurfaceCallableInvocationContext
checkedBranchContext = mapLeft show $
  checkSurfaceCallableInvocationSummaryWithOutcomeBranches
    sourceOrderedWitnesses
    callerContext
    branchSummary

exactContinuationState :: Either String ()
exactContinuationState = do
  checked <- checkedBranchContext
  let continuations = checkedInvocationOutcomeContinuations checked
  case continuations of
    [negativeContinuation, terminalContinuation, successContinuation] -> do
      assertContinuation negativeContinuation negativeWitness negativeOutcome
      assertContinuation terminalContinuation terminalWitness terminalOutcome
      assertContinuation successContinuation successWitness successOutcome
    other -> Left ("unexpected continuation count: " <> show (length other))

sourceOrderPreserved :: Either String ()
sourceOrderPreserved = do
  checked <- checkedBranchContext
  assert
    (map surfaceContinuationSourceLabel
      (checkedInvocationOutcomeContinuations checked)
      == ["negative", "closed", "ok"])
    "outcome continuation order no longer follows source arm order"

declaredTerminalDisposition :: Either String ()
declaredTerminalDisposition = do
  checked <- checkedBranchContext
  let terminal = filter
        ((== "closed") . surfaceContinuationSourceLabel)
        (checkedInvocationOutcomeContinuations checked)
  case terminal of
    [continuation] -> assert
      (surfaceContinuationDisposition continuation
        == SurfaceCallableOutcomeCallerTerminates (Outcome "closed"))
      "declared-terminal branch acquired an ordinary caller continuation"
    other -> Left ("expected one terminal continuation account, got " <> show (length other))

semanticBucketsRemainDistinct :: Either String ()
semanticBucketsRemainDistinct = do
  checked <- checkedBranchContext
  let negative = filter
        ((== "negative") . surfaceContinuationSourceLabel)
        (checkedInvocationOutcomeContinuations checked)
  case negative of
    [continuation] -> do
      assert
        (surfaceContinuationPostconditions continuation
          == Set.singleton (atom "post:negative"))
        "postconditions changed during continuation composition"
      assert
        (surfaceContinuationResidualObligations continuation
          == Set.singleton (atom "residual:negative"))
        "residual obligations changed during continuation composition"
      assert
        (surfaceContinuationAssumptions continuation
          == Set.singleton (atom "assume:negative"))
        "assumptions changed during continuation composition"
      assert
        (surfaceContinuationEffects continuation
          == Set.singleton (atom "effect:negative"))
        "effects changed during continuation composition"
      assert
        (surfaceContinuationDischargedFacts continuation
          == Set.singleton (atom "fact:negative"))
        "discharged facts changed during continuation composition"
    other -> Left ("expected one negative continuation, got " <> show (length other))

legacyScalarHasNoBranchContinuation :: Either String ()
legacyScalarHasNoBranchContinuation = do
  let scalarAccount = branchAccount
        { surfaceSemanticInvocationModeledFailures = Set.empty
        , surfaceSemanticInvocationOutcomes = [successOutcome]
        }
      scalarSummary = branchSummary
        { surfaceCallableSemanticAccounts = [scalarAccount]
        , surfaceReachableCallableFailures = Set.empty
        }
      scalarContext = callerContext
        { surfaceCallerPublicContract =
            (surfaceCallerPublicContract callerContext)
              { callableRefinementFailures = Set.empty }
        }
  checked <- mapLeft show $
    checkSurfaceCallableInvocationSummary scalarContext scalarSummary
  assert
    (null (checkedInvocationOutcomeContinuations checked))
    "legacy scalar invocation invented branch continuation state"

fatalContinuationRejects :: Either String ()
fatalContinuationRejects =
  case composeSurfaceCallableOutcomeContinuations [fatalWitness] of
    Left (SurfaceCallableOutcomeContinuationFatalUnsupported actualSpan outcomeClass)
      | actualSpan == fatalSpan && outcomeClass == fatalClass -> Right ()
    Left other -> Left ("wrong fatal continuation rejection: " <> show other)
    Right continuations -> Left ("fatal continuation unexpectedly composed: " <> show continuations)

assertContinuation
  :: SurfaceCallableOutcomeContinuation
  -> SurfaceCallableOutcomeArmSemanticWitness
  -> CallableOutcomeContract
  -> Either String ()
assertContinuation continuation expectedWitness expectedContract = do
  assert
    (surfaceContinuationInvocationSpan continuation
      == surfaceOutcomeArmInvocationSpan expectedWitness)
    "invocation span changed during continuation composition"
  assert
    (surfaceContinuationArmSpan continuation == surfaceOutcomeArmSpan expectedWitness)
    "arm span changed during continuation composition"
  assert
    (surfaceContinuationDeclarationKey continuation
      == surfaceOutcomeArmDeclarationKey expectedWitness)
    "declaration identity changed during continuation composition"
  assert
    (surfaceContinuationPayload continuation == surfaceOutcomeArmPayload expectedWitness)
    "payload telescope changed during continuation composition"
  assert
    (surfaceContinuationState continuation == callableOutcomeState expectedContract)
    "outcome state changed during continuation composition"
  assert
    (surfaceContinuationCalleeTransition continuation
      == callableOutcomeCalleeTransition expectedContract)
    "callee transition changed during continuation composition"
  assert
    (surfaceContinuationContract continuation == expectedContract)
    "complete contract changed during continuation composition"

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
