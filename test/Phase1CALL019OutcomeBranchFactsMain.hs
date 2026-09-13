{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Compiler.CallableOutcomeBranchFacts
  ( SurfaceCallableOutcomeBranchFactEnvironment (..)
  , SurfaceCallableOutcomeBranchFactError (..)
  , SurfaceCallableOutcomeFactBinding (..)
  , bindSurfaceCallableOutcomeBranchFacts
  )
import Phil.Compiler.CallableOutcomeContinuation
  ( SurfaceCallableOutcomeContinuation (..)
  , SurfaceCallableOutcomeContinuationDisposition (..)
  )
import Phil.Core.Callable
  ( CalleeTransition (..)
  )
import Phil.Core.CallableOutcome
  ( CallableOutcomeAtom (..)
  , CallableOutcomeClass (..)
  , CallableOutcomeContract (..)
  , CallableOutcomeState (..)
  )
import Phil.Core.CallableRefinement
  ( CallableFailure (..)
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  )
import Phil.Core.Syntax
  ( Outcome (..)
  , Proposition (..)
  )
import Phil.Surface.Syntax
  ( SourcePoint (..)
  , SourceSpan (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CALL-019 explicit fact bindings preserve branch-local buckets"
        exactBranchFacts
    , test "CALL-019 sibling outcome facts do not leak across branch environments"
        siblingFactsRemainSeparate
    , test "CALL-019 residual obligations and effects cannot masquerade as proof facts"
        residualAndEffectsRejectAsExtra
    , test "CALL-019 missing usable fact binding rejects fail-closed"
        missingFactRejects
    , test "CALL-019 semantic atom key substitution rejects"
        keySubstitutionRejects
    , test "CALL-019 evidence names must be unambiguous within one branch"
        evidenceNameCollisionRejects
    , test "CALL-019 declared-terminal outcome exposes no caller proof environment"
        terminalFactsStayUnavailable
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

branchKey :: DeclarationKey
branchKey = DeclarationKey "decl.branch"

invocationSpan, successSpan, negativeSpan, terminalSpan :: SourceSpan
invocationSpan = spanAt 1 10
successSpan = spanAt 20 29
negativeSpan = spanAt 30 41
terminalSpan = spanAt 42 52

spanAt :: Int -> Int -> SourceSpan
spanAt start end = SourceSpan
  (SourcePoint "call019-branch-facts" 1 start (start - 1))
  (SourcePoint "call019-branch-facts" 1 end (end - 1))

atom :: Text -> CallableOutcomeAtom
atom = CallableOutcomeAtom

successPost, successAssume, successFact, successResidual, successEffect :: CallableOutcomeAtom
successPost = atom "semantic.success.post"
successAssume = atom "semantic.success.assume"
successFact = atom "semantic.success.fact"
successResidual = atom "semantic.success.residual"
successEffect = atom "semantic.success.effect"

negativePost, negativeAssume, negativeFact :: CallableOutcomeAtom
negativePost = atom "semantic.negative.post"
negativeAssume = atom "semantic.negative.assume"
negativeFact = atom "semantic.negative.fact"

terminalPost :: CallableOutcomeAtom
terminalPost = atom "semantic.closed.post"

negativeFailure, terminalFailure :: CallableFailure
negativeFailure = CallableTypedNegative (Outcome "negative")
terminalFailure = CallableDeclaredTerminal (Outcome "closed")

successClass, negativeClass, terminalClass :: CallableOutcomeClass
successClass = CallableSuccessOutcome
negativeClass = CallableNonSuccessOutcome negativeFailure
terminalClass = CallableNonSuccessOutcome terminalFailure

contract
  :: CallableOutcomeClass
  -> Text
  -> Set.Set CallableOutcomeAtom
  -> Set.Set CallableOutcomeAtom
  -> Set.Set CallableOutcomeAtom
  -> Set.Set CallableOutcomeAtom
  -> Set.Set CallableOutcomeAtom
  -> CallableOutcomeContract
contract outcomeClass state posts residual assumptions effects facts =
  CallableOutcomeContract
    { callableOutcomeClass = outcomeClass
    , callableOutcomeState = CallableOutcomeState state
    , callableOutcomeCalleeTransition = PreserveCallee
    , callableOutcomePostconditions = posts
    , callableOutcomeResidualObligations = residual
    , callableOutcomeAssumptions = assumptions
    , callableOutcomeEffects = effects
    , callableOutcomeDischargedFacts = facts
    }

successContract, negativeContract, terminalContract :: CallableOutcomeContract
successContract = contract successClass "success"
  (Set.singleton successPost)
  (Set.singleton successResidual)
  (Set.singleton successAssume)
  (Set.singleton successEffect)
  (Set.singleton successFact)
negativeContract = contract negativeClass "negative"
  (Set.singleton negativePost)
  Set.empty
  (Set.singleton negativeAssume)
  Set.empty
  (Set.singleton negativeFact)
terminalContract = contract terminalClass "closed"
  (Set.singleton terminalPost)
  Set.empty
  Set.empty
  Set.empty
  Set.empty

continuation
  :: SourceSpan
  -> Text
  -> CallableOutcomeClass
  -> SurfaceCallableOutcomeContinuationDisposition
  -> CallableOutcomeContract
  -> SurfaceCallableOutcomeContinuation
continuation armSpan label outcomeClass disposition outcomeContract =
  SurfaceCallableOutcomeContinuation
    { surfaceContinuationInvocationSpan = invocationSpan
    , surfaceContinuationArmSpan = armSpan
    , surfaceContinuationDeclarationKey = branchKey
    , surfaceContinuationSourceLabel = label
    , surfaceContinuationPayload = []
    , surfaceContinuationOutcomeClass = outcomeClass
    , surfaceContinuationDisposition = disposition
    , surfaceContinuationState = callableOutcomeState outcomeContract
    , surfaceContinuationCalleeTransition = callableOutcomeCalleeTransition outcomeContract
    , surfaceContinuationPostconditions = callableOutcomePostconditions outcomeContract
    , surfaceContinuationResidualObligations = callableOutcomeResidualObligations outcomeContract
    , surfaceContinuationAssumptions = callableOutcomeAssumptions outcomeContract
    , surfaceContinuationEffects = callableOutcomeEffects outcomeContract
    , surfaceContinuationDischargedFacts = callableOutcomeDischargedFacts outcomeContract
    , surfaceContinuationContract = outcomeContract
    }

successContinuation, negativeContinuation, terminalContinuation
  :: SurfaceCallableOutcomeContinuation
successContinuation = continuation successSpan "ok" successClass
  SurfaceCallableOutcomeCallerContinues successContract
negativeContinuation = continuation negativeSpan "negative" negativeClass
  SurfaceCallableOutcomeCallerContinues negativeContract
terminalContinuation = continuation terminalSpan "closed" terminalClass
  (SurfaceCallableOutcomeCallerTerminates (Outcome "closed")) terminalContract

continuations :: [SurfaceCallableOutcomeContinuation]
continuations = [negativeContinuation, terminalContinuation, successContinuation]

binding :: CallableOutcomeAtom -> Text -> Text -> SurfaceCallableOutcomeFactBinding
binding semanticAtom evidenceName propositionName = SurfaceCallableOutcomeFactBinding
  { surfaceOutcomeFactAtom = semanticAtom
  , surfaceOutcomeFactEvidenceName = evidenceName
  , surfaceOutcomeFactProposition = Atom propositionName []
  }

exactBindings :: Map.Map CallableOutcomeAtom SurfaceCallableOutcomeFactBinding
exactBindings = Map.fromList
  [ (successPost, binding successPost "success_post" "SuccessPost")
  , (successAssume, binding successAssume "success_assume" "SuccessAssume")
  , (successFact, binding successFact "success_fact" "SuccessFact")
  , (negativePost, binding negativePost "negative_post" "NegativePost")
  , (negativeAssume, binding negativeAssume "negative_assume" "NegativeAssume")
  , (negativeFact, binding negativeFact "negative_fact" "NegativeFact")
  ]

exactBranchFacts :: Either String ()
exactBranchFacts = do
  environments <- mapLeft show
    (bindSurfaceCallableOutcomeBranchFacts exactBindings continuations)
  case environments of
    [negativeEnvironment, terminalEnvironment, successEnvironment] -> do
      assert
        (surfaceBranchFactSourceLabel negativeEnvironment == "negative"
          && surfaceBranchFactSourceLabel terminalEnvironment == "closed"
          && surfaceBranchFactSourceLabel successEnvironment == "ok")
        "source branch order changed"
      assertBucket negativeEnvironment negativePost negativeAssume negativeFact
      assertBucket successEnvironment successPost successAssume successFact
      assert
        (surfaceBranchFactContinuation negativeEnvironment == negativeContinuation
          && surfaceBranchFactContinuation successEnvironment == successContinuation)
        "complete continuation changed while binding facts"
    other -> Left ("unexpected branch fact environment count: " <> show (length other))

siblingFactsRemainSeparate :: Either String ()
siblingFactsRemainSeparate = do
  environments <- mapLeft show
    (bindSurfaceCallableOutcomeBranchFacts exactBindings continuations)
  let byLabel label = filter ((== label) . surfaceBranchFactSourceLabel) environments
  case (byLabel "negative", byLabel "ok") of
    ([negativeEnvironment], [successEnvironment]) -> do
      assert
        (all ((/= successPost) . surfaceOutcomeFactAtom)
          (allUsable negativeEnvironment))
        "success fact leaked into negative branch"
      assert
        (all ((/= negativePost) . surfaceOutcomeFactAtom)
          (allUsable successEnvironment))
        "negative fact leaked into success branch"
    _ -> Left "could not locate exact sibling branch environments"

residualAndEffectsRejectAsExtra :: Either String ()
residualAndEffectsRejectAsExtra = do
  let withResidual = Map.insert successResidual
        (binding successResidual "residual" "Residual") exactBindings
  case bindSurfaceCallableOutcomeBranchFacts withResidual continuations of
    Left (SurfaceCallableOutcomeFactBindingDomainMismatch expected actual)
      | Set.notMember successResidual expected
          && Set.member successResidual actual -> Right ()
    Left other -> Left ("wrong residual/effect rejection: " <> show other)
    Right environments -> Left ("residual obligation became usable fact: " <> show environments)

missingFactRejects :: Either String ()
missingFactRejects = do
  let missing = Map.delete negativeFact exactBindings
  case bindSurfaceCallableOutcomeBranchFacts missing continuations of
    Left (SurfaceCallableOutcomeFactBindingDomainMismatch expected actual)
      | Set.member negativeFact expected
          && Set.notMember negativeFact actual -> Right ()
    Left other -> Left ("wrong missing-fact rejection: " <> show other)
    Right environments -> Left ("missing fact binding accepted: " <> show environments)

keySubstitutionRejects :: Either String ()
keySubstitutionRejects = do
  let substituted = Map.insert successPost
        (binding negativePost "substituted" "Substituted") exactBindings
  case bindSurfaceCallableOutcomeBranchFacts substituted continuations of
    Left (SurfaceCallableOutcomeFactBindingKeyMismatch expected actual)
      | expected == successPost && actual == negativePost -> Right ()
    Left other -> Left ("wrong key-substitution rejection: " <> show other)
    Right environments -> Left ("semantic atom substitution accepted: " <> show environments)

evidenceNameCollisionRejects :: Either String ()
evidenceNameCollisionRejects = do
  let collided = Map.insert successAssume
        (binding successAssume "success_post" "SuccessAssume") exactBindings
  case bindSurfaceCallableOutcomeBranchFacts collided continuations of
    Left (SurfaceCallableOutcomeFactEvidenceNameCollision actualSpan name atoms)
      | actualSpan == successSpan
          && name == "success_post"
          && atoms == Set.fromList [successPost, successAssume] -> Right ()
    Left other -> Left ("wrong evidence-name collision rejection: " <> show other)
    Right environments -> Left ("ambiguous evidence names accepted: " <> show environments)

terminalFactsStayUnavailable :: Either String ()
terminalFactsStayUnavailable = do
  environments <- mapLeft show
    (bindSurfaceCallableOutcomeBranchFacts exactBindings continuations)
  case filter ((== "closed") . surfaceBranchFactSourceLabel) environments of
    [terminalEnvironment] -> do
      assert (null (allUsable terminalEnvironment))
        "terminal branch acquired usable caller proof facts"
      assert
        (surfaceBranchFactDisposition terminalEnvironment
          == SurfaceCallableOutcomeCallerTerminates (Outcome "closed"))
        "terminal branch disposition changed"
      let withTerminal = Map.insert terminalPost
            (binding terminalPost "closed_post" "ClosedPost") exactBindings
      case bindSurfaceCallableOutcomeBranchFacts withTerminal continuations of
        Left (SurfaceCallableOutcomeFactBindingDomainMismatch expected actual)
          | Set.notMember terminalPost expected
              && Set.member terminalPost actual -> Right ()
        Left other -> Left ("wrong terminal-extra rejection: " <> show other)
        Right accepted -> Left ("terminal-only fact became caller-visible: " <> show accepted)
    other -> Left ("expected one terminal environment, got " <> show (length other))

assertBucket
  :: SurfaceCallableOutcomeBranchFactEnvironment
  -> CallableOutcomeAtom
  -> CallableOutcomeAtom
  -> CallableOutcomeAtom
  -> Either String ()
assertBucket environment expectedPost expectedAssume expectedFact = do
  assert
    (map surfaceOutcomeFactAtom (surfaceBranchPostconditions environment)
      == [expectedPost])
    "postcondition bucket changed"
  assert
    (map surfaceOutcomeFactAtom (surfaceBranchAssumptions environment)
      == [expectedAssume])
    "assumption bucket changed"
  assert
    (map surfaceOutcomeFactAtom (surfaceBranchDischargedFacts environment)
      == [expectedFact])
    "discharged-fact bucket changed"

allUsable
  :: SurfaceCallableOutcomeBranchFactEnvironment
  -> [SurfaceCallableOutcomeFactBinding]
allUsable environment =
  surfaceBranchPostconditions environment
    <> surfaceBranchAssumptions environment
    <> surfaceBranchDischargedFacts environment

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
