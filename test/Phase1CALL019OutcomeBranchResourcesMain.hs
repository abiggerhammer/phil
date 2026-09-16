{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Compiler.CallableOutcomeBranchResources
  ( SurfaceCallableOutcomeBranchResourceEnvironment (..)
  , SurfaceCallableOutcomeBranchResourceError (..)
  , SurfaceCallableOutcomeResourceExpectation (..)
  , SurfaceCallableOutcomeResourceResidueBinding (..)
  , bindSurfaceCallableOutcomeBranchResources
  )
import Phil.Compiler.CallableOutcomeContinuation
  ( SurfaceCallableOutcomeContinuation (..)
  , SurfaceCallableOutcomeContinuationDisposition (..)
  )
import Phil.Core.Callable (CalleeTransition (..))
import Phil.Core.CallableOutcome
  ( CallableOutcomeClass (..)
  , CallableOutcomeContract (..)
  , CallableOutcomeState (..)
  )
import Phil.Core.CallableRefinement (CallableFailure (..))
import Phil.Core.Static (DeclarationKey (..))
import Phil.Core.Syntax
  ( Mode (..)
  , Outcome (..)
  , Ty (..)
  )
import Phil.Surface.Check.Types
  ( BindingMeta (..)
  , SurfaceShape (..)
  )
import Phil.Surface.Syntax
  ( SourcePoint (..)
  , SourceSpan (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CALL-019 binds exact branch-local resource residue"
        exactResourceResidueBinds
    , test "CALL-019 missing resource residue rejects"
        missingResourceResidueRejects
    , test "CALL-019 terminal branch cannot acquire caller resource residue"
        terminalResourceResidueRejects
    , test "CALL-019 resource residue semantic state substitution rejects"
        semanticStateSubstitutionRejects
    , test "CALL-019 resource residue callee transition substitution rejects"
        calleeTransitionSubstitutionRejects
    , test "CALL-019 invocation occurrence participates in resource identity"
        occurrenceSubstitutionRejects
    , test "CALL-019 duplicate resource identity rejects"
        duplicateIdentityRejects
    , test "CALL-019 branch order and result payload remain exact"
        branchOrderAndPayloadRemainExact
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

workerKey :: DeclarationKey
workerKey = DeclarationKey "decl.worker"

successState, retryState, haltState :: CallableOutcomeState
successState = CallableOutcomeState "state.success"
retryState = CallableOutcomeState "state.retry"
haltState = CallableOutcomeState "state.halt"

retryFailure :: CallableFailure
retryFailure = CallableTypedNegative (Outcome "retry")

haltOutcome :: Outcome
haltOutcome = Outcome "halt"

successClass, retryClass, haltClass :: CallableOutcomeClass
successClass = CallableSuccessOutcome
retryClass = CallableNonSuccessOutcome retryFailure
haltClass = CallableNonSuccessOutcome (CallableDeclaredTerminal haltOutcome)

successContract, retryContract, haltContract :: CallableOutcomeContract
successContract = contract successClass successState PreserveCallee
retryContract = contract retryClass retryState PreserveCallee
haltContract = contract haltClass haltState PreserveCallee

contract
  :: CallableOutcomeClass
  -> CallableOutcomeState
  -> CalleeTransition
  -> CallableOutcomeContract
contract outcomeClass outcomeState transition = CallableOutcomeContract
  { callableOutcomeClass = outcomeClass
  , callableOutcomeState = outcomeState
  , callableOutcomeCalleeTransition = transition
  , callableOutcomePostconditions = Set.empty
  , callableOutcomeResidualObligations = Set.empty
  , callableOutcomeAssumptions = Set.empty
  , callableOutcomeEffects = Set.empty
  , callableOutcomeDischargedFacts = Set.empty
  }

invocationSpan, wrongInvocationSpan :: SourceSpan
invocationSpan = spanAt "call019-resource-residue" 1 10
wrongInvocationSpan = spanAt "call019-resource-residue" 9 90

spanAt :: Text -> Int -> Int -> SourceSpan
spanAt file line offset = SourceSpan
  (SourcePoint file line 1 offset)
  (SourcePoint file line 2 (offset + 1))

successContinuation, retryContinuation, haltContinuation
  :: SurfaceCallableOutcomeContinuation
successContinuation = continuation
  invocationSpan
  (spanAt "call019-resource-residue" 2 20)
  "ok"
  [(Linear, TyOpaque "Result")]
  SurfaceCallableOutcomeCallerContinues
  successContract
retryContinuation = continuation
  invocationSpan
  (spanAt "call019-resource-residue" 3 30)
  "retry"
  []
  SurfaceCallableOutcomeCallerContinues
  retryContract
haltContinuation = continuation
  invocationSpan
  (spanAt "call019-resource-residue" 4 40)
  "halt"
  []
  (SurfaceCallableOutcomeCallerTerminates haltOutcome)
  haltContract

continuation
  :: SourceSpan
  -> SourceSpan
  -> Text
  -> [(Mode, Ty)]
  -> SurfaceCallableOutcomeContinuationDisposition
  -> CallableOutcomeContract
  -> SurfaceCallableOutcomeContinuation
continuation callSpan armSpan label payload disposition outcomeContract =
  SurfaceCallableOutcomeContinuation
    { surfaceContinuationInvocationSpan = callSpan
    , surfaceContinuationArmSpan = armSpan
    , surfaceContinuationDeclarationKey = workerKey
    , surfaceContinuationSourceLabel = label
    , surfaceContinuationPayload = payload
    , surfaceContinuationOutcomeClass = callableOutcomeClass outcomeContract
    , surfaceContinuationDisposition = disposition
    , surfaceContinuationState = callableOutcomeState outcomeContract
    , surfaceContinuationCalleeTransition =
        callableOutcomeCalleeTransition outcomeContract
    , surfaceContinuationPostconditions =
        callableOutcomePostconditions outcomeContract
    , surfaceContinuationResidualObligations =
        callableOutcomeResidualObligations outcomeContract
    , surfaceContinuationAssumptions = callableOutcomeAssumptions outcomeContract
    , surfaceContinuationEffects = callableOutcomeEffects outcomeContract
    , surfaceContinuationDischargedFacts =
        callableOutcomeDischargedFacts outcomeContract
    , surfaceContinuationContract = outcomeContract
    }

ownerMeta, successorMeta :: BindingMeta
ownerMeta = BindingMeta Linear (TyOpaque "Owner") PlainShape
successorMeta = BindingMeta Linear (TyOpaque "Successor") PlainShape

successBinding, retryBinding :: SurfaceCallableOutcomeResourceResidueBinding
successBinding = resourceBinding
  invocationSpan
  "ok"
  successState
  PreserveCallee
  (Map.fromList
    [ ("owner", SurfaceCallableResourcePresent ownerMeta)
    , ("old_buffer", SurfaceCallableResourceAbsent)
    , ("result_owner", SurfaceCallableResourcePresent successorMeta)
    ])
  (Just "session")
retryBinding = resourceBinding
  invocationSpan
  "retry"
  retryState
  PreserveCallee
  (Map.fromList
    [ ("owner", SurfaceCallableResourcePresent ownerMeta)
    , ("old_buffer", SurfaceCallableResourceAbsent)
    ])
  Nothing

resourceBinding
  :: SourceSpan
  -> Text
  -> CallableOutcomeState
  -> CalleeTransition
  -> Map.Map Text SurfaceCallableOutcomeResourceExpectation
  -> Maybe Text
  -> SurfaceCallableOutcomeResourceResidueBinding
resourceBinding callSpan label outcomeState transition bindings activeEndpoint =
  SurfaceCallableOutcomeResourceResidueBinding
    { surfaceOutcomeResourceInvocationSpan = callSpan
    , surfaceOutcomeResourceDeclarationKey = workerKey
    , surfaceOutcomeResourceSourceLabel = label
    , surfaceOutcomeResourceState = outcomeState
    , surfaceOutcomeResourceCalleeTransition = transition
    , surfaceOutcomeResourceBindings = bindings
    , surfaceOutcomeResourceActiveEndpoint = activeEndpoint
    }

continuations :: [SurfaceCallableOutcomeContinuation]
continuations = [successContinuation, retryContinuation, haltContinuation]

exactResourceResidueBinds :: Either String ()
exactResourceResidueBinds = do
  environments <- mapLeft show $
    bindSurfaceCallableOutcomeBranchResources
      [successBinding, retryBinding]
      continuations
  case environments of
    [successEnvironment, retryEnvironment, haltEnvironment] -> do
      successResidue <- maybe
        (Left "success branch lost resource residue")
        Right
        (surfaceBranchResourceResidue successEnvironment)
      retryResidue <- maybe
        (Left "retry branch lost resource residue")
        Right
        (surfaceBranchResourceResidue retryEnvironment)
      assert
        (surfaceOutcomeResourceBindings successResidue
          == surfaceOutcomeResourceBindings successBinding)
        "success resource residue changed"
      assert
        (surfaceOutcomeResourceActiveEndpoint retryResidue == Nothing)
        "retry active-endpoint residue changed"
      assert
        (surfaceBranchResourceResidue haltEnvironment == Nothing)
        "terminal branch acquired caller resource residue"
    other -> Left ("unexpected resource environment count: " <> show (length other))

missingResourceResidueRejects :: Either String ()
missingResourceResidueRejects =
  case bindSurfaceCallableOutcomeBranchResources [successBinding] continuations of
    Left (SurfaceCallableOutcomeResourceDomainMismatch expected actual)
      | Set.member (invocationSpan, workerKey, "retry") expected
          && not (Set.member (invocationSpan, workerKey, "retry") actual) -> Right ()
    Left other -> Left ("wrong missing-residue rejection: " <> show other)
    Right accepted -> Left ("missing retry resource residue accepted: " <> show accepted)

terminalResourceResidueRejects :: Either String ()
terminalResourceResidueRejects =
  let terminalBinding = resourceBinding
        invocationSpan
        "halt"
        haltState
        PreserveCallee
        Map.empty
        Nothing
  in case bindSurfaceCallableOutcomeBranchResources
      [successBinding, retryBinding, terminalBinding]
      continuations of
    Left (SurfaceCallableOutcomeResourceDomainMismatch expected actual)
      | not (Set.member (invocationSpan, workerKey, "halt") expected)
          && Set.member (invocationSpan, workerKey, "halt") actual -> Right ()
    Left other -> Left ("wrong terminal-residue rejection: " <> show other)
    Right accepted -> Left ("terminal caller resource residue accepted: " <> show accepted)

semanticStateSubstitutionRejects :: Either String ()
semanticStateSubstitutionRejects =
  let poisoned = successBinding { surfaceOutcomeResourceState = retryState }
  in case bindSurfaceCallableOutcomeBranchResources
      [poisoned, retryBinding]
      continuations of
    Left (SurfaceCallableOutcomeResourceStateMismatch actualSpan actualKey actualLabel expected actual)
      | actualSpan == invocationSpan
          && actualKey == workerKey
          && actualLabel == "ok"
          && expected == successState
          && actual == retryState -> Right ()
    Left other -> Left ("wrong semantic-state rejection: " <> show other)
    Right accepted -> Left ("substituted semantic state accepted: " <> show accepted)

calleeTransitionSubstitutionRejects :: Either String ()
calleeTransitionSubstitutionRejects =
  let poisoned = successBinding
        { surfaceOutcomeResourceCalleeTransition = ConsumeCallee }
  in case bindSurfaceCallableOutcomeBranchResources
      [poisoned, retryBinding]
      continuations of
    Left (SurfaceCallableOutcomeResourceCalleeTransitionMismatch actualSpan actualKey actualLabel expected actual)
      | actualSpan == invocationSpan
          && actualKey == workerKey
          && actualLabel == "ok"
          && expected == PreserveCallee
          && actual == ConsumeCallee -> Right ()
    Left other -> Left ("wrong callee-transition rejection: " <> show other)
    Right accepted -> Left ("substituted callee transition accepted: " <> show accepted)

occurrenceSubstitutionRejects :: Either String ()
occurrenceSubstitutionRejects =
  let poisoned = successBinding
        { surfaceOutcomeResourceInvocationSpan = wrongInvocationSpan }
  in case bindSurfaceCallableOutcomeBranchResources
      [poisoned, retryBinding]
      continuations of
    Left (SurfaceCallableOutcomeResourceDomainMismatch expected actual)
      | Set.member (invocationSpan, workerKey, "ok") expected
          && not (Set.member (invocationSpan, workerKey, "ok") actual)
          && Set.member (wrongInvocationSpan, workerKey, "ok") actual -> Right ()
    Left other -> Left ("wrong occurrence rejection: " <> show other)
    Right accepted -> Left ("wrong-occurrence resource residue accepted: " <> show accepted)

duplicateIdentityRejects :: Either String ()
duplicateIdentityRejects =
  case bindSurfaceCallableOutcomeBranchResources
      [successBinding, successBinding, retryBinding]
      continuations of
    Left (SurfaceCallableOutcomeResourceDuplicateIdentity actualSpan actualKey actualLabel)
      | actualSpan == invocationSpan
          && actualKey == workerKey
          && actualLabel == "ok" -> Right ()
    Left other -> Left ("wrong duplicate-identity rejection: " <> show other)
    Right accepted -> Left ("duplicate resource identity accepted: " <> show accepted)

branchOrderAndPayloadRemainExact :: Either String ()
branchOrderAndPayloadRemainExact = do
  environments <- mapLeft show $
    bindSurfaceCallableOutcomeBranchResources
      [retryBinding, successBinding]
      continuations
  let retained = map surfaceBranchResourceContinuation environments
  assert
    (map surfaceContinuationSourceLabel retained == ["ok", "retry", "halt"])
    "source branch order changed"
  case retained of
    success : _ -> assert
      (surfaceContinuationPayload success == [(Linear, TyOpaque "Result")])
      "success result payload changed"
    [] -> Left "no retained continuations"

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
