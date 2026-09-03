{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Core.Callable (CalleeTransition (..))
import Phil.Core.CallableOutcome
import qualified Phil.Core.CallableOutcomeKernelBridge as KernelBridge
import Phil.Core.CallableRefinement (CallableFailure (..))
import Phil.Core.Syntax (Outcome (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "production exact outcome contract preserves maps" exactOutcomeContractPreservesMaps
    , test "production class-domain mismatch preserves diagnostic" classDomainMismatchPreservesDiagnostic
    , test "production state mismatch preserves diagnostic" stateMismatchPreservesDiagnostic
    , test "production transition mismatch preserves diagnostic" transitionMismatchPreservesDiagnostic
    , test "production residual to postcondition preserves diagnostic" residualToPostconditionPreservesDiagnostic
    , test "production residual to assumption preserves diagnostic" residualToAssumptionPreservesDiagnostic
    , test "production residual to effect preserves diagnostic" residualToEffectPreservesDiagnostic
    , test "production residual to discharged fact preserves diagnostic" residualToDischargedPreservesDiagnostic
    , test "production dropped residual preserves diagnostic" droppedResidualPreservesDiagnostic
    , test "production postcondition mismatch preserves diagnostic" postconditionMismatchPreservesDiagnostic
    , test "production assumption mismatch preserves diagnostic" assumptionMismatchPreservesDiagnostic
    , test "production effect mismatch preserves diagnostic" effectMismatchPreservesDiagnostic
    , test "production discharged-fact mismatch preserves diagnostic" dischargedMismatchPreservesDiagnostic
    , test "duplicate expected outcome gate remains native" duplicateExpectedGateRemainsNative
    , test "duplicate actual outcome gate remains native" duplicateActualGateRemainsNative
    , test "bridge preserves class-domain precedence" bridgePreservesClassDomainPrecedence
    , test "bridge preserves state precedence over residual classification" bridgePreservesStatePrecedence
    , test "bridge accepts exact facts" bridgeAcceptsExactFacts
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactOutcomeContractPreservesMaps :: Either String ()
exactOutcomeContractPreservesMaps = do
  checked <- mapLeft show $
    checkCallableOutcomeContract expectedOutcomes (reverse expectedOutcomes)
  let expectedMap = Map.fromList (map pair expectedOutcomes)
      actualMap = Map.fromList (map pair (reverse expectedOutcomes))
  assert
    (checkedCallableExpectedOutcomes checked == expectedMap
      && checkedCallableActualOutcomes checked == actualMap)
    "kernel-bound success changed normalized callable outcome maps"
  where
    pair branch = (callableOutcomeClass branch, branch)

classDomainMismatchPreservesDiagnostic :: Either String ()
classDomainMismatchPreservesDiagnostic =
  let actual = replaceBranch typedNegativeClass
        (\branch -> branch
          { callableOutcomeClass =
              CallableNonSuccessOutcome (CallableDeclaredTerminal notFoundOutcome)
          })
        expectedOutcomes
  in case checkCallableOutcomeContract expectedOutcomes actual of
      Left (CallableOutcomeClassSetMismatch expectedClasses actualClasses) ->
        assert
          (Set.member typedNegativeClass expectedClasses
            && not (Set.member typedNegativeClass actualClasses))
          "class-domain diagnostic changed"
      other -> unexpected other

stateMismatchPreservesDiagnostic :: Either String ()
stateMismatchPreservesDiagnostic =
  let wrongState = CallableOutcomeState "state.wrong"
      actual = replaceBranch typedNegativeClass
        (\branch -> branch { callableOutcomeState = wrongState })
        expectedOutcomes
  in case checkCallableOutcomeContract expectedOutcomes actual of
      Left (CallableOutcomeStateMismatch outcomeClass expected actualState) ->
        assert
          (outcomeClass == typedNegativeClass
            && expected == CallableOutcomeState "state.retryable"
            && actualState == wrongState)
          "state diagnostic changed"
      other -> unexpected other

transitionMismatchPreservesDiagnostic :: Either String ()
transitionMismatchPreservesDiagnostic =
  let actual = replaceBranch typedNegativeClass
        (\branch -> branch { callableOutcomeCalleeTransition = ConsumeCallee })
        expectedOutcomes
  in case checkCallableOutcomeContract expectedOutcomes actual of
      Left (CallableOutcomeCalleeTransitionMismatch outcomeClass expected actualTransition) ->
        assert
          (outcomeClass == typedNegativeClass
            && expected == PreserveCallee
            && actualTransition == ConsumeCallee)
          "callee-transition diagnostic changed"
      other -> unexpected other

residualToPostconditionPreservesDiagnostic :: Either String ()
residualToPostconditionPreservesDiagnostic =
  residualReclassificationPreservesDiagnostic OutcomePostconditionBucket $ \branch ->
    branch
      { callableOutcomeResidualObligations = Set.delete retryObligation
          (callableOutcomeResidualObligations branch)
      , callableOutcomePostconditions = Set.insert retryObligation
          (callableOutcomePostconditions branch)
      }

residualToAssumptionPreservesDiagnostic :: Either String ()
residualToAssumptionPreservesDiagnostic =
  residualReclassificationPreservesDiagnostic OutcomeAssumptionBucket $ \branch ->
    branch
      { callableOutcomeResidualObligations = Set.delete retryObligation
          (callableOutcomeResidualObligations branch)
      , callableOutcomeAssumptions = Set.insert retryObligation
          (callableOutcomeAssumptions branch)
      }

residualToEffectPreservesDiagnostic :: Either String ()
residualToEffectPreservesDiagnostic =
  residualReclassificationPreservesDiagnostic OutcomeEffectBucket $ \branch ->
    branch
      { callableOutcomeResidualObligations = Set.delete retryObligation
          (callableOutcomeResidualObligations branch)
      , callableOutcomeEffects = Set.insert retryObligation
          (callableOutcomeEffects branch)
      }

residualToDischargedPreservesDiagnostic :: Either String ()
residualToDischargedPreservesDiagnostic =
  residualReclassificationPreservesDiagnostic OutcomeDischargedFactBucket $ \branch ->
    branch
      { callableOutcomeResidualObligations = Set.delete retryObligation
          (callableOutcomeResidualObligations branch)
      , callableOutcomeDischargedFacts = Set.insert retryObligation
          (callableOutcomeDischargedFacts branch)
      }

residualReclassificationPreservesDiagnostic
  :: CallableOutcomeBucket
  -> (CallableOutcomeContract -> CallableOutcomeContract)
  -> Either String ()
residualReclassificationPreservesDiagnostic expectedBucket mutate =
  let actual = replaceBranch typedNegativeClass mutate expectedOutcomes
  in case checkCallableOutcomeContract expectedOutcomes actual of
      Left (CallableResidualObligationReclassified outcomeClass obligation bucket) ->
        assert
          (outcomeClass == typedNegativeClass
            && obligation == retryObligation
            && bucket == expectedBucket)
          "residual reclassification diagnostic changed"
      other -> unexpected other

droppedResidualPreservesDiagnostic :: Either String ()
droppedResidualPreservesDiagnostic =
  let actual = replaceBranch typedNegativeClass
        (\branch -> branch { callableOutcomeResidualObligations = Set.empty })
        expectedOutcomes
  in case checkCallableOutcomeContract expectedOutcomes actual of
      Left (CallableResidualObligationMismatch outcomeClass expected actualResidual) ->
        assert
          (outcomeClass == typedNegativeClass
            && expected == Set.singleton retryObligation
            && Set.null actualResidual)
          "residual-mismatch diagnostic changed"
      other -> unexpected other

postconditionMismatchPreservesDiagnostic :: Either String ()
postconditionMismatchPreservesDiagnostic =
  let changed = Set.singleton (atom "post.success.changed")
      actual = replaceBranch successClass
        (\branch -> branch { callableOutcomePostconditions = changed })
        expectedOutcomes
  in case checkCallableOutcomeContract expectedOutcomes actual of
      Left (CallableOutcomePostconditionMismatch outcomeClass expected actualPosts) ->
        assert
          (outcomeClass == successClass
            && expected == Set.singleton (atom "post.success")
            && actualPosts == changed)
          "postcondition diagnostic changed"
      other -> unexpected other

assumptionMismatchPreservesDiagnostic :: Either String ()
assumptionMismatchPreservesDiagnostic =
  let changed = Set.singleton (atom "assumption.changed")
      actual = replaceBranch typedNegativeClass
        (\branch -> branch { callableOutcomeAssumptions = changed })
        expectedOutcomes
  in case checkCallableOutcomeContract expectedOutcomes actual of
      Left (CallableOutcomeAssumptionMismatch outcomeClass expected actualAssumptions) ->
        assert
          (outcomeClass == typedNegativeClass
            && expected == Set.singleton (atom "assumption.catalog-current")
            && actualAssumptions == changed)
          "assumption diagnostic changed"
      other -> unexpected other

effectMismatchPreservesDiagnostic :: Either String ()
effectMismatchPreservesDiagnostic =
  let changed = Set.singleton (atom "effect.changed")
      actual = replaceBranch successClass
        (\branch -> branch { callableOutcomeEffects = changed })
        expectedOutcomes
  in case checkCallableOutcomeContract expectedOutcomes actual of
      Left (CallableOutcomeEffectMismatch outcomeClass expected actualEffects) ->
        assert
          (outcomeClass == successClass
            && expected == Set.singleton (atom "effect.storage.read")
            && actualEffects == changed)
          "effect diagnostic changed"
      other -> unexpected other

dischargedMismatchPreservesDiagnostic :: Either String ()
dischargedMismatchPreservesDiagnostic =
  let changed = Set.singleton (atom "fact.changed")
      actual = replaceBranch successClass
        (\branch -> branch { callableOutcomeDischargedFacts = changed })
        expectedOutcomes
  in case checkCallableOutcomeContract expectedOutcomes actual of
      Left (CallableOutcomeDischargedFactMismatch outcomeClass expected actualFacts) ->
        assert
          (outcomeClass == successClass
            && expected == Set.singleton (atom "fact.request.validated")
            && actualFacts == changed)
          "discharged-fact diagnostic changed"
      other -> unexpected other

duplicateExpectedGateRemainsNative :: Either String ()
duplicateExpectedGateRemainsNative =
  case checkCallableOutcomeContract
      (successBranch : expectedOutcomes) expectedOutcomes of
    Left (DuplicateExpectedCallableOutcome outcomeClass) ->
      assert (outcomeClass == successClass) "duplicate-expected diagnostic changed"
    other -> unexpected other

duplicateActualGateRemainsNative :: Either String ()
duplicateActualGateRemainsNative =
  case checkCallableOutcomeContract
      expectedOutcomes (successBranch : expectedOutcomes) of
    Left (DuplicateActualCallableOutcome outcomeClass) ->
      assert (outcomeClass == successClass) "duplicate-actual diagnostic changed"
    other -> unexpected other

bridgePreservesClassDomainPrecedence :: Either String ()
bridgePreservesClassDomainPrecedence =
  assert
    (KernelBridge.classifyCallableOutcomeFacts
      False False False False False False False False
      (KernelBridge.KernelResidualReclassified
        KernelBridge.KernelOutcomeEffectBucket)
      == KernelBridge.CallableOutcomeClassSetClassification)
    "extracted bridge did not preserve class-domain precedence"

bridgePreservesStatePrecedence :: Either String ()
bridgePreservesStatePrecedence =
  assert
    (KernelBridge.classifyCallableOutcomeFacts
      True False True True True True True True
      (KernelBridge.KernelResidualReclassified
        KernelBridge.KernelOutcomeEffectBucket)
      == KernelBridge.CallableOutcomeStateClassification)
    "extracted bridge did not preserve state precedence"

bridgeAcceptsExactFacts :: Either String ()
bridgeAcceptsExactFacts =
  assert
    (KernelBridge.classifyCallableOutcomeFacts
      True True True True True True True True KernelBridge.KernelResidualExact
      == KernelBridge.CallableOutcomeAcceptedClassification)
    "extracted bridge rejected exact CALL-018 facts"

replaceBranch
  :: CallableOutcomeClass
  -> (CallableOutcomeContract -> CallableOutcomeContract)
  -> [CallableOutcomeContract]
  -> [CallableOutcomeContract]
replaceBranch target mutate = map replaceOne
  where
    replaceOne branch
      | callableOutcomeClass branch == target = mutate branch
      | otherwise = branch

expectedOutcomes :: [CallableOutcomeContract]
expectedOutcomes =
  [ successBranch
  , typedNegativeBranch
  , declaredTerminalBranch
  , fatalBranch
  ]

successClass, typedNegativeClass, declaredTerminalClass, fatalClass :: CallableOutcomeClass
successClass = CallableSuccessOutcome
typedNegativeClass = CallableNonSuccessOutcome (CallableTypedNegative notFoundOutcome)
declaredTerminalClass = CallableNonSuccessOutcome (CallableDeclaredTerminal doneOutcome)
fatalClass = CallableNonSuccessOutcome (CallableFatal "storage.fatal")

successBranch, typedNegativeBranch, declaredTerminalBranch, fatalBranch :: CallableOutcomeContract
successBranch = mkBranch
  successClass "state.ready" PreserveCallee
  ["post.success"] [] [] ["effect.storage.read"] ["fact.request.validated"]
typedNegativeBranch = mkBranch
  typedNegativeClass "state.retryable" PreserveCallee
  ["post.not-found"] ["obligation.retry-budget"] ["assumption.catalog-current"]
  ["effect.storage.read"] ["fact.request.validated"]
declaredTerminalBranch = mkBranch
  declaredTerminalClass "state.closed" ConsumeCallee
  ["post.session-closed"] [] [] ["effect.session.close"] ["fact.close-authorized"]
fatalBranch = mkBranch
  fatalClass "state.failed" ConsumeCallee
  ["post.fatal-recorded"] ["obligation.fatal-audit"] []
  ["effect.diagnostic.emit"] []

mkBranch
  :: CallableOutcomeClass
  -> String
  -> CalleeTransition
  -> [String]
  -> [String]
  -> [String]
  -> [String]
  -> [String]
  -> CallableOutcomeContract
mkBranch outcomeClass state transition postconditions residual assumptions effects discharged =
  CallableOutcomeContract
    { callableOutcomeClass = outcomeClass
    , callableOutcomeState = CallableOutcomeState (fromString state)
    , callableOutcomeCalleeTransition = transition
    , callableOutcomePostconditions = atoms postconditions
    , callableOutcomeResidualObligations = atoms residual
    , callableOutcomeAssumptions = atoms assumptions
    , callableOutcomeEffects = atoms effects
    , callableOutcomeDischargedFacts = atoms discharged
    }

retryObligation :: CallableOutcomeAtom
retryObligation = atom "obligation.retry-budget"

notFoundOutcome, doneOutcome :: Outcome
notFoundOutcome = Outcome "not-found"
doneOutcome = Outcome "done"

atoms :: [String] -> Set.Set CallableOutcomeAtom
atoms = Set.fromList . map atom

atom :: String -> CallableOutcomeAtom
atom = CallableOutcomeAtom . fromString

fromString :: String -> Text.Text
fromString = Text.pack

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

unexpected :: Show a => a -> Either String ()
unexpected value = Left ("unexpected result: " <> show value)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
