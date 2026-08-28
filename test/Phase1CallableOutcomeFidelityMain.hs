{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.Callable (CalleeTransition (..))
import Phil.Core.CallableOutcome
import Phil.Core.CallableRefinement (CallableFailure (..))
import Phil.Core.Syntax (Outcome (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CALL-018 exact outcome contract is enumeration-order independent" exactOutcomeContractAccepts
    , test "CALL-018 outcome class cannot be reclassified" outcomeClassReclassificationRejects
    , test "CALL-018 branch-sensitive state is exact" branchStateMismatchRejects
    , test "CALL-018 callee transition is preserved per outcome" calleeTransitionMismatchRejects
    , test "CALL-018 postcondition is preserved per outcome" postconditionMismatchRejects
    , test "CALL-018 residual obligation cannot become postcondition" residualToPostconditionRejects
    , test "CALL-018 residual obligation cannot become assumption" residualToAssumptionRejects
    , test "CALL-018 residual obligation cannot become effect" residualToEffectRejects
    , test "CALL-018 residual obligation cannot become discharged fact" residualToDischargedFactRejects
    , test "CALL-018 residual obligation cannot silently disappear" droppedResidualRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactOutcomeContractAccepts :: Either String ()
exactOutcomeContractAccepts = do
  checkedForward <- mapLeft show $
    checkCallableOutcomeContract expectedOutcomes expectedOutcomes
  checkedReverse <- mapLeft show $
    checkCallableOutcomeContract expectedOutcomes (reverse expectedOutcomes)
  assert
    (checkedCallableActualOutcomes checkedForward == checkedCallableActualOutcomes checkedReverse)
    "outcome enumeration order changed the checked callable contract"
  assert
    (Map.keysSet (checkedCallableActualOutcomes checkedForward) == expectedClasses)
    "checked callable contract lost an exact outcome class"

outcomeClassReclassificationRejects :: Either String ()
outcomeClassReclassificationRejects =
  let actual = replaceBranch typedNegativeClass
        (\branch -> branch
          { callableOutcomeClass =
              CallableNonSuccessOutcome (CallableDeclaredTerminal notFoundOutcome)
          })
        expectedOutcomes
  in case checkCallableOutcomeContract expectedOutcomes actual of
      Left (CallableOutcomeClassSetMismatch expected actualClasses) -> do
        assert (Set.member typedNegativeClass expected)
          "class mismatch lost expected typed-negative outcome"
        assert (not (Set.member typedNegativeClass actualClasses))
          "typed-negative outcome survived attempted reclassification"
        assert
          (Set.member
            (CallableNonSuccessOutcome (CallableDeclaredTerminal notFoundOutcome))
            actualClasses)
          "class mismatch lost reclassified declared-terminal outcome"
      other -> Left ("outcome class reclassification was accepted: " <> show other)

branchStateMismatchRejects :: Either String ()
branchStateMismatchRejects =
  let actual = replaceBranch typedNegativeClass
        (\branch -> branch { callableOutcomeState = CallableOutcomeState "state.wrong" })
        expectedOutcomes
  in case checkCallableOutcomeContract expectedOutcomes actual of
      Left (CallableOutcomeStateMismatch outcomeClass expected actualState) ->
        assert
          ( outcomeClass == typedNegativeClass
            && expected == CallableOutcomeState "state.retryable"
            && actualState == CallableOutcomeState "state.wrong"
          )
          "branch-state mismatch lost exact class/state identity"
      other -> Left ("branch-sensitive state drift was accepted: " <> show other)

calleeTransitionMismatchRejects :: Either String ()
calleeTransitionMismatchRejects =
  let actual = replaceBranch typedNegativeClass
        (\branch -> branch { callableOutcomeCalleeTransition = ConsumeCallee })
        expectedOutcomes
  in case checkCallableOutcomeContract expectedOutcomes actual of
      Left (CallableOutcomeCalleeTransitionMismatch outcomeClass expected actualTransition) ->
        assert
          ( outcomeClass == typedNegativeClass
            && expected == PreserveCallee
            && actualTransition == ConsumeCallee
          )
          "callee-transition mismatch lost exact outcome transition"
      other -> Left ("per-outcome callee transition drift was accepted: " <> show other)

postconditionMismatchRejects :: Either String ()
postconditionMismatchRejects =
  let actual = replaceBranch successClass
        (\branch -> branch
          { callableOutcomePostconditions = Set.singleton (atom "post.success.changed") })
        expectedOutcomes
  in case checkCallableOutcomeContract expectedOutcomes actual of
      Left (CallableOutcomePostconditionMismatch outcomeClass expected actualPosts) ->
        assert
          ( outcomeClass == successClass
            && expected == Set.singleton (atom "post.success")
            && actualPosts == Set.singleton (atom "post.success.changed")
          )
          "postcondition mismatch lost exact outcome/postcondition identity"
      other -> Left ("per-outcome postcondition drift was accepted: " <> show other)

residualToPostconditionRejects :: Either String ()
residualToPostconditionRejects =
  reclassificationRejects
    OutcomePostconditionBucket
    (\branch -> branch
      { callableOutcomeResidualObligations = Set.delete retryObligation
          (callableOutcomeResidualObligations branch)
      , callableOutcomePostconditions = Set.insert retryObligation
          (callableOutcomePostconditions branch)
      })

residualToAssumptionRejects :: Either String ()
residualToAssumptionRejects =
  reclassificationRejects
    OutcomeAssumptionBucket
    (\branch -> branch
      { callableOutcomeResidualObligations = Set.delete retryObligation
          (callableOutcomeResidualObligations branch)
      , callableOutcomeAssumptions = Set.insert retryObligation
          (callableOutcomeAssumptions branch)
      })

residualToEffectRejects :: Either String ()
residualToEffectRejects =
  reclassificationRejects
    OutcomeEffectBucket
    (\branch -> branch
      { callableOutcomeResidualObligations = Set.delete retryObligation
          (callableOutcomeResidualObligations branch)
      , callableOutcomeEffects = Set.insert retryObligation
          (callableOutcomeEffects branch)
      })

residualToDischargedFactRejects :: Either String ()
residualToDischargedFactRejects =
  reclassificationRejects
    OutcomeDischargedFactBucket
    (\branch -> branch
      { callableOutcomeResidualObligations = Set.delete retryObligation
          (callableOutcomeResidualObligations branch)
      , callableOutcomeDischargedFacts = Set.insert retryObligation
          (callableOutcomeDischargedFacts branch)
      })

reclassificationRejects
  :: CallableOutcomeBucket
  -> (CallableOutcomeContract -> CallableOutcomeContract)
  -> Either String ()
reclassificationRejects expectedBucket mutate =
  let actual = replaceBranch typedNegativeClass mutate expectedOutcomes
  in case checkCallableOutcomeContract expectedOutcomes actual of
      Left (CallableResidualObligationReclassified outcomeClass obligation bucket) ->
        assert
          ( outcomeClass == typedNegativeClass
            && obligation == retryObligation
            && bucket == expectedBucket
          )
          "residual-obligation laundering rejection lost exact class/obligation/bucket"
      other -> Left ("residual obligation was laundered into another bucket: " <> show other)

droppedResidualRejects :: Either String ()
droppedResidualRejects =
  let actual = replaceBranch typedNegativeClass
        (\branch -> branch
          { callableOutcomeResidualObligations = Set.empty })
        expectedOutcomes
  in case checkCallableOutcomeContract expectedOutcomes actual of
      Left (CallableResidualObligationMismatch outcomeClass expected actualResidual) ->
        assert
          ( outcomeClass == typedNegativeClass
            && expected == Set.singleton retryObligation
            && Set.null actualResidual
          )
          "dropped-residual rejection lost exact outcome/obligation set"
      other -> Left ("residual obligation silently disappeared: " <> show other)

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

expectedClasses :: Set.Set CallableOutcomeClass
expectedClasses = Set.fromList (map callableOutcomeClass expectedOutcomes)

successClass, typedNegativeClass, declaredTerminalClass, fatalClass :: CallableOutcomeClass
successClass = CallableSuccessOutcome
typedNegativeClass = CallableNonSuccessOutcome (CallableTypedNegative notFoundOutcome)
declaredTerminalClass = CallableNonSuccessOutcome (CallableDeclaredTerminal doneOutcome)
fatalClass = CallableNonSuccessOutcome (CallableFatal "storage.fatal")

successBranch, typedNegativeBranch, declaredTerminalBranch, fatalBranch :: CallableOutcomeContract
successBranch = branch
  successClass
  "state.ready"
  PreserveCallee
  ["post.success"]
  []
  []
  ["effect.storage.read"]
  ["fact.request.validated"]
typedNegativeBranch = branch
  typedNegativeClass
  "state.retryable"
  PreserveCallee
  ["post.not-found"]
  ["obligation.retry-budget"]
  ["assumption.catalog-current"]
  ["effect.storage.read"]
  ["fact.request.validated"]
declaredTerminalBranch = branch
  declaredTerminalClass
  "state.closed"
  ConsumeCallee
  ["post.session-closed"]
  []
  []
  ["effect.session.close"]
  ["fact.close-authorized"]
fatalBranch = branch
  fatalClass
  "state.failed"
  ConsumeCallee
  ["post.fatal-recorded"]
  ["obligation.fatal-audit"]
  []
  ["effect.diagnostic.emit"]
  []

branch
  :: CallableOutcomeClass
  -> String
  -> CalleeTransition
  -> [String]
  -> [String]
  -> [String]
  -> [String]
  -> [String]
  -> CallableOutcomeContract
branch outcomeClass state transition postconditions residual assumptions effects discharged =
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

fromString :: String -> Data.Text.Text
fromString = Data.Text.pack

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
