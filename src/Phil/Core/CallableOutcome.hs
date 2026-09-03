{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.CallableOutcome
  ( CallableOutcomeClass (..)
  , CallableOutcomeState (..)
  , CallableOutcomeAtom (..)
  , CallableOutcomeBucket (..)
  , CallableOutcomeContract (..)
  , CheckedCallableOutcomeContract (..)
  , CallableOutcomeError (..)
  , checkCallableOutcomeContract
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Callable (CalleeTransition)
import qualified Phil.Core.CallableOutcomeKernelBridge as KernelBridge
import Phil.Core.CallableRefinement (CallableFailure)

-- | Exact caller-visible outcome class. Success is explicit here so the complete
-- callable branch domain is checked rather than treating non-success cases as an
-- untyped side set.
data CallableOutcomeClass
  = CallableSuccessOutcome
  | CallableNonSuccessOutcome CallableFailure
  deriving (Eq, Ord, Show)

-- | Canonical summary of the branch-sensitive semantic state at one callable
-- outcome. The concrete resource/evidence telescope remains owned by the
-- competent checkers that produce this stable summary.
newtype CallableOutcomeState = CallableOutcomeState
  { unCallableOutcomeState :: Text
  }
  deriving (Eq, Ord, Show)

-- | Stable semantic reference used across the distinct callable outcome buckets.
-- A shared atom type makes accidental reclassification executable to detect:
-- moving the same obligation reference into an assumption/effect/postcondition
-- bucket cannot be hidden by changing only its Haskell constructor.
newtype CallableOutcomeAtom = CallableOutcomeAtom
  { unCallableOutcomeAtom :: Text
  }
  deriving (Eq, Ord, Show)

data CallableOutcomeBucket
  = OutcomePostconditionBucket
  | OutcomeAssumptionBucket
  | OutcomeEffectBucket
  | OutcomeDischargedFactBucket
  deriving (Eq, Ord, Show)

-- | One exact public/checked callable outcome branch. Each semantic category is
-- retained independently; in particular residual obligations are not inferred
-- from absence in another bucket and cannot silently become assumptions,
-- effects, postconditions, or discharged facts.
data CallableOutcomeContract = CallableOutcomeContract
  { callableOutcomeClass :: CallableOutcomeClass
  , callableOutcomeState :: CallableOutcomeState
  , callableOutcomeCalleeTransition :: CalleeTransition
  , callableOutcomePostconditions :: Set.Set CallableOutcomeAtom
  , callableOutcomeResidualObligations :: Set.Set CallableOutcomeAtom
  , callableOutcomeAssumptions :: Set.Set CallableOutcomeAtom
  , callableOutcomeEffects :: Set.Set CallableOutcomeAtom
  , callableOutcomeDischargedFacts :: Set.Set CallableOutcomeAtom
  }
  deriving (Eq, Ord, Show)

data CheckedCallableOutcomeContract = CheckedCallableOutcomeContract
  { checkedCallableExpectedOutcomes :: Map.Map CallableOutcomeClass CallableOutcomeContract
  , checkedCallableActualOutcomes :: Map.Map CallableOutcomeClass CallableOutcomeContract
  }
  deriving (Eq, Show)

data CallableOutcomeError
  = DuplicateExpectedCallableOutcome CallableOutcomeClass
  | DuplicateActualCallableOutcome CallableOutcomeClass
  | CallableOutcomeClassSetMismatch
      (Set.Set CallableOutcomeClass)
      (Set.Set CallableOutcomeClass)
  | CallableOutcomeStateMismatch
      CallableOutcomeClass CallableOutcomeState CallableOutcomeState
  | CallableOutcomeCalleeTransitionMismatch
      CallableOutcomeClass CalleeTransition CalleeTransition
  | CallableResidualObligationReclassified
      CallableOutcomeClass CallableOutcomeAtom CallableOutcomeBucket
  | CallableResidualObligationMismatch
      CallableOutcomeClass
      (Set.Set CallableOutcomeAtom)
      (Set.Set CallableOutcomeAtom)
  | CallableOutcomePostconditionMismatch
      CallableOutcomeClass
      (Set.Set CallableOutcomeAtom)
      (Set.Set CallableOutcomeAtom)
  | CallableOutcomeAssumptionMismatch
      CallableOutcomeClass
      (Set.Set CallableOutcomeAtom)
      (Set.Set CallableOutcomeAtom)
  | CallableOutcomeEffectMismatch
      CallableOutcomeClass
      (Set.Set CallableOutcomeAtom)
      (Set.Set CallableOutcomeAtom)
  | CallableOutcomeDischargedFactMismatch
      CallableOutcomeClass
      (Set.Set CallableOutcomeAtom)
      (Set.Set CallableOutcomeAtom)
  | CallableOutcomeKernelDisagreement Text
  deriving (Eq, Show)

-- | Check complete branch-class and residue fidelity for CALL-018. Native code
-- owns normalization, concrete equality, residual witness selection, and exact
-- diagnostic payloads. The extracted Rocq classifier owns the final semantic
-- decision over those reflected facts and is used fail-closed.
checkCallableOutcomeContract
  :: [CallableOutcomeContract]
  -> [CallableOutcomeContract]
  -> Either CallableOutcomeError CheckedCallableOutcomeContract
checkCallableOutcomeContract expectedOutcomes actualOutcomes = do
  expected <- normalizeExpected expectedOutcomes
  actual <- normalizeActual actualOutcomes
  let expectedClasses = Map.keysSet expected
      actualClasses = Map.keysSet actual
      classDomainExact = expectedClasses == actualClasses
  if classDomainExact
    then mapM_ (checkOne actual) (Map.toAscList expected)
    else case KernelBridge.classifyCallableOutcomeFacts
        False True True True True True True True KernelBridge.KernelResidualExact of
      KernelBridge.CallableOutcomeClassSetClassification ->
        Left (CallableOutcomeClassSetMismatch expectedClasses actualClasses)
      _ -> kernelDisagreement "class-domain rejection"
  Right CheckedCallableOutcomeContract
    { checkedCallableExpectedOutcomes = expected
    , checkedCallableActualOutcomes = actual
    }

normalizeExpected
  :: [CallableOutcomeContract]
  -> Either CallableOutcomeError (Map.Map CallableOutcomeClass CallableOutcomeContract)
normalizeExpected = normalizeOutcomes DuplicateExpectedCallableOutcome

normalizeActual
  :: [CallableOutcomeContract]
  -> Either CallableOutcomeError (Map.Map CallableOutcomeClass CallableOutcomeContract)
normalizeActual = normalizeOutcomes DuplicateActualCallableOutcome

normalizeOutcomes
  :: (CallableOutcomeClass -> CallableOutcomeError)
  -> [CallableOutcomeContract]
  -> Either CallableOutcomeError (Map.Map CallableOutcomeClass CallableOutcomeContract)
normalizeOutcomes duplicateError = foldl addOutcome (Right Map.empty)
  where
    addOutcome accumulated outcome = do
      normalized <- accumulated
      let outcomeClass = callableOutcomeClass outcome
      if Map.member outcomeClass normalized
        then Left (duplicateError outcomeClass)
        else Right (Map.insert outcomeClass outcome normalized)

checkOne
  :: Map.Map CallableOutcomeClass CallableOutcomeContract
  -> (CallableOutcomeClass, CallableOutcomeContract)
  -> Either CallableOutcomeError ()
checkOne actualByClass (outcomeClass, expected) =
  case classification of
    KernelBridge.CallableOutcomeClassSetClassification ->
      kernelDisagreement "per-branch class-domain classification"
    KernelBridge.CallableOutcomeStateClassification
      | not stateExact ->
          Left (CallableOutcomeStateMismatch outcomeClass
            (callableOutcomeState expected) (callableOutcomeState actual))
      | otherwise -> kernelDisagreement "state classification"
    KernelBridge.CallableOutcomeCalleeTransitionClassification
      | stateExact && not transitionExact ->
          Left (CallableOutcomeCalleeTransitionMismatch outcomeClass
            (callableOutcomeCalleeTransition expected)
            (callableOutcomeCalleeTransition actual))
      | otherwise -> kernelDisagreement "callee-transition classification"
    KernelBridge.CallableResidualObligationReclassifiedClassification kernelBucket ->
      case firstReclassified of
        Just (obligation, bucket)
          | stateExact
              && transitionExact
              && toKernelBucket bucket == kernelBucket ->
              Left (CallableResidualObligationReclassified
                outcomeClass obligation bucket)
        _ -> kernelDisagreement "residual-reclassification classification"
    KernelBridge.CallableResidualObligationMismatchClassification
      | stateExact
          && transitionExact
          && noReclassification
          && not residualExact ->
          Left (CallableResidualObligationMismatch outcomeClass
            expectedResidual actualResidual)
      | otherwise -> kernelDisagreement "residual-mismatch classification"
    KernelBridge.CallableOutcomePostconditionClassification
      | prefixThroughResidual && not postconditionsExact ->
          Left (CallableOutcomePostconditionMismatch outcomeClass
            expectedPostconditions actualPostconditions)
      | otherwise -> kernelDisagreement "postcondition classification"
    KernelBridge.CallableOutcomeAssumptionClassification
      | prefixThroughResidual
          && postconditionsExact
          && not assumptionsExact ->
          Left (CallableOutcomeAssumptionMismatch outcomeClass
            expectedAssumptions actualAssumptions)
      | otherwise -> kernelDisagreement "assumption classification"
    KernelBridge.CallableOutcomeEffectClassification
      | prefixThroughResidual
          && postconditionsExact
          && assumptionsExact
          && not effectsExact ->
          Left (CallableOutcomeEffectMismatch outcomeClass
            expectedEffects actualEffects)
      | otherwise -> kernelDisagreement "effect classification"
    KernelBridge.CallableOutcomeDischargedFactClassification
      | prefixThroughResidual
          && postconditionsExact
          && assumptionsExact
          && effectsExact
          && not dischargedFactsExact ->
          Left (CallableOutcomeDischargedFactMismatch outcomeClass
            expectedDischarged actualDischarged)
      | otherwise -> kernelDisagreement "discharged-fact classification"
    KernelBridge.CallableOutcomeAcceptedClassification
      | prefixThroughResidual
          && postconditionsExact
          && assumptionsExact
          && effectsExact
          && dischargedFactsExact -> Right ()
      | otherwise -> kernelDisagreement "accepted classification"
  where
    actual = actualByClass Map.! outcomeClass
    stateExact = callableOutcomeState expected == callableOutcomeState actual
    transitionExact =
      callableOutcomeCalleeTransition expected == callableOutcomeCalleeTransition actual
    expectedResidual = callableOutcomeResidualObligations expected
    actualResidual = callableOutcomeResidualObligations actual
    residualExact = expectedResidual == actualResidual
    expectedPostconditions = callableOutcomePostconditions expected
    actualPostconditions = callableOutcomePostconditions actual
    postconditionsExact = expectedPostconditions == actualPostconditions
    expectedAssumptions = callableOutcomeAssumptions expected
    actualAssumptions = callableOutcomeAssumptions actual
    assumptionsExact = expectedAssumptions == actualAssumptions
    expectedEffects = callableOutcomeEffects expected
    actualEffects = callableOutcomeEffects actual
    effectsExact = expectedEffects == actualEffects
    expectedDischarged = callableOutcomeDischargedFacts expected
    actualDischarged = callableOutcomeDischargedFacts actual
    dischargedFactsExact = expectedDischarged == actualDischarged
    missing = Set.toAscList (Set.difference expectedResidual actualResidual)
    firstReclassified = firstJust (map reclassifiedBucket missing)
    noReclassification = case firstReclassified of
      Nothing -> True
      Just _ -> False
    prefixThroughResidual =
      stateExact && transitionExact && noReclassification && residualExact
    residualDisposition = case firstReclassified of
      Nothing -> KernelBridge.KernelResidualExact
      Just (_, bucket) ->
        KernelBridge.KernelResidualReclassified (toKernelBucket bucket)
    classification = KernelBridge.classifyCallableOutcomeFacts
      True
      stateExact
      transitionExact
      residualExact
      postconditionsExact
      assumptionsExact
      effectsExact
      dischargedFactsExact
      residualDisposition

    reclassifiedBucket obligation
      | Set.member obligation actualPostconditions =
          Just (obligation, OutcomePostconditionBucket)
      | Set.member obligation actualAssumptions =
          Just (obligation, OutcomeAssumptionBucket)
      | Set.member obligation actualEffects =
          Just (obligation, OutcomeEffectBucket)
      | Set.member obligation actualDischarged =
          Just (obligation, OutcomeDischargedFactBucket)
      | otherwise = Nothing

firstJust :: [Maybe a] -> Maybe a
firstJust [] = Nothing
firstJust (candidate : rest) = case candidate of
  Just value -> Just value
  Nothing -> firstJust rest

toKernelBucket :: CallableOutcomeBucket -> KernelBridge.KernelOutcomeBucket
toKernelBucket bucket = case bucket of
  OutcomePostconditionBucket -> KernelBridge.KernelOutcomePostconditionBucket
  OutcomeAssumptionBucket -> KernelBridge.KernelOutcomeAssumptionBucket
  OutcomeEffectBucket -> KernelBridge.KernelOutcomeEffectBucket
  OutcomeDischargedFactBucket -> KernelBridge.KernelOutcomeDischargedFactBucket

kernelDisagreement :: Text -> Either CallableOutcomeError a
kernelDisagreement detail =
  Left (CallableOutcomeKernelDisagreement
    ("extracted Callable Outcome decision disagreed with native facts at " <> detail))
