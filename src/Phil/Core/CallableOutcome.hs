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
  deriving (Eq, Show)

-- | Check complete branch-class and residue fidelity for CALL-018. This is a
-- direct equality boundary, not a refinement/subtyping relation: CALL-012 owns
-- whether one callable may substitute for another, while this checker ensures
-- that the chosen callable interface preserves the exact classification and
-- semantic account of each of its outcomes.
checkCallableOutcomeContract
  :: [CallableOutcomeContract]
  -> [CallableOutcomeContract]
  -> Either CallableOutcomeError CheckedCallableOutcomeContract
checkCallableOutcomeContract expectedOutcomes actualOutcomes = do
  expected <- normalizeExpected expectedOutcomes
  actual <- normalizeActual actualOutcomes
  let expectedClasses = Map.keysSet expected
      actualClasses = Map.keysSet actual
  if expectedClasses /= actualClasses
    then Left (CallableOutcomeClassSetMismatch expectedClasses actualClasses)
    else mapM_ (checkOne actual) (Map.toAscList expected)
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
checkOne actualByClass (outcomeClass, expected) = do
  let actual = actualByClass Map.! outcomeClass
  requireEqual (CallableOutcomeStateMismatch outcomeClass)
    (callableOutcomeState expected)
    (callableOutcomeState actual)
  requireEqual (CallableOutcomeCalleeTransitionMismatch outcomeClass)
    (callableOutcomeCalleeTransition expected)
    (callableOutcomeCalleeTransition actual)
  checkResidualObligations outcomeClass expected actual
  requireEqual (CallableOutcomePostconditionMismatch outcomeClass)
    (callableOutcomePostconditions expected)
    (callableOutcomePostconditions actual)
  requireEqual (CallableOutcomeAssumptionMismatch outcomeClass)
    (callableOutcomeAssumptions expected)
    (callableOutcomeAssumptions actual)
  requireEqual (CallableOutcomeEffectMismatch outcomeClass)
    (callableOutcomeEffects expected)
    (callableOutcomeEffects actual)
  requireEqual (CallableOutcomeDischargedFactMismatch outcomeClass)
    (callableOutcomeDischargedFacts expected)
    (callableOutcomeDischargedFacts actual)

checkResidualObligations
  :: CallableOutcomeClass
  -> CallableOutcomeContract
  -> CallableOutcomeContract
  -> Either CallableOutcomeError ()
checkResidualObligations outcomeClass expected actual =
  case firstReclassified of
    Just (obligation, bucket) ->
      Left (CallableResidualObligationReclassified outcomeClass obligation bucket)
    Nothing -> requireEqual (CallableResidualObligationMismatch outcomeClass)
      expectedResidual actualResidual
  where
    expectedResidual = callableOutcomeResidualObligations expected
    actualResidual = callableOutcomeResidualObligations actual
    missing = Set.toAscList (Set.difference expectedResidual actualResidual)
    firstReclassified = firstJust (map reclassifiedBucket missing)

    reclassifiedBucket obligation
      | Set.member obligation (callableOutcomePostconditions actual) =
          Just (obligation, OutcomePostconditionBucket)
      | Set.member obligation (callableOutcomeAssumptions actual) =
          Just (obligation, OutcomeAssumptionBucket)
      | Set.member obligation (callableOutcomeEffects actual) =
          Just (obligation, OutcomeEffectBucket)
      | Set.member obligation (callableOutcomeDischargedFacts actual) =
          Just (obligation, OutcomeDischargedFactBucket)
      | otherwise = Nothing

firstJust :: [Maybe a] -> Maybe a
firstJust [] = Nothing
firstJust (candidate : rest) = case candidate of
  Just value -> Just value
  Nothing -> firstJust rest

requireEqual :: Eq a => (a -> a -> CallableOutcomeError) -> a -> a -> Either CallableOutcomeError ()
requireEqual makeError expected actual
  | expected == actual = Right ()
  | otherwise = Left (makeError expected actual)
