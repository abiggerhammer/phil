module Main (main) where

import qualified CallableOutcomeKernel as Kernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ expect "class-domain mismatch rejects first" isClassSet
        (decide False True True True True True True True Kernel.ResidualExact)
    , expect "state mismatch precedes residual classification" isState
        (decide True False True True True True True True
          (Kernel.ResidualReclassified Kernel.OutcomePostconditionBucket))
    , expect "callee transition mismatch precedes residual classification" isTransition
        (decide True True False True True True True True
          (Kernel.ResidualReclassified Kernel.OutcomePostconditionBucket))
    , expect "residual obligation reclassified as postcondition rejects exact bucket"
        (isReclassifiedPostcondition)
        (decide True True True False False False False False
          (Kernel.ResidualReclassified Kernel.OutcomePostconditionBucket))
    , expect "residual obligation reclassified as assumption rejects exact bucket"
        (isReclassifiedAssumption)
        (decide True True True False False False False False
          (Kernel.ResidualReclassified Kernel.OutcomeAssumptionBucket))
    , expect "residual obligation reclassified as effect rejects exact bucket"
        (isReclassifiedEffect)
        (decide True True True False False False False False
          (Kernel.ResidualReclassified Kernel.OutcomeEffectBucket))
    , expect "residual obligation reclassified as discharged fact rejects exact bucket"
        (isReclassifiedDischarged)
        (decide True True True False False False False False
          (Kernel.ResidualReclassified Kernel.OutcomeDischargedFactBucket))
    , expect "residual mismatch disposition rejects before semantic buckets" isResidualMismatch
        (decide True True True True False False False False Kernel.ResidualMismatch)
    , expect "exact disposition still requires exact residual set" isResidualMismatch
        (decide True True True False True True True True Kernel.ResidualExact)
    , expect "postcondition mismatch rejects" isPostcondition
        (decide True True True True False True True True Kernel.ResidualExact)
    , expect "assumption mismatch rejects" isAssumption
        (decide True True True True True False True True Kernel.ResidualExact)
    , expect "effect mismatch rejects" isEffect
        (decide True True True True True True False True Kernel.ResidualExact)
    , expect "discharged-fact mismatch rejects" isDischarged
        (decide True True True True True True True False Kernel.ResidualExact)
    , expect "exact callable outcome facts accept" isAccepted
        (decide True True True True True True True True Kernel.ResidualExact)
    ]
  if and results then pure () else exitFailure

decide
  :: Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool
  -> Kernel.ResidualDisposition
  -> Kernel.CallableOutcomeDecision
decide = Kernel.decideCallableOutcomeByFacts

expect :: String -> (a -> Bool) -> a -> IO Bool
expect label predicate actual
  | predicate actual = putStrLn ("PASS: " <> label) >> pure True
  | otherwise = putStrLn ("FAIL: " <> label) >> pure False

isClassSet :: Kernel.CallableOutcomeDecision -> Bool
isClassSet Kernel.CallableOutcomeClassSetDecision = True
isClassSet _ = False

isState :: Kernel.CallableOutcomeDecision -> Bool
isState Kernel.CallableOutcomeStateDecision = True
isState _ = False

isTransition :: Kernel.CallableOutcomeDecision -> Bool
isTransition Kernel.CallableOutcomeCalleeTransitionDecision = True
isTransition _ = False

isReclassifiedPostcondition :: Kernel.CallableOutcomeDecision -> Bool
isReclassifiedPostcondition
  (Kernel.CallableResidualObligationReclassifiedDecision
    Kernel.OutcomePostconditionBucket) = True
isReclassifiedPostcondition _ = False

isReclassifiedAssumption :: Kernel.CallableOutcomeDecision -> Bool
isReclassifiedAssumption
  (Kernel.CallableResidualObligationReclassifiedDecision
    Kernel.OutcomeAssumptionBucket) = True
isReclassifiedAssumption _ = False

isReclassifiedEffect :: Kernel.CallableOutcomeDecision -> Bool
isReclassifiedEffect
  (Kernel.CallableResidualObligationReclassifiedDecision
    Kernel.OutcomeEffectBucket) = True
isReclassifiedEffect _ = False

isReclassifiedDischarged :: Kernel.CallableOutcomeDecision -> Bool
isReclassifiedDischarged
  (Kernel.CallableResidualObligationReclassifiedDecision
    Kernel.OutcomeDischargedFactBucket) = True
isReclassifiedDischarged _ = False

isResidualMismatch :: Kernel.CallableOutcomeDecision -> Bool
isResidualMismatch Kernel.CallableResidualObligationMismatchDecision = True
isResidualMismatch _ = False

isPostcondition :: Kernel.CallableOutcomeDecision -> Bool
isPostcondition Kernel.CallableOutcomePostconditionDecision = True
isPostcondition _ = False

isAssumption :: Kernel.CallableOutcomeDecision -> Bool
isAssumption Kernel.CallableOutcomeAssumptionDecision = True
isAssumption _ = False

isEffect :: Kernel.CallableOutcomeDecision -> Bool
isEffect Kernel.CallableOutcomeEffectDecision = True
isEffect _ = False

isDischarged :: Kernel.CallableOutcomeDecision -> Bool
isDischarged Kernel.CallableOutcomeDischargedFactDecision = True
isDischarged _ = False

isAccepted :: Kernel.CallableOutcomeDecision -> Bool
isAccepted Kernel.CallableOutcomeAcceptedDecision = True
isAccepted _ = False
