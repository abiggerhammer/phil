module Main (main) where

import qualified CallableModeStrengtheningKernel as Kernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ expect "weakening rejects" isWeakening
        (Kernel.decideExplicitClosureModeByFacts False False False False False False)
    , expect "weakening takes precedence over contradictory equal fact" isWeakening
        (Kernel.decideExplicitClosureModeByFacts False True True True True True)
    , expect "equal mode accepts without justification" isEqual
        (Kernel.decideExplicitClosureModeByFacts True True False False False False)
    , expect "equal mode accepts before target-reason inspection" isEqual
        (Kernel.decideExplicitClosureModeByFacts True True True True False False)
    , expect "strict mode without justification rejects" isMissing
        (Kernel.decideExplicitClosureModeByFacts True False False False False False)
    , expect "target implementation reason rejects" isTarget
        (Kernel.decideExplicitClosureModeByFacts True False True True True True)
    , expect "wrong contract rejects" isWrongContract
        (Kernel.decideExplicitClosureModeByFacts True False True False False True)
    , expect "wrong contract takes precedence over empty detail" isWrongContract
        (Kernel.decideExplicitClosureModeByFacts True False True False False False)
    , expect "empty semantic detail rejects" isEmpty
        (Kernel.decideExplicitClosureModeByFacts True False True False True False)
    , expect "exact semantic strengthening accepts" isStrengthened
        (Kernel.decideExplicitClosureModeByFacts True False True False True True)
    , expect "exact checked shape accepts" isShapeAccepted
        (Kernel.decideCheckedClosureModeShapeByFacts True True True)
    , expect "checked minimum mismatch rejects first" isShapeMinimum
        (Kernel.decideCheckedClosureModeShapeByFacts False False False)
    , expect "checked selected mismatch rejects" isShapeSelected
        (Kernel.decideCheckedClosureModeShapeByFacts True False False)
    , expect "checked justification mismatch rejects" isShapeJustification
        (Kernel.decideCheckedClosureModeShapeByFacts True True False)
    ]
  if and results then pure () else exitFailure

expect :: String -> (a -> Bool) -> a -> IO Bool
expect label predicate actual
  | predicate actual = putStrLn ("PASS: " <> label) >> pure True
  | otherwise = putStrLn ("FAIL: " <> label) >> pure False

isWeakening :: Kernel.ExplicitClosureModeDecision -> Bool
isWeakening Kernel.ExplicitClosureModeWeakeningDecision = True
isWeakening _ = False

isEqual :: Kernel.ExplicitClosureModeDecision -> Bool
isEqual Kernel.ExplicitClosureModeEqualDecision = True
isEqual _ = False

isMissing :: Kernel.ExplicitClosureModeDecision -> Bool
isMissing Kernel.ExplicitClosureModeMissingJustificationDecision = True
isMissing _ = False

isTarget :: Kernel.ExplicitClosureModeDecision -> Bool
isTarget Kernel.ExplicitClosureModeTargetImplementationDecision = True
isTarget _ = False

isWrongContract :: Kernel.ExplicitClosureModeDecision -> Bool
isWrongContract Kernel.ExplicitClosureModeWrongContractDecision = True
isWrongContract _ = False

isEmpty :: Kernel.ExplicitClosureModeDecision -> Bool
isEmpty Kernel.ExplicitClosureModeEmptyJustificationDecision = True
isEmpty _ = False

isStrengthened :: Kernel.ExplicitClosureModeDecision -> Bool
isStrengthened Kernel.ExplicitClosureModeStrengthenedDecision = True
isStrengthened _ = False

isShapeMinimum :: Kernel.CheckedClosureModeShapeDecision -> Bool
isShapeMinimum Kernel.CheckedClosureModeMinimumDecision = True
isShapeMinimum _ = False

isShapeSelected :: Kernel.CheckedClosureModeShapeDecision -> Bool
isShapeSelected Kernel.CheckedClosureModeSelectedDecision = True
isShapeSelected _ = False

isShapeJustification :: Kernel.CheckedClosureModeShapeDecision -> Bool
isShapeJustification Kernel.CheckedClosureModeJustificationDecision = True
isShapeJustification _ = False

isShapeAccepted :: Kernel.CheckedClosureModeShapeDecision -> Bool
isShapeAccepted Kernel.CheckedClosureModeShapeAcceptedDecision = True
isShapeAccepted _ = False
