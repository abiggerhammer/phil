module Main (main) where

import qualified GenericStaticKindKernel as Kernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ expect "direct matching kind accepts"
        (Kernel.decideDirectStaticActualByFact True)
        Kernel.DirectStaticActualAcceptedDecision
    , expect "direct wrong kind rejects"
        (Kernel.decideDirectStaticActualByFact False)
        Kernel.DirectStaticActualKindMismatchDecision
    , expect "missing reference rejects unresolved"
        (Kernel.decideReferencedStaticActualByFacts False False False False)
        Kernel.ReferencedStaticActualUnresolvedDecision
    , expect "missing name wins rejection precedence"
        (Kernel.decideReferencedStaticActualByFacts False True True True)
        Kernel.ReferencedStaticActualUnresolvedDecision
    , expect "wrong expected kind rejects"
        (Kernel.decideReferencedStaticActualByFacts True False False False)
        Kernel.ReferencedStaticActualKindMismatchDecision
    , expect "kind mismatch wins later facts"
        (Kernel.decideReferencedStaticActualByFacts True False True True)
        Kernel.ReferencedStaticActualKindMismatchDecision
    , expect "same-kind ambiguity rejects"
        (Kernel.decideReferencedStaticActualByFacts True True False False)
        Kernel.ReferencedStaticActualAmbiguousDecision
    , expect "ambiguity wins selected-form fact"
        (Kernel.decideReferencedStaticActualByFacts True True False True)
        Kernel.ReferencedStaticActualAmbiguousDecision
    , expect "selected semantic-form mismatch rejects"
        (Kernel.decideReferencedStaticActualByFacts True True True False)
        Kernel.ReferencedStaticActualSemanticFormMismatchDecision
    , expect "unique exact expected-kind reference accepts"
        (Kernel.decideReferencedStaticActualByFacts True True True True)
        Kernel.ReferencedStaticActualAcceptedDecision
    , expect "shape missing parameter-key identity rejects"
        (Kernel.decideCheckedStaticActualShapeByFacts False False)
        Kernel.CheckedStaticActualParameterKeyDecision
    , expect "parameter-key rejection precedes kind fact"
        (Kernel.decideCheckedStaticActualShapeByFacts False True)
        Kernel.CheckedStaticActualParameterKeyDecision
    , expect "shape kind mismatch rejects"
        (Kernel.decideCheckedStaticActualShapeByFacts True False)
        Kernel.CheckedStaticActualKindDecision
    , expect "exact checked shape accepts"
        (Kernel.decideCheckedStaticActualShapeByFacts True True)
        Kernel.CheckedStaticActualShapeAcceptedDecision
    ]
  if and results then pure () else exitFailure

expect :: (Eq a, Show a) => String -> a -> a -> IO Bool
expect label actual expected
  | actual == expected = putStrLn ("PASS: " <> label) >> pure True
  | otherwise = do
      putStrLn ("FAIL: " <> label <> " -- got " <> show actual <> ", expected " <> show expected)
      pure False
