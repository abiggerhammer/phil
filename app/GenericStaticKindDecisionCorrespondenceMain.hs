module Main (main) where

import qualified GenericStaticKindKernel as Kernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ expect "direct matching kind accepts" $
        isDirectAccepted (Kernel.decideDirectStaticActualByFact True)
    , expect "direct wrong kind rejects" $
        isDirectKindMismatch (Kernel.decideDirectStaticActualByFact False)
    , expect "missing reference rejects unresolved" $
        isReferenceUnresolved
          (Kernel.decideReferencedStaticActualByFacts False False False False)
    , expect "missing name wins rejection precedence" $
        isReferenceUnresolved
          (Kernel.decideReferencedStaticActualByFacts False True True True)
    , expect "wrong expected kind rejects" $
        isReferenceKindMismatch
          (Kernel.decideReferencedStaticActualByFacts True False False False)
    , expect "kind mismatch wins later facts" $
        isReferenceKindMismatch
          (Kernel.decideReferencedStaticActualByFacts True False True True)
    , expect "same-kind ambiguity rejects" $
        isReferenceAmbiguous
          (Kernel.decideReferencedStaticActualByFacts True True False False)
    , expect "ambiguity wins selected-form fact" $
        isReferenceAmbiguous
          (Kernel.decideReferencedStaticActualByFacts True True False True)
    , expect "selected semantic-form mismatch rejects" $
        isReferenceSemanticFormMismatch
          (Kernel.decideReferencedStaticActualByFacts True True True False)
    , expect "unique exact expected-kind reference accepts" $
        isReferenceAccepted
          (Kernel.decideReferencedStaticActualByFacts True True True True)
    , expect "shape missing parameter-key identity rejects" $
        isShapeParameterKeyMismatch
          (Kernel.decideCheckedStaticActualShapeByFacts False False)
    , expect "parameter-key rejection precedes kind fact" $
        isShapeParameterKeyMismatch
          (Kernel.decideCheckedStaticActualShapeByFacts False True)
    , expect "shape kind mismatch rejects" $
        isShapeKindMismatch
          (Kernel.decideCheckedStaticActualShapeByFacts True False)
    , expect "exact checked shape accepts" $
        isShapeAccepted
          (Kernel.decideCheckedStaticActualShapeByFacts True True)
    ]
  if and results then pure () else exitFailure

expect :: String -> Bool -> IO Bool
expect label condition
  | condition = putStrLn ("PASS: " <> label) >> pure True
  | otherwise = putStrLn ("FAIL: " <> label) >> pure False

isDirectAccepted :: Kernel.DirectStaticActualDecision -> Bool
isDirectAccepted decision = case decision of
  Kernel.DirectStaticActualAcceptedDecision -> True
  _ -> False

isDirectKindMismatch :: Kernel.DirectStaticActualDecision -> Bool
isDirectKindMismatch decision = case decision of
  Kernel.DirectStaticActualKindMismatchDecision -> True
  _ -> False

isReferenceUnresolved :: Kernel.ReferencedStaticActualDecision -> Bool
isReferenceUnresolved decision = case decision of
  Kernel.ReferencedStaticActualUnresolvedDecision -> True
  _ -> False

isReferenceKindMismatch :: Kernel.ReferencedStaticActualDecision -> Bool
isReferenceKindMismatch decision = case decision of
  Kernel.ReferencedStaticActualKindMismatchDecision -> True
  _ -> False

isReferenceAmbiguous :: Kernel.ReferencedStaticActualDecision -> Bool
isReferenceAmbiguous decision = case decision of
  Kernel.ReferencedStaticActualAmbiguousDecision -> True
  _ -> False

isReferenceSemanticFormMismatch :: Kernel.ReferencedStaticActualDecision -> Bool
isReferenceSemanticFormMismatch decision = case decision of
  Kernel.ReferencedStaticActualSemanticFormMismatchDecision -> True
  _ -> False

isReferenceAccepted :: Kernel.ReferencedStaticActualDecision -> Bool
isReferenceAccepted decision = case decision of
  Kernel.ReferencedStaticActualAcceptedDecision -> True
  _ -> False

isShapeParameterKeyMismatch :: Kernel.CheckedStaticActualShapeDecision -> Bool
isShapeParameterKeyMismatch decision = case decision of
  Kernel.CheckedStaticActualParameterKeyDecision -> True
  _ -> False

isShapeKindMismatch :: Kernel.CheckedStaticActualShapeDecision -> Bool
isShapeKindMismatch decision = case decision of
  Kernel.CheckedStaticActualKindDecision -> True
  _ -> False

isShapeAccepted :: Kernel.CheckedStaticActualShapeDecision -> Bool
isShapeAccepted decision = case decision of
  Kernel.CheckedStaticActualShapeAcceptedDecision -> True
  _ -> False
