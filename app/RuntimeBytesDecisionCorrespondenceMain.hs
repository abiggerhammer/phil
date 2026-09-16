module Main (main) where

import qualified RuntimeBytesKernel as Kernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  let checks =
        [ ("forgetting dominates later type facts",
            isAcceptedForgetting
              (Kernel.decideBytesCheckByFacts True False False))
        , ("definitionally equal accepts after non-forgetting",
            isAcceptedDefinitionallyEqual
              (Kernel.decideBytesCheckByFacts False True False))
        , ("same Bytes family requires explicit transport",
            isRequiresExplicitTransport
              (Kernel.decideBytesCheckByFacts False False True))
        , ("unrelated nondefinitional types reject",
            isIncompatible
              (Kernel.decideBytesCheckByFacts False False False))
        , ("non-runtime refinement source rejects first",
            isSourceNotRuntime
              (Kernel.decideRuntimeBytesRefinementByFacts False True True True))
        , ("non-exact refinement target rejects second",
            isTargetNotExact
              (Kernel.decideRuntimeBytesRefinementByFacts True False True True))
        , ("invisible value subject rejects before evidence",
            isSubjectNotVisible
              (Kernel.decideRuntimeBytesRefinementByFacts True True False True))
        , ("missing exact length evidence rejects",
            isEvidenceRequired
              (Kernel.decideRuntimeBytesRefinementByFacts True True True False))
        , ("all exact runtime refinement facts accept",
            isRefinementAccepted
              (Kernel.decideRuntimeBytesRefinementByFacts True True True True))
        ]
  mapM_ report checks
  if all snd checks then pure () else exitFailure
  where
    report (label, True) = putStrLn ("PASS: IO-BYTES kernel " <> label)
    report (label, False) = putStrLn ("FAIL: IO-BYTES kernel " <> label)

isAcceptedForgetting :: Kernel.BytesCheckDecision -> Bool
isAcceptedForgetting decision = case decision of
  Kernel.BytesCheckAcceptedForgetting -> True
  _ -> False

isAcceptedDefinitionallyEqual :: Kernel.BytesCheckDecision -> Bool
isAcceptedDefinitionallyEqual decision = case decision of
  Kernel.BytesCheckAcceptedDefinitionallyEqual -> True
  _ -> False

isRequiresExplicitTransport :: Kernel.BytesCheckDecision -> Bool
isRequiresExplicitTransport decision = case decision of
  Kernel.BytesCheckRequiresExplicitTransport -> True
  _ -> False

isIncompatible :: Kernel.BytesCheckDecision -> Bool
isIncompatible decision = case decision of
  Kernel.BytesCheckIncompatible -> True
  _ -> False

isSourceNotRuntime :: Kernel.RuntimeBytesRefinementDecision -> Bool
isSourceNotRuntime decision = case decision of
  Kernel.RuntimeBytesRefinementSourceNotRuntime -> True
  _ -> False

isTargetNotExact :: Kernel.RuntimeBytesRefinementDecision -> Bool
isTargetNotExact decision = case decision of
  Kernel.RuntimeBytesRefinementTargetNotExact -> True
  _ -> False

isSubjectNotVisible :: Kernel.RuntimeBytesRefinementDecision -> Bool
isSubjectNotVisible decision = case decision of
  Kernel.RuntimeBytesRefinementSubjectNotVisible -> True
  _ -> False

isEvidenceRequired :: Kernel.RuntimeBytesRefinementDecision -> Bool
isEvidenceRequired decision = case decision of
  Kernel.RuntimeBytesRefinementEvidenceRequired -> True
  _ -> False

isRefinementAccepted :: Kernel.RuntimeBytesRefinementDecision -> Bool
isRefinementAccepted decision = case decision of
  Kernel.RuntimeBytesRefinementAccepted -> True
  _ -> False
