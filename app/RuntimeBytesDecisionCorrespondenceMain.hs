module Main (main) where

import qualified RuntimeBytesKernel as Kernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  let checks =
        [ ("forgetting dominates later type facts",
            Kernel.decideBytesCheckByFacts True False False
              == Kernel.BytesCheckAcceptedForgetting)
        , ("definitionally equal accepts after non-forgetting",
            Kernel.decideBytesCheckByFacts False True False
              == Kernel.BytesCheckAcceptedDefinitionallyEqual)
        , ("same Bytes family requires explicit transport",
            Kernel.decideBytesCheckByFacts False False True
              == Kernel.BytesCheckRequiresExplicitTransport)
        , ("unrelated nondefinitional types reject",
            Kernel.decideBytesCheckByFacts False False False
              == Kernel.BytesCheckIncompatible)
        , ("non-runtime refinement source rejects first",
            Kernel.decideRuntimeBytesRefinementByFacts False True True True
              == Kernel.RuntimeBytesRefinementSourceNotRuntime)
        , ("non-exact refinement target rejects second",
            Kernel.decideRuntimeBytesRefinementByFacts True False True True
              == Kernel.RuntimeBytesRefinementTargetNotExact)
        , ("invisible value subject rejects before evidence",
            Kernel.decideRuntimeBytesRefinementByFacts True True False True
              == Kernel.RuntimeBytesRefinementSubjectNotVisible)
        , ("missing exact length evidence rejects",
            Kernel.decideRuntimeBytesRefinementByFacts True True True False
              == Kernel.RuntimeBytesRefinementEvidenceRequired)
        , ("all exact runtime refinement facts accept",
            Kernel.decideRuntimeBytesRefinementByFacts True True True True
              == Kernel.RuntimeBytesRefinementAccepted)
        ]
  mapM_ report checks
  if all snd checks then pure () else exitFailure
  where
    report (label, True) = putStrLn ("PASS: IO-BYTES kernel " <> label)
    report (label, False) = putStrLn ("FAIL: IO-BYTES kernel " <> label)
