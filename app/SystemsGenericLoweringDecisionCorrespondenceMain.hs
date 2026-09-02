module Main where

import qualified SystemsGenericLoweringKernel as Kernel
import System.Exit (exitFailure)

assert :: String -> Bool -> IO ()
assert label condition =
  if condition
    then putStrLn ("PASS: " <> label)
    else do
      putStrLn ("FAIL: " <> label)
      exitFailure

tag :: Kernel.GenericSystemsLoweringDecision -> String
tag decision = case decision of
  Kernel.GenericSystemsLoweringAcceptedDecision -> "accepted"
  Kernel.GenericSystemsLoweringContextRevisionDecision -> "context-revision"
  Kernel.GenericSystemsLoweringVerifierProfileDecision -> "verifier-profile"
  Kernel.GenericSystemsLoweringRealizationRefsDecision -> "realization-refs"
  Kernel.GenericSystemsLoweringRealizationSemanticDecision -> "realization-semantic"
  Kernel.GenericSystemsLoweringResultCorrespondenceDecision -> "result-correspondence"
  Kernel.GenericSystemsLoweringStageClosureDecision -> "stage-closure"

main :: IO ()
main = do
  assert "generic Systems lowering accepts the complete Certified admission surface"
    (tag (Kernel.decideGenericSystemsLoweringByFacts
      True True True True True True) == "accepted")
  assert "generic Systems lowering requires explicit context revision"
    (tag (Kernel.decideGenericSystemsLoweringByFacts
      False True True True True True) == "context-revision")
  assert "generic Systems lowering requires verifier profile"
    (tag (Kernel.decideGenericSystemsLoweringByFacts
      True False True True True True) == "verifier-profile")
  assert "generic Systems lowering requires realization references"
    (tag (Kernel.decideGenericSystemsLoweringByFacts
      True True False True True True) == "realization-refs")
  assert "generic Systems lowering requires realization semantics"
    (tag (Kernel.decideGenericSystemsLoweringByFacts
      True True True False True True) == "realization-semantic")
  assert "generic Systems lowering requires exact normalized result correspondence"
    (tag (Kernel.decideGenericSystemsLoweringByFacts
      True True True True False True) == "result-correspondence")
  assert "generic Systems lowering composes Certified StageClosure"
    (tag (Kernel.decideGenericSystemsLoweringByFacts
      True True True True True False) == "stage-closure")
