module Main (main) where

import qualified ConcurrencyExecutionRealizationKernel as Kernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ check "process/decision group accepts exact facts"
        (Kernel.decideProcessDecisionRealizationByFacts True True True True True)
    , check "process/decision rejects missing process coverage"
        (not (Kernel.decideProcessDecisionRealizationByFacts False True True True True))
    , check "process/decision rejects empty execution identity"
        (not (Kernel.decideProcessDecisionRealizationByFacts True False True True True))
    , check "process/decision rejects missing decision coverage"
        (not (Kernel.decideProcessDecisionRealizationByFacts True True False True True))
    , check "process/decision rejects missing explicit cost"
        (not (Kernel.decideProcessDecisionRealizationByFacts True True True False True))
    , check "process/decision rejects hidden assumption"
        (not (Kernel.decideProcessDecisionRealizationByFacts True True True True False))

    , check "event/causality group accepts exact facts"
        (Kernel.decideEventCausalityRealizationByFacts True True True True)
    , check "event/causality rejects missing event coverage"
        (not (Kernel.decideEventCausalityRealizationByFacts False True True True))
    , check "event/causality rejects empty physical event identity"
        (not (Kernel.decideEventCausalityRealizationByFacts True False True True))
    , check "event/causality rejects physical event alias"
        (not (Kernel.decideEventCausalityRealizationByFacts True True False True))
    , check "event/causality rejects dropped causal path"
        (not (Kernel.decideEventCausalityRealizationByFacts True True True False))

    , check "semantic-preservation group accepts exact facts"
        (Kernel.decideSemanticPreservationRealizationByFacts True True True True True)
    , check "semantic-preservation rejects owner drift"
        (not (Kernel.decideSemanticPreservationRealizationByFacts False True True True True))
    , check "semantic-preservation rejects semantic fact drift"
        (not (Kernel.decideSemanticPreservationRealizationByFacts True False True True True))
    , check "semantic-preservation rejects undeclared stage fact"
        (not (Kernel.decideSemanticPreservationRealizationByFacts True True False True True))
    , check "semantic-preservation rejects terminal fact drift"
        (not (Kernel.decideSemanticPreservationRealizationByFacts True True True False True))
    , check "semantic-preservation rejects assumption-set drift"
        (not (Kernel.decideSemanticPreservationRealizationByFacts True True True True False))

    , check "trace group accepts exact facts"
        (Kernel.decideTraceRealizationByFacts True True True)
    , check "trace rejects missing process trace"
        (not (Kernel.decideTraceRealizationByFacts False True True))
    , check "trace rejects missing event trace"
        (not (Kernel.decideTraceRealizationByFacts True False True))
    , check "trace rejects missing physical-causality trace"
        (not (Kernel.decideTraceRealizationByFacts True True False))

    , check "outer realization accepts all four groups"
        (Kernel.decideProcessExecutionRealizationByFacts True True True True)
    , check "outer realization rejects process/decision disagreement"
        (not (Kernel.decideProcessExecutionRealizationByFacts False True True True))
    , check "outer realization rejects event/causality disagreement"
        (not (Kernel.decideProcessExecutionRealizationByFacts True False True True))
    , check "outer realization rejects semantic-preservation disagreement"
        (not (Kernel.decideProcessExecutionRealizationByFacts True True False True))
    , check "outer realization rejects trace disagreement"
        (not (Kernel.decideProcessExecutionRealizationByFacts True True True False))
    ]
  if and results then pure () else exitFailure

check :: String -> Bool -> IO Bool
check label accepted
  | accepted = putStrLn ("PASS: " <> label) >> pure True
  | otherwise = putStrLn ("FAIL: " <> label) >> pure False
