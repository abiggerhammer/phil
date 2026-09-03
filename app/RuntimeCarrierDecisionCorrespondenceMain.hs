module Main (main) where

import qualified RuntimeCarrierKernel as Kernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "exact carrier binding accepts all exact facts" $
        exactBinding True True True True True True True True True True True True True
    , test "exact carrier binding rejects missing selected-use binding" $
        not (exactBinding False True True True True True True True True True True True True)
    , test "exact carrier binding rejects unknown carrier" $
        not (exactBinding True True False True True True True True True True True True True)
    , test "exact carrier binding rejects wrong carrier obligation" $
        not (exactBinding True True True True False True True True True True True True True)
    , test "exact carrier binding rejects wrong runtime-site evidence" $
        not (exactBinding True True True True True True False True True True True True True)
    , test "exact carrier binding rejects absent establishment site" $
        not (exactBinding True True True True True True True True False True True True True)
    , test "exact carrier binding rejects missing claim lineage" $
        not (exactBinding True True True True True True True True True False True True True)
    , test "exact carrier binding rejects incomplete runtime authority" $
        not (exactBinding True True True True True True True True True True True True False)
    , test "covered use accepts exact carrier binding" $
        Kernel.decideCoveredCarrierUseByFacts True
    , test "covered use rejects inexact carrier binding" $
        not (Kernel.decideCoveredCarrierUseByFacts False)
    , test "explicit boundary use accepts nonempty boundary" $
        Kernel.decideExplicitBoundaryCarrierUseByFacts True
    , test "explicit boundary use rejects empty boundary" $
        not (Kernel.decideExplicitBoundaryCarrierUseByFacts False)
    , test "preserved transition accepts exact carrier coverage" $
        Kernel.decidePreservedCarrierTransitionByFacts True True True True True
    , test "preserved transition rejects uncovered destination" $
        not (Kernel.decidePreservedCarrierTransitionByFacts True True True True False)
    , test "replacement transition accepts exact prior/next lineage" $
        Kernel.decideReplacedCarrierTransitionByFacts True True True True True True True True
    , test "replacement transition rejects unknown next carrier" $
        not (Kernel.decideReplacedCarrierTransitionByFacts True False True True True True True True)
    , test "closed transition accepts exact source plus closed destination" $
        Kernel.decideClosedCarrierTransitionByFacts True True True True True
    , test "closed transition rejects destination still RuntimeBound" $
        not (Kernel.decideClosedCarrierTransitionByFacts True True True True False)
    ]
  if and results then pure () else exitFailure

exactBinding
  :: Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool
  -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool
exactBinding = Kernel.decideExactCarrierBindingByFacts

test :: String -> Bool -> IO Bool
test label result = do
  putStrLn ((if result then "PASS: " else "FAIL: ") <> label)
  pure result
