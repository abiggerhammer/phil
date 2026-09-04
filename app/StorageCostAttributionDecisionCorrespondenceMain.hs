module Main (main) where

import qualified StorageCostAttributionKernel as Kernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "subject exact accepts" True
        (Kernel.decideStorageCostSubjectExactByFacts True)
    , test "subject mismatch rejects" False
        (Kernel.decideStorageCostSubjectExactByFacts False)
    , test "physical domain exact accepts" True
        (Kernel.decideStorageCostPhysicalDomainExactByFacts True)
    , test "physical domain mismatch rejects" False
        (Kernel.decideStorageCostPhysicalDomainExactByFacts False)
    , test "allocation count is attributable" True
        (attributable True False False False False)
    , test "peak live memory is attributable" True
        (attributable False True False False False)
    , test "bytes copied is attributable" True
        (attributable False False True False False)
    , test "residency ref is attributable" True
        (attributable False False False True False)
    , test "cleanup ref is attributable" True
        (attributable False False False False True)
    , test "missing attribution rejects" False
        (attributable False False False False False)
    , test "lineage accepts exact attributable facts" True
        (lineage True True True)
    , test "lineage rejects subject mismatch" False
        (lineage False True True)
    , test "lineage rejects physical-domain mismatch" False
        (lineage True False True)
    , test "lineage rejects missing attribution" False
        (lineage True True False)
    , test "runtime binding accepts exact contribution/charge/class/shape" True
        (binding True True True)
    , test "runtime binding rejects missing charge membership" False
        (binding False True True)
    , test "runtime binding rejects class mismatch" False
        (binding True False True)
    , test "runtime binding rejects shape mismatch" False
        (binding True True False)
    , test "certified composition accepts all predecessors" True
        (certified True True True)
    , test "certified composition rejects realization failure" False
        (certified False True True)
    , test "certified composition rejects runtime graph failure" False
        (certified True False True)
    , test "certified composition rejects lineage failure" False
        (certified True True False)
    ]
  if and results then pure () else exitFailure

attributable :: Bool -> Bool -> Bool -> Bool -> Bool -> Bool
attributable = Kernel.decideAttributableStorageCostByFacts

lineage :: Bool -> Bool -> Bool -> Bool
lineage = Kernel.decideStorageCostLineageValidByFacts

binding :: Bool -> Bool -> Bool -> Bool
binding = Kernel.decideStorageRuntimeCostBindingByFacts

certified :: Bool -> Bool -> Bool -> Bool
certified = Kernel.decideCertifiedStorageCostAttributionByFacts

test :: String -> Bool -> Bool -> IO Bool
test label expected actual
  | expected == actual = putStrLn ("PASS: " <> label) >> pure True
  | otherwise = do
      putStrLn ("FAIL: " <> label <> " -- expected " <> show expected
        <> ", got " <> show actual)
      pure False
