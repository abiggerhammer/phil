module Main where

import qualified SystemsRuntimeGraphKernel as Kernel
import System.Exit (exitFailure)

assert :: String -> Bool -> IO ()
assert label condition =
  if condition
    then putStrLn ("PASS: " <> label)
    else do
      putStrLn ("FAIL: " <> label)
      exitFailure

claimTag :: Kernel.RuntimeClaimGraphDecision -> String
claimTag decision = case decision of
  Kernel.RuntimeClaimGraphAcceptedDecision -> "accepted"
  Kernel.RuntimeClaimGraphSiteVerificationDecision -> "site"

reuseTag :: Kernel.RuntimePrimitiveReuseDecision -> String
reuseTag decision = case decision of
  Kernel.RuntimePrimitiveReuseAcceptedDecision -> "accepted"
  Kernel.RuntimePrimitiveReuseContributionIdentityDecision -> "contribution"
  Kernel.RuntimePrimitiveReuseSymbolIdentityDecision -> "symbol"

costTag :: Kernel.RuntimeCostAttributionDecision -> String
costTag decision = case decision of
  Kernel.RuntimeCostAttributionAcceptedDecision -> "accepted"
  Kernel.RuntimeCostAttributionClassDecision -> "class"
  Kernel.RuntimeCostAttributionShapeDecision -> "shape"

graphTag :: Kernel.SystemsRuntimeGraphDecision -> String
graphTag decision = case decision of
  Kernel.SystemsRuntimeGraphAcceptedDecision -> "accepted"
  Kernel.SystemsRuntimeGraphClaimGraphDecision -> "claim"
  Kernel.SystemsRuntimeGraphPrimitiveReuseDecision -> "reuse"
  Kernel.SystemsRuntimeGraphCostAttributionDecision -> "cost"

main :: IO ()
main = do
  assert "SYS-015 accepts verified runtime sites"
    (claimTag (Kernel.decideRuntimeClaimGraphByFacts True) == "accepted")
  assert "SYS-015 rejects an unverified runtime site surface"
    (claimTag (Kernel.decideRuntimeClaimGraphByFacts False) == "site")

  assert "SYS-016 accepts separated contributions and verified symbols"
    (reuseTag (Kernel.decideRuntimePrimitiveReuseByFacts True True) == "accepted")
  assert "SYS-016 requires site-owned contribution identity"
    (reuseTag (Kernel.decideRuntimePrimitiveReuseByFacts False True) == "contribution")
  assert "SYS-016 requires verified physical runtime-symbol identity"
    (reuseTag (Kernel.decideRuntimePrimitiveReuseByFacts True False) == "symbol")

  assert "SYS-018 accepts exact shared-charge compatibility"
    (costTag (Kernel.decideRuntimeCostAttributionByFacts True True) == "accepted")
  assert "SYS-018 requires exact shared-charge cost class"
    (costTag (Kernel.decideRuntimeCostAttributionByFacts False True) == "class")
  assert "SYS-018 requires exact shared-charge cost shape"
    (costTag (Kernel.decideRuntimeCostAttributionByFacts True False) == "shape")

  assert "runtime graph cumulative decision accepts all three Certified surfaces"
    (graphTag (Kernel.decideSystemsRuntimeGraphByFacts True True True) == "accepted")
  assert "runtime graph cumulative decision requires SYS-015"
    (graphTag (Kernel.decideSystemsRuntimeGraphByFacts False True True) == "claim")
  assert "runtime graph cumulative decision requires SYS-016"
    (graphTag (Kernel.decideSystemsRuntimeGraphByFacts True False True) == "reuse")
  assert "runtime graph cumulative decision requires SYS-018"
    (graphTag (Kernel.decideSystemsRuntimeGraphByFacts True True False) == "cost")
