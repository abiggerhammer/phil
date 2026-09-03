module Main (main) where

import ResourceObligationKernel

assert :: String -> Bool -> IO ()
assert label condition =
  if condition
    then putStrLn ("PASS: " <> label)
    else fail ("FAIL: " <> label)

isAccepted :: PendingObligationDecision -> Bool
isAccepted decision = case decision of
  PendingObligationAcceptedDecision -> True
  _ -> False

isLost :: PendingObligationDecision -> Bool
isLost decision = case decision of
  PendingObligationLostDecision -> True
  _ -> False

main :: IO ()
main = do
  assert "RES-OBL accepts pending obligation preserved across reconvergence" $
    isAccepted (decidePendingObligationReconvergenceByFacts True True)
  assert "RES-OBL rejects pending obligation lost at reconvergence" $
    isLost (decidePendingObligationReconvergenceByFacts True False)
  assert "RES-OBL accepts non-pending to pending because no unresolved input was lost" $
    isAccepted (decidePendingObligationReconvergenceByFacts False True)
  assert "RES-OBL accepts non-pending to non-pending because no unresolved input was lost" $
    isAccepted (decidePendingObligationReconvergenceByFacts False False)
