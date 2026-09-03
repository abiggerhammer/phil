module Main (main) where

import ResourceLoopKernel

assert :: String -> Bool -> IO ()
assert label condition =
  if condition
    then putStrLn ("PASS: " <> label)
    else fail ("FAIL: " <> label)

isLoopAccepted :: LoopProjectionDecision -> Bool
isLoopAccepted decision = case decision of
  LoopProjectionAcceptedDecision -> True
  _ -> False

isLoopKindFailure :: LoopProjectionDecision -> Bool
isLoopKindFailure decision = case decision of
  LoopProjectionKindDecision -> True
  _ -> False

isLoopResourceFailure :: LoopProjectionDecision -> Bool
isLoopResourceFailure decision = case decision of
  LoopProjectionResourceDecision -> True
  _ -> False

isLoopSlotDomainFailure :: LoopProjectionDecision -> Bool
isLoopSlotDomainFailure decision = case decision of
  LoopProjectionSlotDomainDecision -> True
  _ -> False

isLoopRequirementFailure :: LoopProjectionDecision -> Bool
isLoopRequirementFailure decision = case decision of
  LoopProjectionRequirementDecision -> True
  _ -> False

isTransportAccepted :: StateTransportDecision -> Bool
isTransportAccepted decision = case decision of
  StateTransportAcceptedDecision -> True
  _ -> False

isTransportEvidenceFailure :: StateTransportDecision -> Bool
isTransportEvidenceFailure decision = case decision of
  StateTransportExplicitEvidenceDecision -> True
  _ -> False

main :: IO ()
main = do
  assert "RES-LOOP accepts exact loop projection over bound Resource Join" $
    isLoopAccepted (decideLoopProjectionByFacts True True True True)
  assert "RES-LOOP reports wrong initial/backedge kind first" $
    isLoopKindFailure (decideLoopProjectionByFacts False True True True)
  assert "RES-LOOP reports Resource Join predecessor failure" $
    isLoopResourceFailure (decideLoopProjectionByFacts True False True True)
  assert "RES-LOOP rejects loop telescope slot-domain mismatch" $
    isLoopSlotDomainFailure (decideLoopProjectionByFacts True True False True)
  assert "RES-LOOP rejects loop telescope requirement mismatch" $
    isLoopRequirementFailure (decideLoopProjectionByFacts True True True False)

  assert "RES-LOOP accepts definitional state transport without evidence" $
    isTransportAccepted (decideStateTransportByFacts True False)
  assert "RES-LOOP accepts nondefinitional state transport with explicit evidence" $
    isTransportAccepted (decideStateTransportByFacts False True)
  assert "RES-LOOP rejects nondefinitional state transport without evidence" $
    isTransportEvidenceFailure (decideStateTransportByFacts False False)
