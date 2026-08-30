module Main (main) where

import ProtocolIdentityKernel

assert :: String -> Bool -> IO ()
assert label ok =
  if ok then pure () else error ("protocol identity correspondence failed: " <> label)

isContractAccepted :: ProtocolContractDecision -> Bool
isContractAccepted ProtocolContractAccepted = True
isContractAccepted _ = False

isContractInstanceMismatch :: ProtocolContractDecision -> Bool
isContractInstanceMismatch ProtocolContractInstanceMismatchDecision = True
isContractInstanceMismatch _ = False

isContractRoleMismatch :: ProtocolContractDecision -> Bool
isContractRoleMismatch ProtocolContractRoleMismatchDecision = True
isContractRoleMismatch _ = False

isContractSessionMismatch :: ProtocolContractDecision -> Bool
isContractSessionMismatch ProtocolContractSessionMismatchDecision = True
isContractSessionMismatch _ = False

isActionAccepted :: ProtocolActionDecision -> Bool
isActionAccepted ProtocolActionAccepted = True
isActionAccepted _ = False

isActionInstanceMismatch :: ProtocolActionDecision -> Bool
isActionInstanceMismatch ProtocolActionInstanceMismatchDecision = True
isActionInstanceMismatch _ = False

isActionRoleMismatch :: ProtocolActionDecision -> Bool
isActionRoleMismatch ProtocolActionRoleMismatchDecision = True
isActionRoleMismatch _ = False

isActionLocalStateRejected :: ProtocolActionDecision -> Bool
isActionLocalStateRejected ProtocolActionLocalStateRejectedDecision = True
isActionLocalStateRejected _ = False

exactPlan :: Bool
exactPlan =
  case planProtocolContract (11 :: Int) (22 :: Int) (33 :: Int) of
    MkProtocolContractPlan instanceRevision roleKey localSession ->
      instanceRevision == 11 && roleKey == 22 && localSession == 33

main :: IO ()
main = do
  assert "contract accepts exact identity"
    (isContractAccepted (decideProtocolContractByFacts True True True))
  assert "contract instance mismatch has precedence"
    (isContractInstanceMismatch (decideProtocolContractByFacts False False False))
  assert "contract role mismatch has second precedence"
    (isContractRoleMismatch (decideProtocolContractByFacts True False False))
  assert "contract session mismatch has third precedence"
    (isContractSessionMismatch (decideProtocolContractByFacts True True False))
  assert "action accepts exact identity and local-state admission"
    (isActionAccepted (decideProtocolActionByFacts True True True))
  assert "action instance mismatch has precedence"
    (isActionInstanceMismatch (decideProtocolActionByFacts False False False))
  assert "action role mismatch has second precedence"
    (isActionRoleMismatch (decideProtocolActionByFacts True False False))
  assert "action local-state rejection has third precedence"
    (isActionLocalStateRejected (decideProtocolActionByFacts True True False))
  assert "contract plan preserves exact three coordinates" exactPlan
