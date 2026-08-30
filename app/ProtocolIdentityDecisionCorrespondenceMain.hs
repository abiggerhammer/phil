module Main (main) where

import ProtocolIdentityKernel

main :: IO ()
main = mapM_ run controls
  where
    run (label, condition)
      | condition = putStrLn ("PASS: " <> label)
      | otherwise = error ("FAIL: " <> label)

controls :: [(String, Bool)]
controls =
  [ ("contract accepts exact identity", decideProtocolContractByFacts True True True == ProtocolContractAccepted)
  , ("contract instance mismatch has precedence", decideProtocolContractByFacts False False False == ProtocolContractInstanceMismatchDecision)
  , ("contract role mismatch has second precedence", decideProtocolContractByFacts True False False == ProtocolContractRoleMismatchDecision)
  , ("contract session mismatch has third precedence", decideProtocolContractByFacts True True False == ProtocolContractSessionMismatchDecision)
  , ("action accepts exact identity and local-state admission", decideProtocolActionByFacts True True True == ProtocolActionAccepted)
  , ("action instance mismatch has precedence", decideProtocolActionByFacts False False False == ProtocolActionInstanceMismatchDecision)
  , ("action role mismatch has second precedence", decideProtocolActionByFacts True False False == ProtocolActionRoleMismatchDecision)
  , ("action local-state rejection has third precedence", decideProtocolActionByFacts True True False == ProtocolActionLocalStateRejectedDecision)
  , ("contract plan preserves exact three coordinates", exactPlan)
  ]

exactPlan :: Bool
exactPlan =
  case planProtocolContract (11 :: Int) (22 :: Int) (33 :: Int) of
    MkProtocolContractPlan instanceRevision roleKey localSession ->
      instanceRevision == 11 && roleKey == 22 && localSession == 33
