module Main (main) where

import SystemsRevisionCanonicalizationKernel

main :: IO ()
main = do
  case planSystemsArtifactRevision
      "source-semantics" "program-semantics" "stage-contract-semantics" "lowering-semantics" of
    MkSystemsArtifactRevisionPlan
        SystemsArtifactRevisionNamespace source program stageContract lowering -> do
      assert (source == "source-semantics") "SYS-REV Systems source coordinate"
      assert (program == "program-semantics") "SYS-REV Systems program coordinate"
      assert (stageContract == "stage-contract-semantics") "SYS-REV Systems StageContract coordinate"
      assert (lowering == "lowering-semantics") "SYS-REV Systems lowering coordinate"
    _ -> fail "SYS-REV Systems revision namespace"
  pass "SYS-REV Systems revision construction plan"

  case planPhase1StageContractRevision
      "instance-revision"
      "realization-revision"
      "systems-revision"
      "verifier-profile"
      "source-facts"
      "dispositions"
      "mechanisms"
      "justifications" of
    MkPhase1StageContractRevisionPlan
        Phase1StageContractRevisionNamespace
        instanceValue realization systems profile facts dispositions mechanisms justifications -> do
      assert (instanceValue == "instance-revision") "SYS-REV Stage instance coordinate"
      assert (realization == "realization-revision") "SYS-REV Stage realization coordinate"
      assert (systems == "systems-revision") "SYS-REV Stage Systems coordinate"
      assert (profile == "verifier-profile") "SYS-REV Stage verifier-profile coordinate"
      assert (facts == "source-facts") "SYS-REV Stage source-facts coordinate"
      assert (dispositions == "dispositions") "SYS-REV Stage dispositions coordinate"
      assert (mechanisms == "mechanisms") "SYS-REV Stage mechanisms coordinate"
      assert (justifications == "justifications") "SYS-REV Stage justifications coordinate"
    _ -> fail "SYS-REV StageContract revision namespace"
  pass "SYS-REV StageContract revision construction plan"

assert :: Bool -> String -> IO ()
assert True label = pass label
assert False label = fail label

pass :: String -> IO ()
pass label = putStrLn ("PASS: " <> label)
