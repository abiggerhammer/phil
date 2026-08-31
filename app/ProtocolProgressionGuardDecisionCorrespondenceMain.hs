module Main (main) where

import ProtocolProgressionGuardKernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "continuation accepts exact facts" $
        decideProtocolContinuationByFacts True True True == ProtocolContinuationAccepted
    , test "missing predecessor wins first" $
        decideProtocolContinuationByFacts False True True ==
          ProtocolContinuationPredecessorMissingDecision
    , test "same-name successor rejects" $
        decideProtocolContinuationByFacts True False True ==
          ProtocolContinuationSameNameDecision
    , test "occupied successor rejects" $
        decideProtocolContinuationByFacts True True False ==
          ProtocolContinuationSuccessorOccupiedDecision
    , test "live close accepts" $
        decideProtocolCloseByFact True == ProtocolCloseAccepted
    , test "stale close rejects" $
        decideProtocolCloseByFact False == ProtocolClosePredecessorMissingDecision
    , test "successor plan preserves exact coordinates" $
        case planProtocolSuccessorContract (11 :: Int) (22 :: Int) (33 :: Int) of
          MkProtocolSuccessorContractPlan instanceRevision role session ->
            instanceRevision == 11 && role == 22 && session == 33
    , test "unique guard list accepts" $
        decideProtocolGuardListByFact True == ProtocolGuardListAccepted
    , test "duplicate guard list rejects" $
        decideProtocolGuardListByFact False == ProtocolGuardListDuplicateDecision
    , test "present certified guard accepts" $
        decideProtocolGuardRequirementByFacts True True ==
          ProtocolGuardRequirementAccepted
    , test "missing guard revision wins first" $
        decideProtocolGuardRequirementByFacts False True ==
          ProtocolGuardRevisionMissingDecision
    , test "uncertified guard rejects" $
        decideProtocolGuardRequirementByFacts True False ==
          ProtocolGuardRevisionNotCertifiedDecision
    ]
  if and results then pure () else exitFailure

test :: String -> Bool -> IO Bool
test label ok = do
  putStrLn ((if ok then "PASS: " else "FAIL: ") <> label)
  pure ok
