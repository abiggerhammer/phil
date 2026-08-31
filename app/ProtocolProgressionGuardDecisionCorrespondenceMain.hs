module Main (main) where

import ProtocolProgressionGuardKernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "continuation accepts exact facts" $
        case decideProtocolContinuationByFacts True True True of
          ProtocolContinuationAccepted -> True
          _ -> False
    , test "missing predecessor wins first" $
        case decideProtocolContinuationByFacts False True True of
          ProtocolContinuationPredecessorMissingDecision -> True
          _ -> False
    , test "same-name successor rejects" $
        case decideProtocolContinuationByFacts True False True of
          ProtocolContinuationSameNameDecision -> True
          _ -> False
    , test "occupied successor rejects" $
        case decideProtocolContinuationByFacts True True False of
          ProtocolContinuationSuccessorOccupiedDecision -> True
          _ -> False
    , test "live close accepts" $
        case decideProtocolCloseByFact True of
          ProtocolCloseAccepted -> True
          _ -> False
    , test "stale close rejects" $
        case decideProtocolCloseByFact False of
          ProtocolClosePredecessorMissingDecision -> True
          _ -> False
    , test "successor plan preserves exact coordinates" $
        case planProtocolSuccessorContract (11 :: Int) (22 :: Int) (33 :: Int) of
          MkProtocolSuccessorContractPlan instanceRevision role session ->
            instanceRevision == 11 && role == 22 && session == 33
    , test "unique guard list accepts" $
        case decideProtocolGuardListByFact True of
          ProtocolGuardListAccepted -> True
          _ -> False
    , test "duplicate guard list rejects" $
        case decideProtocolGuardListByFact False of
          ProtocolGuardListDuplicateDecision -> True
          _ -> False
    , test "present certified guard accepts" $
        case decideProtocolGuardRequirementByFacts True True of
          ProtocolGuardRequirementAccepted -> True
          _ -> False
    , test "missing guard revision wins first" $
        case decideProtocolGuardRequirementByFacts False True of
          ProtocolGuardRevisionMissingDecision -> True
          _ -> False
    , test "uncertified guard rejects" $
        case decideProtocolGuardRequirementByFacts True False of
          ProtocolGuardRevisionNotCertifiedDecision -> True
          _ -> False
    ]
  if and results then pure () else exitFailure

test :: String -> Bool -> IO Bool
test label ok = do
  putStrLn ((if ok then "PASS: " else "FAIL: ") <> label)
  pure ok
