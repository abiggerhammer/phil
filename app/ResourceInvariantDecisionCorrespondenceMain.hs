module Main (main) where

import ResourceInvariantKernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "RES-INVARIANT accepts exact structural/witness/evidence facts"
        (isAccepted (decideInvariantBoundaryByFacts True True True True))
    , test "RES-INVARIANT reports duplicate predecessor first"
        (isDuplicate (decideInvariantBoundaryByFacts False False False False))
    , test "RES-INVARIANT reports structural projection failure"
        (isStructural (decideInvariantBoundaryByFacts True False True True))
    , test "RES-INVARIANT reports exact witness-domain failure"
        (isWitness (decideInvariantBoundaryByFacts True True False True))
    , test "RES-INVARIANT reports independent establishment failure"
        (isEstablishment (decideInvariantBoundaryByFacts True True True False))
    ]
  if and results then pure () else exitFailure

test :: String -> Bool -> IO Bool
test label condition = do
  putStrLn ((if condition then "PASS: " else "FAIL: ") <> label)
  pure condition

isAccepted :: InvariantBoundaryDecision -> Bool
isAccepted decision = case decision of
  InvariantBoundaryAcceptedDecision -> True
  _ -> False

isDuplicate :: InvariantBoundaryDecision -> Bool
isDuplicate decision = case decision of
  InvariantBoundaryDuplicatePredecessorDecision -> True
  _ -> False

isStructural :: InvariantBoundaryDecision -> Bool
isStructural decision = case decision of
  InvariantBoundaryStructuralDecision -> True
  _ -> False

isWitness :: InvariantBoundaryDecision -> Bool
isWitness decision = case decision of
  InvariantBoundaryWitnessDomainDecision -> True
  _ -> False

isEstablishment :: InvariantBoundaryDecision -> Bool
isEstablishment decision = case decision of
  InvariantBoundaryEstablishmentDecision -> True
  _ -> False
