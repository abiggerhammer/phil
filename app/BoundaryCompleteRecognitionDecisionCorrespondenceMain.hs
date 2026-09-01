module Main (main) where

import BoundaryCompleteRecognitionKernel

main :: IO ()
main = do
  check "exact complete extent accepts"
    CompleteExpected
    (decideCompleteExtentByFacts False False False False)
  check "declared-negative extent rejects first"
    InvalidExpected
    (decideCompleteExtentByFacts True False False False)
  check "declared-negative precedence dominates all later facts"
    InvalidExpected
    (decideCompleteExtentByFacts True True True True)
  check "consumed-negative extent rejects second"
    InvalidExpected
    (decideCompleteExtentByFacts False True False False)
  check "consumed-negative precedence dominates trailing/past facts"
    InvalidExpected
    (decideCompleteExtentByFacts False True True True)
  check "trailing bytes classify exactly"
    TrailingExpected
    (decideCompleteExtentByFacts False False True False)
  check "trailing classification precedes past when both reflected facts are true"
    TrailingExpected
    (decideCompleteExtentByFacts False False True True)
  check "consumed-past-frame classifies exactly"
    PastExpected
    (decideCompleteExtentByFacts False False False True)

data ExpectedExtent
  = InvalidExpected
  | TrailingExpected
  | PastExpected
  | CompleteExpected

check :: String -> ExpectedExtent -> ExtentCheck -> IO ()
check label expected actual
  | matches expected actual = putStrLn ("PASS: " ++ label)
  | otherwise = error ("FAIL: " ++ label)

matches :: ExpectedExtent -> ExtentCheck -> Bool
matches expected actual = case (expected, actual) of
  (InvalidExpected, ExtentInvalid) -> True
  (TrailingExpected, ExtentTrailing) -> True
  (PastExpected, ExtentPast) -> True
  (CompleteExpected, ExtentComplete) -> True
  _ -> False
