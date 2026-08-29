module Main (main) where

import ArchitectureRealizationKernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "plan preserves exact architecture instance key"
        (assert (components "instance:k" "instance:r" "realization:s"
          == ("instance:k", "instance:r", "realization:s"))
          "realization plan changed one of its exact Certified coordinates")
    , test "plan preserves exact architecture instance revision"
        (assert (second (components "instance:k" "instance:r" "realization:s")
          == "instance:r")
          "realization plan lost the exact InstanceRevision")
    , test "plan preserves selected realization semantics"
        (assert (third (components "instance:k" "instance:r" "realization:s")
          == "realization:s")
          "realization plan lost the selected realization semantics")
    , test "changed selected realization changes plan coordinate"
        (assert (components "instance:k" "instance:r" "realization:prior"
          /= components "instance:k" "instance:r" "realization:replacement")
          "changed realization semantics collapsed in the construction plan")
    , test "changed abstract instance key changes plan coordinate"
        (assert (components "instance:prior" "instance:r" "realization:s"
          /= components "instance:replacement" "instance:r" "realization:s")
          "changed InstanceKey collapsed in the construction plan")
    , test "changed abstract instance revision changes plan coordinate"
        (assert (components "instance:k" "revision:prior" "realization:s"
          /= components "instance:k" "revision:replacement" "realization:s")
          "changed InstanceRevision collapsed in the construction plan")
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

components :: String -> String -> String -> (String, String, String)
components instanceKey instanceRevision semantics =
  case planArchitectureRealization instanceKey instanceRevision semantics of
    MkArchitectureRealizationPlan plannedKey plannedRevision plannedSemantics ->
      (plannedKey, plannedRevision, plannedSemantics)

second :: (a, b, c) -> b
second (_, value, _) = value

third :: (a, b, c) -> c
third (_, _, value) = value

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail
