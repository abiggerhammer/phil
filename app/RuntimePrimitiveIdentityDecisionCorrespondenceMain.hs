module Main (main) where

import qualified RuntimePrimitiveIdentityKernel as Kernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "target runtime primitive identity accepts exact physical/profile entry" $
        Kernel.decideRuntimePrimitiveIdentityByFacts True True
    , test "target runtime primitive identity rejects physical/profile entry drift" $
        not (Kernel.decideRuntimePrimitiveIdentityByFacts False True)
    , test "target runtime primitive identity rejects assurance-derived entry identity" $
        not (Kernel.decideRuntimePrimitiveIdentityByFacts True False)
    ]
  if and results then pure () else exitFailure

test :: String -> Bool -> IO Bool
test label accepted = do
  putStrLn ((if accepted then "PASS: " else "FAIL: ") <> label)
  pure accepted
