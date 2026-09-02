module Main where

import qualified ResourceJoinKernel as Kernel
import System.Exit (exitFailure)

assert :: String -> Bool -> IO ()
assert label condition =
  if condition
    then putStrLn ("PASS: " <> label)
    else do
      putStrLn ("FAIL: " <> label)
      exitFailure

main :: IO ()
main = do
  assert "RES-JOIN accepts exact projection facts" $
    case Kernel.decideResourceProjectionByFacts True True True of
      Kernel.ResourceProjectionAcceptedDecision -> True
      _ -> False

  assert "RES-JOIN reports linear coverage/uniqueness first" $
    case Kernel.decideResourceProjectionByFacts False False False of
      Kernel.ResourceProjectionLinearCoverageDecision -> True
      _ -> False

  assert "RES-JOIN reports invented owner after linear coverage" $
    case Kernel.decideResourceProjectionByFacts True False False of
      Kernel.ResourceProjectionInventedOwnerDecision -> True
      _ -> False

  assert "RES-JOIN reports subject admission after owner conservation" $
    case Kernel.decideResourceProjectionByFacts True True False of
      Kernel.ResourceProjectionSubjectAdmissionDecision -> True
      _ -> False
