module Main (main) where

import qualified ConcurrencyTerminalKernel as Kernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "process terminal accepts exact closed boundary"
        (expect True (terminal True True True True))
    , test "process terminal rejects live resource/loan residue"
        (expect False (terminal False True True True))
    , test "process terminal rejects pending obligation"
        (expect False (terminal True False True True))
    , test "process terminal rejects live endpoint"
        (expect False (terminal True True False True))
    , test "process terminal rejects nonterminal control"
        (expect False (terminal True True True False))
    , test "failure isolation accepts exact actor/peer transition"
        (expect True (failure True True True))
    , test "failure isolation rejects actor not running"
        (expect False (failure False True True))
    , test "failure isolation rejects actor not failed"
        (expect False (failure True False True))
    , test "failure isolation rejects changed peer semantic state"
        (expect False (failure True True False))
    , test "root terminal accepts exact all-process closure"
        (expect True (rootTerminal True True True True True True))
    , test "root terminal rejects open root resource"
        (expect False (rootTerminal False True True True True True))
    , test "root terminal rejects open root obligation"
        (expect False (rootTerminal True False True True True True))
    , test "root terminal rejects pending root observable"
        (expect False (rootTerminal True True False True True True))
    , test "root terminal rejects missing static-process terminal fact"
        (expect False (rootTerminal True True True False True True))
    , test "root terminal rejects invented nonpopulation terminal fact"
        (expect False (rootTerminal True True True True False True))
    , test "root terminal rejects nonterminal static status"
        (expect False (rootTerminal True True True True True False))
    , test "stuck accepts running nonterminal network with no semantic step"
        (expect True (stuck True True True))
    , test "stuck rejects root-terminal network"
        (expect False (stuck False True True))
    , test "stuck rejects network with no running static process"
        (expect False (stuck True False True))
    , test "stuck rejects network with enabled semantic step"
        (expect False (stuck True True False))
    ]
  if and results then pure () else exitFailure

terminal :: Bool -> Bool -> Bool -> Bool -> Bool
terminal = Kernel.decideCertifiedProcessTerminalByFacts

failure :: Bool -> Bool -> Bool -> Bool
failure = Kernel.decideExactFailureIsolationByFacts

rootTerminal :: Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool
rootTerminal = Kernel.decideCertifiedRootTerminalByFacts

stuck :: Bool -> Bool -> Bool -> Bool
stuck = Kernel.decideCertifiedNetworkStuckByFacts

expect :: Bool -> Bool -> Either String ()
expect expected actual
  | expected == actual = Right ()
  | otherwise = Left ("expected " <> show expected <> ", got " <> show actual)

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False
