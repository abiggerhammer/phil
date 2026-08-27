{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Core.DataMode (deriveSumMode)
import Phil.Core.Syntax (Mode (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "DATA-007 unrestricted-only sum remains unrestricted"
        (deriveSumMode [[Unrestricted], []] == Unrestricted)
    , test "DATA-007 affine constructor raises whole sum to affine"
        (deriveSumMode [[Unrestricted], [Affine]] == Affine)
    , test "DATA-007 linear constructor makes whole sum linear"
        (deriveSumMode [[], [Linear]] == Linear)
    , test "DATA-007 constructor without restricted payload does not weaken linear sum"
        (deriveSumMode [[Linear], []] == Linear)
    ]
  if and results then pure () else exitFailure

test :: String -> Bool -> IO Bool
test label ok = do
  putStrLn ((if ok then "PASS: " else "FAIL: ") <> label)
  pure ok
