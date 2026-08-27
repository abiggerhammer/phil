module Main (main) where

import Phil.Core.DataMode
  ( ModeExpr (..)
  , instantiateMode
  )
import Phil.Core.Syntax (Mode (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "DATA-009 Option<unrestricted> is unrestricted" $ expectMode Unrestricted [("T", Unrestricted)] optionMode
    , test "DATA-009 Option<affine> is affine" $ expectMode Affine [("T", Affine)] optionMode
    , test "DATA-009 Option<linear> is linear" $ expectMode Linear [("T", Linear)] optionMode
    , test "DATA-009 independent unrestricted field does not weaken generic owner" $ expectMode Linear [("T", Linear)] genericRecordMode
    , test "DATA-009 unknown generic mode fails closed" unknownParameterFailsClosed
    ]
  if and results then pure () else exitFailure

optionMode :: ModeExpr
optionMode = StrongestMode
  [ FixedMode Unrestricted
  , ParameterMode "T"
  ]

genericRecordMode :: ModeExpr
genericRecordMode = StrongestMode
  [ FixedMode Unrestricted
  , ParameterMode "T"
  ]

expectMode :: Mode -> [(String, Mode)] -> ModeExpr -> Either String ()
expectMode expected environment expression = do
  actual <- instantiateMode environment expression
  assert (actual == expected) ("expected " <> show expected <> ", got " <> show actual)

unknownParameterFailsClosed :: Either String ()
unknownParameterFailsClosed = case instantiateMode [] optionMode of
  Left detail -> assert (detail == "unknown generic mode parameter: T") "wrong unknown-parameter diagnostic"
  Right actual -> Left ("unbound T was silently assigned mode " <> show actual)

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail
