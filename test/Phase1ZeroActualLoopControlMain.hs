{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Surface.Check.LoopControl
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "RES-014 bare continue supplies zero actuals" bareContinueZeroAccepts
    , test "RES-014 empty continue supplies zero actuals" emptyContinueZeroAccepts
    , test "RES-014 explicit continue supplies exact state actuals" explicitContinueStateAccepts
    , test "RES-014 bare continue cannot capture nonempty state" bareContinueStateRejects
    , test "RES-014 empty continue cannot capture nonempty state" emptyContinueStateRejects
    , test "RES-014 bare break supplies zero actuals" bareBreakZeroAccepts
    , test "RES-014 empty break supplies zero actuals" emptyBreakZeroAccepts
    , test "RES-014 explicit break supplies exact exit actuals" explicitBreakExitAccepts
    , test "RES-014 bare break cannot export current state" bareBreakExitRejects
    , test "RES-014 empty break cannot export current state" emptyBreakExitRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

zeroContract :: LoopControlContract
zeroContract = LoopControlContract [] []

statefulContract :: LoopControlContract
statefulContract = LoopControlContract ["i", "payload"] ["result"]

bareContinueZeroAccepts :: Either String ()
bareContinueZeroAccepts =
  expectActuals [] $ elaborateLoopControl ContinueControl zeroContract BareLoopControl

emptyContinueZeroAccepts :: Either String ()
emptyContinueZeroAccepts =
  expectActuals [] $ elaborateLoopControl ContinueControl zeroContract EmptyLoopControl

explicitContinueStateAccepts :: Either String ()
explicitContinueStateAccepts =
  expectActuals [1 :: Int, 2] $
    elaborateLoopControl ContinueControl statefulContract (ExplicitLoopControl [1, 2])

bareContinueStateRejects :: Either String ()
bareContinueStateRejects =
  expectArityError ContinueControl 2 0 $
    elaborateLoopControl ContinueControl statefulContract (BareLoopControl :: LoopControlSyntax Int)

emptyContinueStateRejects :: Either String ()
emptyContinueStateRejects =
  expectArityError ContinueControl 2 0 $
    elaborateLoopControl ContinueControl statefulContract (EmptyLoopControl :: LoopControlSyntax Int)

bareBreakZeroAccepts :: Either String ()
bareBreakZeroAccepts =
  expectActuals [] $ elaborateLoopControl BreakControl zeroContract BareLoopControl

emptyBreakZeroAccepts :: Either String ()
emptyBreakZeroAccepts =
  expectActuals [] $ elaborateLoopControl BreakControl zeroContract EmptyLoopControl

explicitBreakExitAccepts :: Either String ()
explicitBreakExitAccepts =
  expectActuals [7 :: Int] $
    elaborateLoopControl BreakControl statefulContract (ExplicitLoopControl [7])

bareBreakExitRejects :: Either String ()
bareBreakExitRejects =
  expectArityError BreakControl 1 0 $
    elaborateLoopControl BreakControl statefulContract (BareLoopControl :: LoopControlSyntax Int)

emptyBreakExitRejects :: Either String ()
emptyBreakExitRejects =
  expectArityError BreakControl 1 0 $
    elaborateLoopControl BreakControl statefulContract (EmptyLoopControl :: LoopControlSyntax Int)

expectActuals :: (Eq a, Show a) => [a] -> Either LoopControlError [a] -> Either String ()
expectActuals expected result = case result of
  Right actual
    | actual == expected -> Right ()
    | otherwise -> Left ("expected actuals " <> show expected <> ", got " <> show actual)
  Left errorValue -> Left ("unexpected rejection: " <> show errorValue)

expectArityError
  :: LoopControlKind
  -> Int
  -> Int
  -> Either LoopControlError [a]
  -> Either String ()
expectArityError expectedKind expectedArity actualArity result = case result of
  Left (LoopControlArityMismatch kind expected actual)
    | kind == expectedKind && expected == expectedArity && actual == actualArity -> Right ()
    | otherwise -> Left ("unexpected arity rejection: " <> show (kind, expected, actual))
  Right _ -> Left "expected loop-control arity rejection"
