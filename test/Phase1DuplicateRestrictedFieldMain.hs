{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Core.Context
  ( CheckError (..)
  , consumeLinear
  , emptyContext
  , insertBinding
  )
import Phil.Core.Syntax (Mode (..), Name (Name), Ty (TyOpaque))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "DATA-003 first owning field consumes restricted occurrence" firstFieldConsumes
    , test "DATA-003 second owning field cannot reuse same occurrence" duplicateFieldRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

firstFieldConsumes :: Either String ()
firstFieldConsumes = do
  before <- mapLeft show $ insertBinding Linear ownerName ownerTy emptyContext
  (_, afterFirst) <- mapLeft show $ consumeLinear ownerName before
  case consumeLinear ownerName afterFirst of
    Left (UnknownBinding actual) ->
      assert (actual == ownerName) "wrong restricted occurrence reported missing"
    other -> Left ("restricted occurrence unexpectedly reusable: " <> show other)

duplicateFieldRejects :: Either String ()
duplicateFieldRejects = do
  before <- mapLeft show $ insertBinding Linear ownerName ownerTy emptyContext
  (_, afterFirst) <- mapLeft show $ consumeLinear ownerName before
  case consumeLinear ownerName afterFirst of
    Left (UnknownBinding actual) ->
      assert (actual == ownerName) "duplicate field did not fail on consumed owner"
    other -> Left ("same restricted owner satisfied two fields: " <> show other)

ownerName :: Name
ownerName = Name "payload"

ownerTy :: Ty
ownerTy = TyOpaque "OwnedBytes[4]"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
