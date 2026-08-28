{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Phil.Core.Context
  ( CheckError (..)
  , ResourceContext
  , emptyContext
  , ensureComplete
  , insertBinding
  , useBinding
  )
import Phil.Core.Syntax (Mode (..), Name (Name), Ty (TyOpaque))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "DATA-008 continuing arm rejects leaked linear payload" continuingArmRejectsLeak
    , test "DATA-008 continuing arm accepts after payload disposition" continuingArmAcceptsAfterDisposition
    , test "DATA-008 empty constructor has no fabricated linear residue" emptyConstructorHasNoResidue
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

continuingArmRejectsLeak :: Either String ()
continuingArmRejectsLeak = do
  matched <- matchLinearConstructor =<< initialSumContext
  case ensureComplete matched of
    Left (UnconsumedLinearResources residue) -> do
      assert
        (Map.lookup payloadName residue == Just payloadTy)
        "continuing-arm rejection did not identify the restored linear payload"
      assert
        (not (Map.member sumName residue))
        "consumed sum aggregate incorrectly remained in continuing-arm residue"
    other -> Left ("continuing arm with leaked linear payload was not rejected: " <> show other)

continuingArmAcceptsAfterDisposition :: Either String ()
continuingArmAcceptsAfterDisposition = do
  matched <- matchLinearConstructor =<< initialSumContext
  (mode, ty, afterPayload) <- mapLeft show $ useBinding payloadName matched
  assert (mode == Linear) "constructor payload was not restored as linear"
  assert (ty == payloadTy) "constructor payload was restored with the wrong type"
  mapLeft show $ ensureComplete afterPayload

emptyConstructorHasNoResidue :: Either String ()
emptyConstructorHasNoResidue = do
  matched <- matchEmptyConstructor =<< initialSumContext
  mapLeft show $ ensureComplete matched

initialSumContext :: Either String ResourceContext
initialSumContext = mapLeft show $ insertBinding Linear sumName sumTy emptyContext

matchLinearConstructor :: ResourceContext -> Either String ResourceContext
matchLinearConstructor context = do
  (_, _, afterSum) <- mapLeft show $ useBinding sumName context
  mapLeft show $ insertBinding Linear payloadName payloadTy afterSum

matchEmptyConstructor :: ResourceContext -> Either String ResourceContext
matchEmptyConstructor context = do
  (_, _, afterSum) <- mapLeft show $ useBinding sumName context
  pure afterSum

sumName, payloadName :: Name
sumName = Name "result"
payloadName = Name "bytes"

sumTy, payloadTy :: Ty
sumTy = TyOpaque "GetResult"
payloadTy = TyOpaque "OwnedBytes[n]"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
