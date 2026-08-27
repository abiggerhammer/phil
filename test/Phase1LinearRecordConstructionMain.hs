{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Core.Context
  ( CheckError (..)
  , ResourceContext
  , consumeLinear
  , emptyContext
  , insertBinding
  , useBinding
  )
import Phil.Core.DataMode (deriveRecordMode)
import Phil.Core.Syntax (Mode (..), Name (Name), Ty (TyOpaque))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "DATA-002 linear field makes record linear" linearRecordMode
    , test "DATA-002 construction transfers predecessor owner" constructionTransfersOwner
    , test "DATA-002 aggregate remains uniquely owned" aggregateIsLinear
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

linearRecordMode :: Either String ()
linearRecordMode =
  assert (deriveRecordMode [Unrestricted, Linear] == Linear)
    "record owning a linear field did not derive Linear"

constructionTransfersOwner :: Either String ()
constructionTransfersOwner = do
  before <- mapLeft show $ insertBinding Linear payloadName payloadTy emptyContext
  (_, afterMove) <- mapLeft show $ consumeLinear payloadName before
  afterConstruct <- mapLeft show $ insertBinding Linear recordName recordTy afterMove
  case useBinding payloadName afterConstruct of
    Left (UnknownBinding actual) ->
      assert (actual == payloadName) "wrong predecessor binding reported missing"
    other -> Left ("predecessor owner remained usable after construction: " <> show other)

aggregateIsLinear :: Either String ()
aggregateIsLinear = do
  constructed <- constructRecord
  (mode, ty, afterUse) <- mapLeft show $ useBinding recordName constructed
  assert (mode == Linear) "aggregate binding was not linear"
  assert (ty == recordTy) "aggregate binding had the wrong type"
  case useBinding recordName afterUse of
    Left (UnknownBinding actual) ->
      assert (actual == recordName) "wrong aggregate binding reported missing"
    other -> Left ("linear aggregate was reusable after consumption: " <> show other)

constructRecord :: Either String ResourceContext
constructRecord = do
  before <- mapLeft show $ insertBinding Linear payloadName payloadTy emptyContext
  (_, afterMove) <- mapLeft show $ consumeLinear payloadName before
  mapLeft show $ insertBinding Linear recordName recordTy afterMove

payloadName, recordName :: Name
payloadName = Name "payload"
recordName = Name "packet"

payloadTy, recordTy :: Ty
payloadTy = TyOpaque "OwnedBytes[4]"
recordTy = TyOpaque "Packet"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
