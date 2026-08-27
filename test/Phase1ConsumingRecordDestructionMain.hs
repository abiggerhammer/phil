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
import Phil.Core.Syntax (Mode (..), Name (Name), Ty (TyOpaque))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "DATA-004 consuming destruction consumes aggregate" destructionConsumesAggregate
    , test "DATA-004 destruction restores exact successor owner" destructionRestoresLinearField
    , test "DATA-004 unrestricted field remains unrestricted" destructionRestoresUnrestrictedField
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

destructionConsumesAggregate :: Either String ()
destructionConsumesAggregate = do
  after <- destructRecord =<< constructedRecord
  case useBinding recordName after of
    Left (UnknownBinding actual) ->
      assert (actual == recordName) "wrong aggregate binding reported missing"
    other -> Left ("aggregate remained usable after consuming destruction: " <> show other)

destructionRestoresLinearField :: Either String ()
destructionRestoresLinearField = do
  after <- destructRecord =<< constructedRecord
  (mode, ty, afterUse) <- mapLeft show $ useBinding payloadName after
  assert (mode == Linear) "restored payload was not linear"
  assert (ty == payloadTy) "restored payload had wrong type"
  case useBinding payloadName afterUse of
    Left (UnknownBinding actual) ->
      assert (actual == payloadName) "wrong restored payload reported missing"
    other -> Left ("restored linear payload was reusable: " <> show other)

destructionRestoresUnrestrictedField :: Either String ()
destructionRestoresUnrestrictedField = do
  after <- destructRecord =<< constructedRecord
  (mode1, ty1, afterFirst) <- mapLeft show $ useBinding metadataName after
  (mode2, ty2, _) <- mapLeft show $ useBinding metadataName afterFirst
  assert (mode1 == Unrestricted && mode2 == Unrestricted)
    "restored metadata was not unrestricted"
  assert (ty1 == metadataTy && ty2 == metadataTy)
    "restored metadata had wrong type"

constructedRecord :: Either String ResourceContext
constructedRecord = do
  initial <- mapLeft show $ insertBinding Linear payloadName payloadTy emptyContext
  (_, afterPayloadMove) <- mapLeft show $ consumeLinear payloadName initial
  mapLeft show $ insertBinding Linear recordName recordTy afterPayloadMove

destructRecord :: ResourceContext -> Either String ResourceContext
destructRecord before = do
  (_, afterRecordConsume) <- mapLeft show $ consumeLinear recordName before
  withPayload <- mapLeft show $ insertBinding Linear payloadName payloadTy afterRecordConsume
  mapLeft show $ insertBinding Unrestricted metadataName metadataTy withPayload

payloadName, metadataName, recordName :: Name
payloadName = Name "payload"
metadataName = Name "tag"
recordName = Name "packet"

payloadTy, metadataTy, recordTy :: Ty
payloadTy = TyOpaque "OwnedBytes[4]"
metadataTy = TyOpaque "UInt[8]"
recordTy = TyOpaque "Packet"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
