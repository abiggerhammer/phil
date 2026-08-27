{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Core.Context
  ( CheckError (..)
  , ResourceContext
  , emptyContext
  , insertBinding
  , useBinding
  )
import Phil.Core.Syntax (Mode (..), Name (Name), Ty (TyOpaque))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "DATA-008 linear constructor restores one owner" linearConstructorRestoresOwner
    , test "DATA-008 empty constructor manufactures no owner" emptyConstructorRestoresNothing
    , test "DATA-008 unrestricted payload remains unrestricted" unrestrictedPayloadRemainsReusable
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

linearConstructorRestoresOwner :: Either String ()
linearConstructorRestoresOwner = do
  matched <- matchLinearConstructor =<< initialSumContext
  case useBinding sumName matched of
    Left (UnknownBinding actual) -> assert (actual == sumName) "wrong aggregate binding remained after consuming match"
    other -> Left ("sum aggregate remained usable after consuming match: " <> show other)
  (mode, ty, afterUse) <- mapLeft show $ useBinding payloadName matched
  assert (mode == Linear) "restored payload was not linear"
  assert (ty == payloadTy) "restored payload had wrong type"
  case useBinding payloadName afterUse of
    Left (UnknownBinding actual) -> assert (actual == payloadName) "wrong payload binding reported missing"
    other -> Left ("restored linear payload was reusable: " <> show other)

emptyConstructorRestoresNothing :: Either String ()
emptyConstructorRestoresNothing = do
  matched <- matchEmptyConstructor =<< initialSumContext
  case useBinding payloadName matched of
    Left (UnknownBinding actual) -> assert (actual == payloadName) "wrong absent payload binding reported"
    other -> Left ("empty constructor manufactured payload ownership: " <> show other)

unrestrictedPayloadRemainsReusable :: Either String ()
unrestrictedPayloadRemainsReusable = do
  matched <- matchMetadataConstructor =<< initialMetadataSumContext
  (firstMode, _, once) <- mapLeft show $ useBinding metadataName matched
  (secondMode, _, _) <- mapLeft show $ useBinding metadataName once
  assert (firstMode == Unrestricted && secondMode == Unrestricted) "unrestricted constructor payload did not remain reusable"

initialSumContext :: Either String ResourceContext
initialSumContext = mapLeft show $ insertBinding Linear sumName sumTy emptyContext

initialMetadataSumContext :: Either String ResourceContext
initialMetadataSumContext = mapLeft show $ insertBinding Linear sumName sumTy emptyContext

matchLinearConstructor :: ResourceContext -> Either String ResourceContext
matchLinearConstructor context = do
  (_, _, afterConsume) <- mapLeft show $ useBinding sumName context
  mapLeft show $ insertBinding Linear payloadName payloadTy afterConsume

matchEmptyConstructor :: ResourceContext -> Either String ResourceContext
matchEmptyConstructor context = do
  (_, _, afterConsume) <- mapLeft show $ useBinding sumName context
  pure afterConsume

matchMetadataConstructor :: ResourceContext -> Either String ResourceContext
matchMetadataConstructor context = do
  (_, _, afterConsume) <- mapLeft show $ useBinding sumName context
  mapLeft show $ insertBinding Unrestricted metadataName metadataTy afterConsume

sumName, payloadName, metadataName :: Name
sumName = Name "message"
payloadName = Name "payload"
metadataName = Name "tag"

sumTy, payloadTy, metadataTy :: Ty
sumTy = TyOpaque "Message"
payloadTy = TyOpaque "OwnedBytes[4]"
metadataTy = TyOpaque "Tag"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
