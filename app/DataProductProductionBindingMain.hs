{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Phil.Core.Context
  ( CheckError (..)
  , ResourceContext (..)
  , emptyContext
  , insertBinding
  , useBinding
  )
import Phil.Core.DataMode
  ( ProductError (..)
  , eliminateProductBinding
  , formProductBinding
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Name (..)
  , Ty (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "DATA-PRODUCT production exact elimination accepts" exactEliminationAccepts
    , test "DATA-PRODUCT production arity diagnostic preserved" arityDiagnosticPreserved
    , test "DATA-PRODUCT production duplicate-successor diagnostic preserved" duplicateDiagnosticPreserved
    , test "DATA-PRODUCT production preexisting-successor rejection remains native" preexistingSuccessorRejects
    , test "DATA-PRODUCT production restricted owner is consumed" restrictedOwnerConsumed
    , test "DATA-PRODUCT production exact successor contracts restored" exactSuccessorsRestored
    , test "DATA-PRODUCT production unrestricted product remains reusable" unrestrictedProductRemainsReusable
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactEliminationAccepts :: Either String ()
exactEliminationAccepts = do
  formed <- mixedProduct
  _ <- mapLeft show $
    eliminateProductBinding productName [metaOut, capOut, payloadOut] formed
  Right ()

arityDiagnosticPreserved :: Either String ()
arityDiagnosticPreserved = do
  formed <- linearProduct
  case eliminateProductBinding productName [] formed of
    Left (ProductArityMismatch 1 0) -> Right ()
    other -> Left ("wrong arity result: " <> show other)

duplicateDiagnosticPreserved :: Either String ()
duplicateDiagnosticPreserved = do
  formed <- mixedProduct
  case eliminateProductBinding productName [sameOut, sameOut, sameOut] formed of
    Left (ProductContextError (DuplicateBinding actual)) ->
      assert (actual == sameOut) "wrong duplicate successor reported"
    other -> Left ("wrong duplicate result: " <> show other)

preexistingSuccessorRejects :: Either String ()
preexistingSuccessorRejects = do
  formed <- linearProduct
  withCollision <- mapLeft show $
    insertBinding Unrestricted payloadOut metadataTy formed
  case eliminateProductBinding productName [payloadOut] withCollision of
    Left (ProductContextError (DuplicateBinding actual)) ->
      assert (actual == payloadOut) "wrong preexisting successor reported"
    other -> Left ("preexisting successor was accepted: " <> show other)

restrictedOwnerConsumed :: Either String ()
restrictedOwnerConsumed = do
  formed <- linearProduct
  eliminated <- mapLeft show $
    eliminateProductBinding productName [payloadOut] formed
  case useBinding productName eliminated of
    Left (UnknownBinding actual) ->
      assert (actual == productName) "wrong missing product reported"
    other -> Left ("restricted product owner remained usable: " <> show other)

exactSuccessorsRestored :: Either String ()
exactSuccessorsRestored = do
  formed <- mixedProduct
  eliminated <- mapLeft show $
    eliminateProductBinding productName [metaOut, capOut, payloadOut] formed
  assert (Map.lookup metaOut (unrestrictedBindings eliminated) == Just metadataTy)
    "unrestricted successor contract mismatch"
  assert (Map.lookup capOut (affineBindings eliminated) == Just capabilityTy)
    "affine successor contract mismatch"
  assert (Map.lookup payloadOut (linearBindings eliminated) == Just payloadTy)
    "linear successor contract mismatch"

unrestrictedProductRemainsReusable :: Either String ()
unrestrictedProductRemainsReusable = do
  withMeta <- mapLeft show $
    insertBinding Unrestricted metadataName metadataTy emptyContext
  (_, formed) <- mapLeft show $
    formProductBinding productName [metadataName] withMeta
  eliminated <- mapLeft show $
    eliminateProductBinding productName [metaOut] formed
  (firstMode, _, once) <- mapLeft show $ useBinding productName eliminated
  (secondMode, _, _) <- mapLeft show $ useBinding productName once
  assert (firstMode == Unrestricted && secondMode == Unrestricted)
    "unrestricted product did not remain reusable"

mixedProduct :: Either String ResourceContext
mixedProduct = do
  withMeta <- mapLeft show $
    insertBinding Unrestricted metadataName metadataTy emptyContext
  withCap <- mapLeft show $
    insertBinding Affine capabilityName capabilityTy withMeta
  withPayload <- mapLeft show $
    insertBinding Linear payloadName payloadTy withCap
  snd <$> mapLeft show
    (formProductBinding productName [metadataName, capabilityName, payloadName] withPayload)

linearProduct :: Either String ResourceContext
linearProduct = do
  withPayload <- mapLeft show $
    insertBinding Linear payloadName payloadTy emptyContext
  snd <$> mapLeft show (formProductBinding productName [payloadName] withPayload)

productName, metadataName, capabilityName, payloadName :: Name
productName = Name "product"
metadataName = Name "metadata"
capabilityName = Name "capability"
payloadName = Name "payload"

metaOut, capOut, payloadOut, sameOut :: Name
metaOut = Name "metadata.out"
capOut = Name "capability.out"
payloadOut = Name "payload.out"
sameOut = Name "same.out"

metadataTy, capabilityTy, payloadTy :: Ty
metadataTy = TyOpaque "Metadata"
capabilityTy = TyOpaque "Lease"
payloadTy = TyOpaque "OwnedBytes[4]"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
