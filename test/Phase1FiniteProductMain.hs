{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Phil.Core.Context
  ( CheckError (..)
  , ResourceContext (..)
  , emptyContext
  , ensureComplete
  , insertBinding
  , useBinding
  )
import Phil.Core.DataMode
  ( ProductError (..)
  , eliminateProductBinding
  , formProductBinding
  , productMode
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Name (..)
  , ProductElementType (..)
  , ProductValue (..)
  , Ty (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "DATA-015 product mode derives from owned elements" productModeDerives
    , test "DATA-015 formation transfers restricted owners" formationTransfersOwners
    , test "DATA-015 duplicate restricted source rejects" duplicateRestrictedSourceRejects
    , test "DATA-015 elimination restores exact elements" eliminationRestoresElements
    , test "DATA-015 missing successor rejects" missingSuccessorRejects
    , test "DATA-015 duplicate successor rejects" duplicateSuccessorRejects
    , test "DATA-015 linear product cannot be silently dropped" linearProductCannotDrop
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

productModeDerives :: Either String ()
productModeDerives = do
  assert
    (productMode
      [ ProductElementType Unrestricted metadataTy
      , ProductElementType Affine capabilityTy
      ] == Affine)
    "unrestricted+affine product did not derive affine mode"
  assert
    (productMode
      [ ProductElementType Unrestricted metadataTy
      , ProductElementType Linear payloadTy
      , ProductElementType Affine capabilityTy
      ] == Linear)
    "product containing a linear element did not derive linear mode"

formationTransfersOwners :: Either String ()
formationTransfersOwners = do
  initial <- mixedContext
  (ProductValue elements, formed) <- mapLeft show $
    formProductBinding productName [metadataName, capabilityName, payloadName] initial
  assert
    (elements ==
      [ ProductElementType Unrestricted metadataTy
      , ProductElementType Affine capabilityTy
      , ProductElementType Linear payloadTy
      ])
    "product value did not retain exact ordered element contracts"
  (_, _, afterMetadataUse) <- mapLeft show $ useBinding metadataName formed
  (_, _, _) <- mapLeft show $ useBinding metadataName afterMetadataUse
  expectUnknown capabilityName (useBinding capabilityName formed)
  expectUnknown payloadName (useBinding payloadName formed)
  assert
    (Map.lookup productName (linearBindings formed) == Just (TyProduct elements))
    "formed product was not inserted as the exact linear product type"

-- Reusing one linear source for two product slots is contraction and must fail.
duplicateRestrictedSourceRejects :: Either String ()
duplicateRestrictedSourceRejects = do
  initial <- mapLeft show $ insertBinding Linear payloadName payloadTy emptyContext
  case formProductBinding productName [payloadName, payloadName] initial of
    Left (ProductContextError (UnknownBinding actual)) ->
      assert (actual == payloadName) "wrong source reported for duplicate restricted use"
    other -> Left ("duplicate restricted source was accepted: " <> show other)

eliminationRestoresElements :: Either String ()
eliminationRestoresElements = do
  initial <- mixedContext
  (_, formed) <- mapLeft show $
    formProductBinding productName [metadataName, capabilityName, payloadName] initial
  eliminated <- mapLeft show $
    eliminateProductBinding productName [metadataOut, capabilityOut, payloadOut] formed
  expectUnknown productName (useBinding productName eliminated)
  (metadataMode1, metadataActualTy, once) <- mapLeft show $ useBinding metadataOut eliminated
  (metadataMode2, _, _) <- mapLeft show $ useBinding metadataOut once
  assert
    (metadataMode1 == Unrestricted && metadataMode2 == Unrestricted && metadataActualTy == metadataTy)
    "unrestricted product element was not restored as reusable unrestricted data"
  (capabilityMode, capabilityActualTy, afterCapability) <- mapLeft show $ useBinding capabilityOut eliminated
  assert
    (capabilityMode == Affine && capabilityActualTy == capabilityTy)
    "affine product element was not restored exactly"
  expectUnknown capabilityOut (useBinding capabilityOut afterCapability)
  (payloadMode, payloadActualTy, afterPayload) <- mapLeft show $ useBinding payloadOut eliminated
  assert
    (payloadMode == Linear && payloadActualTy == payloadTy)
    "linear product element was not restored exactly"
  expectUnknown payloadOut (useBinding payloadOut afterPayload)

missingSuccessorRejects :: Either String ()
missingSuccessorRejects = do
  initial <- mapLeft show $ insertBinding Linear payloadName payloadTy emptyContext
  (_, formed) <- mapLeft show $ formProductBinding productName [payloadName] initial
  case eliminateProductBinding productName [] formed of
    Left (ProductArityMismatch 1 0) -> Right ()
    other -> Left ("missing restricted successor was accepted: " <> show other)

duplicateSuccessorRejects :: Either String ()
duplicateSuccessorRejects = do
  initial <- mixedContext
  (_, formed) <- mapLeft show $
    formProductBinding productName [metadataName, capabilityName, payloadName] initial
  case eliminateProductBinding productName [sameOut, sameOut, sameOut] formed of
    Left (ProductContextError (DuplicateBinding actual)) ->
      assert (actual == sameOut) "wrong duplicate successor name reported"
    other -> Left ("duplicate successor bindings were accepted: " <> show other)

linearProductCannotDrop :: Either String ()
linearProductCannotDrop = do
  initial <- mapLeft show $ insertBinding Linear payloadName payloadTy emptyContext
  (_, formed) <- mapLeft show $ formProductBinding productName [payloadName] initial
  case ensureComplete formed of
    Left (UnconsumedLinearResources residue) ->
      assert
        (Map.member productName residue)
        "completion failure did not identify the live linear product owner"
    other -> Left ("linear product was silently droppable: " <> show other)

mixedContext :: Either String ResourceContext
mixedContext = do
  withMetadata <- mapLeft show $ insertBinding Unrestricted metadataName metadataTy emptyContext
  withCapability <- mapLeft show $ insertBinding Affine capabilityName capabilityTy withMetadata
  mapLeft show $ insertBinding Linear payloadName payloadTy withCapability

expectUnknown
  :: Name
  -> Either CheckError (Mode, Ty, ResourceContext)
  -> Either String ()
expectUnknown expected result = case result of
  Left (UnknownBinding actual) ->
    assert (actual == expected) "wrong missing binding reported"
  other -> Left ("binding unexpectedly remained usable: " <> show other)

productName, metadataName, capabilityName, payloadName :: Name
productName = Name "product"
metadataName = Name "metadata"
capabilityName = Name "capability"
payloadName = Name "payload"

metadataOut, capabilityOut, payloadOut, sameOut :: Name
metadataOut = Name "metadata.out"
capabilityOut = Name "capability.out"
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
