{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Core.Context
  ( CheckError (..)
  , ResourceContext
  , emptyContext
  , insertBinding
  , useBinding
  )
import Phil.Core.DataDestruction
  ( OwnedField (..)
  )
import Phil.Core.DataMode (deriveSumMode)
import Phil.Core.DataSum
  ( DataSumError (..)
  , SumConstructor (..)
  , checkContinuingSumArm
  , consumeSelectedSumPayload
  , joinPackagedSumContinuing
  , joinSumContinuing
  , selectSumConstructorPayload
  )
import Phil.Core.Syntax (Mode (..), Name (Name), Ty (TyOpaque))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "DATA-SUM production conservative mode reuses refined Data Mode" conservativeMode
    , test "DATA-SUM production declared constructor selects exact payload" declaredConstructorSelects
    , test "DATA-SUM production unknown constructor keeps native diagnostic" unknownConstructorRejects
    , test "DATA-SUM production consuming match restores selected linear payload" consumingLinearPayload
    , test "DATA-SUM production empty constructor manufactures no payload" emptyConstructor
    , test "DATA-SUM production live linear payload rejects continuing arm" livePayloadRejectsArm
    , test "DATA-SUM production consumed payload clears continuing arm" consumedPayloadClearsArm
    , test "DATA-SUM production raw branch-dependent state rejects" rawBranchShapesReject
    , test "DATA-SUM production explicit owning package reconverges" explicitPackageReconverges
    , test "DATA-SUM production joined explicit package remains linear" joinedPackageRemainsLinear
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

conservativeMode :: Either String ()
conservativeMode =
  assert (deriveSumMode [[Unrestricted], [Linear]] == Linear)
    "conservative sum mode was not linear"

declaredConstructorSelects :: Either String ()
declaredConstructorSelects = do
  payload <- mapLeft show $ selectSumConstructorPayload 0 constructors
  assert (payload == [payloadField]) "selected constructor payload changed"

unknownConstructorRejects :: Either String ()
unknownConstructorRejects =
  assert
    (selectSumConstructorPayload 99 constructors == Left (UnknownSumConstructor 99))
    "unknown constructor did not retain native diagnostic"

consumingLinearPayload :: Either String ()
consumingLinearPayload = do
  initial <- mapLeft show $ insertBinding Linear sumName sumTy emptyContext
  matched <- mapLeft show $ consumeSelectedSumPayload sumName 0 constructors initial
  case useBinding sumName matched of
    Left (UnknownBinding actual) ->
      assert (actual == sumName) "wrong sum aggregate reported missing"
    other -> Left ("sum aggregate remained usable: " <> show other)
  (mode, ty, afterUse) <- mapLeft show $ useBinding payloadName matched
  assert (mode == Linear && ty == payloadTy) "selected linear payload was not restored exactly"
  case useBinding payloadName afterUse of
    Left (UnknownBinding actual) ->
      assert (actual == payloadName) "wrong selected payload reported missing"
    other -> Left ("selected linear payload was reusable: " <> show other)

emptyConstructor :: Either String ()
emptyConstructor = do
  initial <- mapLeft show $ insertBinding Linear sumName sumTy emptyContext
  matched <- mapLeft show $ consumeSelectedSumPayload sumName 1 constructors initial
  case useBinding payloadName matched of
    Left (UnknownBinding actual) ->
      assert (actual == payloadName) "wrong absent payload reported"
    other -> Left ("empty constructor manufactured payload: " <> show other)

livePayloadRejectsArm :: Either String ()
livePayloadRejectsArm = do
  initial <- mapLeft show $ insertBinding Linear sumName sumTy emptyContext
  matched <- mapLeft show $ consumeSelectedSumPayload sumName 0 constructors initial
  case checkContinuingSumArm [payloadField] matched of
    Left (DataSumContextError (UnconsumedLinearResources _)) -> Right ()
    other -> Left ("live selected payload did not reject arm: " <> show other)

consumedPayloadClearsArm :: Either String ()
consumedPayloadClearsArm = do
  initial <- mapLeft show $ insertBinding Linear sumName sumTy emptyContext
  matched <- mapLeft show $ consumeSelectedSumPayload sumName 0 constructors initial
  (_, _, afterUse) <- mapLeft show $ useBinding payloadName matched
  mapLeft show $ checkContinuingSumArm [payloadField] afterUse

rawBranchShapesReject :: Either String ()
rawBranchShapesReject = do
  left <- mapLeft show $ insertBinding Linear leftName leftTy emptyContext
  right <- mapLeft show $ insertBinding Linear rightName rightTy emptyContext
  case joinSumContinuing [left, right] of
    Left (DataSumContextError (LinearBranchMismatch _ _)) -> Right ()
    other -> Left ("raw branch-dependent state was accepted: " <> show other)

explicitPackageReconverges :: Either String ()
explicitPackageReconverges = do
  left <- packageBranch leftName leftTy
  right <- packageBranch rightName rightTy
  _ <- mapLeft show $ joinPackagedSumContinuing choiceName choiceTy [left, right]
  Right ()

joinedPackageRemainsLinear :: Either String ()
joinedPackageRemainsLinear = do
  left <- packageBranch leftName leftTy
  right <- packageBranch rightName rightTy
  joined <- mapLeft show $ joinPackagedSumContinuing choiceName choiceTy [left, right]
  (mode, ty, afterUse) <- mapLeft show $ useBinding choiceName joined
  assert (mode == Linear && ty == choiceTy) "joined package changed mode or type"
  case useBinding choiceName afterUse of
    Left (UnknownBinding actual) ->
      assert (actual == choiceName) "wrong joined package reported missing"
    other -> Left ("joined explicit package was reusable: " <> show other)

packageBranch :: Name -> Ty -> Either String ResourceContext
packageBranch localName localTy = do
  initial <- mapLeft show $ insertBinding Linear localName localTy emptyContext
  (_, _, afterConsume) <- mapLeft show $ useBinding localName initial
  mapLeft show $ insertBinding Linear choiceName choiceTy afterConsume

constructors :: [SumConstructor]
constructors =
  [ SumConstructor 0 [payloadField]
  , SumConstructor 1 []
  , SumConstructor 2 [metadataField]
  ]

payloadField, metadataField :: OwnedField
payloadField = OwnedField payloadName Linear payloadTy
metadataField = OwnedField metadataName Unrestricted metadataTy

sumName, payloadName, metadataName, leftName, rightName, choiceName :: Name
sumName = Name "message"
payloadName = Name "payload"
metadataName = Name "tag"
leftName = Name "left_resource"
rightName = Name "right_resource"
choiceName = Name "branch_resource"

sumTy, payloadTy, metadataTy, leftTy, rightTy, choiceTy :: Ty
sumTy = TyOpaque "Message"
payloadTy = TyOpaque "OwnedBytes[4]"
metadataTy = TyOpaque "Tag"
leftTy = TyOpaque "OwnedLeft"
rightTy = TyOpaque "OwnedRight"
choiceTy = TyOpaque "BranchResource[OwnedLeft,OwnedRight]"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
