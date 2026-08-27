{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Core.Context
  ( CheckError (..)
  , ResourceContext
  , consumeLinear
  , emptyContext
  , insertBinding
  , joinContinuing
  , useBinding
  )
import Phil.Core.Syntax (Mode (..), Name (Name), Ty (TyOpaque))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "DATA-013 raw branch-dependent linear state is rejected" rawBranchShapesRejected
    , test "DATA-013 explicit owning sum state reconverges" explicitOwningSumReconverges
    , test "DATA-013 joined owning sum remains linear" joinedOwningSumRemainsLinear
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

rawBranchShapesRejected :: Either String ()
rawBranchShapesRejected = do
  left <- mapLeft show $ insertBinding Linear leftName leftTy emptyContext
  right <- mapLeft show $ insertBinding Linear rightName rightTy emptyContext
  case joinContinuing [left, right] of
    Left (LinearBranchMismatch _ _) -> Right ()
    other -> Left ("join synthesized hidden branch-dependent state: " <> show other)

explicitOwningSumReconverges :: Either String ()
explicitOwningSumReconverges = do
  left <- packageBranch leftName leftTy
  right <- packageBranch rightName rightTy
  joined <- mapLeft show $ joinContinuing [left, right]
  (mode, ty, _) <- mapLeft show $ useBinding choiceName joined
  assert (mode == Linear) "explicit branch sum lost linearity"
  assert (ty == choiceTy) "explicit branch sum changed type at join"

joinedOwningSumRemainsLinear :: Either String ()
joinedOwningSumRemainsLinear = do
  left <- packageBranch leftName leftTy
  right <- packageBranch rightName rightTy
  joined <- mapLeft show $ joinContinuing [left, right]
  (_, _, afterUse) <- mapLeft show $ useBinding choiceName joined
  case useBinding choiceName afterUse of
    Left (UnknownBinding actual) ->
      assert (actual == choiceName) "wrong joined binding reported missing"
    other -> Left ("joined owning sum was reusable: " <> show other)

packageBranch :: Name -> Ty -> Either String ResourceContext
packageBranch localName localTy = do
  initial <- mapLeft show $ insertBinding Linear localName localTy emptyContext
  (_, afterConsume) <- mapLeft show $ consumeLinear localName initial
  mapLeft show $ insertBinding Linear choiceName choiceTy afterConsume

leftName, rightName, choiceName :: Name
leftName = Name "left_resource"
rightName = Name "right_resource"
choiceName = Name "branch_resource"

leftTy, rightTy, choiceTy :: Ty
leftTy = TyOpaque "OwnedLeft"
rightTy = TyOpaque "OwnedRight"
choiceTy = TyOpaque "BranchResource[OwnedLeft,OwnedRight]"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
