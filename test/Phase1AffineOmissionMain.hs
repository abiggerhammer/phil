{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Core.DataDestruction
  ( FieldDisposition (..)
  , OwnedField (..)
  , checkFieldDispositions
  )
import Phil.Core.Syntax (Mode (..), Name (Name), Ty (TyOpaque))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "DATA-006 affine owned field may be omitted" affineOmissionAccepts
    , test "DATA-006 affine owned field may also be bound" affineBindingAccepts
    , test "DATA-006 mixed affine omission and linear binding accepts" mixedDispositionAccepts
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

affineOmissionAccepts :: Either String ()
affineOmissionAccepts =
  mapLeft show $ checkFieldDispositions
    [affineField]
    [(affineName, FieldOmitted)]

affineBindingAccepts :: Either String ()
affineBindingAccepts =
  mapLeft show $ checkFieldDispositions
    [affineField]
    [(affineName, FieldBound)]

mixedDispositionAccepts :: Either String ()
mixedDispositionAccepts =
  mapLeft show $ checkFieldDispositions
    [affineField, linearField]
    [ (affineName, FieldOmitted)
    , (linearName, FieldBound)
    ]

affineField, linearField :: OwnedField
affineField = OwnedField affineName Affine affineTy
linearField = OwnedField linearName Linear linearTy

affineName, linearName :: Name
affineName = Name "capability"
linearName = Name "payload"

affineTy, linearTy :: Ty
affineTy = TyOpaque "AffineCap"
linearTy = TyOpaque "OwnedBytes[4]"

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
