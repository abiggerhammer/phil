{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Core.DataDestruction
  ( DataDestructionError (..)
  , FieldDisposition (..)
  , OwnedField (..)
  , checkFieldDispositions
  )
import Phil.Core.Syntax (Mode (..), Name (Name), Ty (TyOpaque))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "DATA-005 explicit linear successor binding accepts" explicitLinearBindingAccepts
    , test "DATA-005 omitted linear field rejects" omittedLinearFieldRejects
    , test "DATA-005 absent linear disposition rejects" absentLinearDispositionRejects
    , test "DATA-005 unrestricted omission remains legal" unrestrictedOmissionAccepts
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

explicitLinearBindingAccepts :: Either String ()
explicitLinearBindingAccepts =
  mapLeft show $ checkFieldDispositions fields
    [(metadataName, FieldOmitted), (payloadName, FieldBound)]

omittedLinearFieldRejects :: Either String ()
omittedLinearFieldRejects =
  expectMissing $ checkFieldDispositions fields
    [(metadataName, FieldBound), (payloadName, FieldOmitted)]

absentLinearDispositionRejects :: Either String ()
absentLinearDispositionRejects =
  expectMissing $ checkFieldDispositions fields
    [(metadataName, FieldBound)]

unrestrictedOmissionAccepts :: Either String ()
unrestrictedOmissionAccepts =
  mapLeft show $ checkFieldDispositions [metadataField]
    [(metadataName, FieldOmitted)]

expectMissing :: Either DataDestructionError () -> Either String ()
expectMissing result = case result of
  Left (MissingLinearFieldDisposition actual) ->
    assert (actual == payloadName) "wrong omitted linear field reported"
  Left err -> Left ("wrong error: " <> show err)
  Right () -> Left "missing linear field disposition was accepted"

fields :: [OwnedField]
fields = [metadataField, payloadField]

metadataField, payloadField :: OwnedField
metadataField = OwnedField metadataName Unrestricted metadataTy
payloadField = OwnedField payloadName Linear payloadTy

metadataName, payloadName :: Name
metadataName = Name "tag"
payloadName = Name "payload"

metadataTy, payloadTy :: Ty
metadataTy = TyOpaque "UInt[8]"
payloadTy = TyOpaque "OwnedBytes[4]"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
