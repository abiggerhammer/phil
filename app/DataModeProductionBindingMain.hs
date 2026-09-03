{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Core.Context
  ( CheckError (..)
  , emptyContext
  , insertBinding
  )
import Phil.Core.DataMode
  ( ModeExpr (..)
  , ProductError (..)
  , deriveRecordMode
  , deriveSumMode
  , formProductBinding
  , instantiateMode
  )
import Phil.Core.NominalDataMode
  ( NominalModeError (..)
  , NominalRestrictionJustification (..)
  , checkNominalMode
  )
import Phil.Core.Syntax (Mode (..), Name (Name), Ty (TyOpaque))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "DATA-MODE production record derivation is kernel-backed" recordDerivation
    , test "DATA-MODE production sum derivation is kernel-backed" sumDerivation
    , test "DATA-MODE production generic strongest fold is kernel-backed" genericStrongest
    , test "DATA-MODE unresolved generic actual still fails closed natively" genericMissing
    , test "DATA-MODE omitted nominal declaration preserves derived mode" nominalOmitted
    , test "DATA-MODE admitted strict nominal strengthening is kernel-accepted" nominalStrictAccepted
    , test "DATA-MODE weakening retains native diagnostic" nominalWeakeningDiagnostic
    , test "DATA-MODE missing strengthening authority retains native diagnostic" nominalMissingDiagnostic
    , test "DATA-MODE real restricted source collection passes formation postcheck" restrictedFormationAccepted
    , test "DATA-MODE duplicate restricted source rejects through ResourceContext" duplicateRestrictedRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

recordDerivation :: Either String ()
recordDerivation =
  assert (deriveRecordMode [Unrestricted, Affine, Linear] == Linear)
    "record mode did not preserve the strongest owned field"

sumDerivation :: Either String ()
sumDerivation =
  assert (deriveSumMode [[Unrestricted], [Affine], [Linear]] == Linear)
    "sum mode did not conservatively include all constructor payloads"

genericStrongest :: Either String ()
genericStrongest =
  assert
    ( instantiateMode
        [("T", Linear)]
        (StrongestMode [FixedMode Affine, ParameterMode "T"])
        == Right Linear
    )
    "resolved generic actual did not reach the certified strongest-mode fold"

genericMissing :: Either String ()
genericMissing =
  assert
    (instantiateMode [] (ParameterMode "T") == Left "unknown generic mode parameter: T")
    "missing generic actual did not preserve the native fail-closed diagnostic"

nominalOmitted :: Either String ()
nominalOmitted =
  assert
    (checkNominalMode Affine Nothing Nothing == Right Affine)
    "omitted nominal declaration did not keep the derived mode"

nominalStrictAccepted :: Either String ()
nominalStrictAccepted =
  assert
    ( checkNominalMode
        Unrestricted
        (Just Linear)
        (Just (AdmittedLifecycleObligation "one-shot lifecycle"))
        == Right Linear
    )
    "admitted strict strengthening was not accepted by the production binding"

nominalWeakeningDiagnostic :: Either String ()
nominalWeakeningDiagnostic =
  assert
    ( checkNominalMode Linear (Just Affine) Nothing
        == Left (DeclaredModeWeakensDerived Linear Affine)
    )
    "nominal weakening did not retain the native diagnostic"

nominalMissingDiagnostic :: Either String ()
nominalMissingDiagnostic =
  assert
    ( checkNominalMode Unrestricted (Just Affine) Nothing
        == Left (StrongerModeMissingJustification Unrestricted Affine)
    )
    "missing strengthening authority did not retain the native diagnostic"

restrictedFormationAccepted :: Either String ()
restrictedFormationAccepted = do
  before <- mapLeft show $ insertBinding Linear ownerName ownerTy emptyContext
  _ <- mapLeft show $ formProductBinding aggregateName [ownerName] before
  Right ()

duplicateRestrictedRejects :: Either String ()
duplicateRestrictedRejects = do
  before <- mapLeft show $ insertBinding Linear ownerName ownerTy emptyContext
  case formProductBinding aggregateName [ownerName, ownerName] before of
    Left (ProductContextError (UnknownBinding actual)) ->
      assert (actual == ownerName) "wrong restricted occurrence reported missing"
    other -> Left ("duplicate restricted source escaped native rejection: " <> show other)

ownerName, aggregateName :: Name
ownerName = Name "payload"
aggregateName = Name "packet"

ownerTy :: Ty
ownerTy = TyOpaque "OwnedBytes[4]"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
