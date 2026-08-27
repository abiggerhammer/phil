{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Core.Context
  ( emptyContext
  , insertBinding
  , useUnrestricted
  )
import Phil.Core.DataMode (deriveRecordMode, modeLub)
import Phil.Core.Syntax
  ( Mode (..)
  , Name (..)
  , Ty (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "DATA-001 unrestricted-only record derives unrestricted mode" unrestrictedRecordMode
    , test "DATA-001 unrestricted aggregate may be copied repeatedly" unrestrictedAggregateCopies
    , test "DATA-001 empty record derives unrestricted identity mode" emptyRecordMode
    , test "DATA-001 mode lattice preserves stronger owned field" strongerModeControl
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

unrestrictedRecordMode :: Either String ()
unrestrictedRecordMode =
  assert (deriveRecordMode [Unrestricted, Unrestricted] == Unrestricted)
    "unrestricted owned fields did not derive unrestricted aggregate mode"

unrestrictedAggregateCopies :: Either String ()
unrestrictedAggregateCopies = do
  context <- mapLeft show $ insertBinding Unrestricted recordName recordTy emptyContext
  (_, first) <- mapLeft show $ useUnrestricted recordName context
  (_, second) <- mapLeft show $ useUnrestricted recordName first
  assert (first == context && second == context)
    "using an unrestricted aggregate consumed or altered its binding"

emptyRecordMode :: Either String ()
emptyRecordMode =
  assert (deriveRecordMode [] == Unrestricted)
    "empty record did not derive unrestricted identity mode"

strongerModeControl :: Either String ()
strongerModeControl = do
  assert (modeLub Unrestricted Affine == Affine) "affine mode was weakened"
  assert (modeLub Affine Linear == Linear) "linear mode was weakened"

recordName :: Name
recordName = Name "metadata"

recordTy :: Ty
recordTy = TyOpaque "MetadataRecord"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
