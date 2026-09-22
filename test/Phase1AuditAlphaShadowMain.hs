{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Monad (unless)
import Data.Text (Text)
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (insertBinding)
import Phil.Core.Syntax
import Phil.Core.Value
import System.Exit (exitFailure)

data AuditCase = AuditCase String (Either String ())

main :: IO ()
main = do
  results <- mapM runCase cases
  unless (and results) exitFailure

runCase :: AuditCase -> IO Bool
runCase (AuditCase ident action) = case action of
  Right () -> putStrLn ("PASS: PHIL-AUD-ALPHA-SHADOW-001 " <> ident) >> pure True
  Left detail -> do
    putStrLn ("FAIL: PHIL-AUD-ALPHA-SHADOW-001 " <> ident <> " -- " <> detail)
    pure False

cases :: [AuditCase]
cases =
  [ AuditCase "A01 mismatched lexical binders are not session-equal" $
      assert (not (definitionallyEqualSession badLeft badRight))
        "cross-shadowed dependent sessions compared equal"
  , AuditCase "A02 endpoint comparison rejects the cross-shadow witness" $
      assert
        (compareTypes (TyEndpoint badLeft) (TyEndpoint badRight) == IncompatibleTypes)
        "cross-shadowed endpoint types were not incompatible"
  , AuditCase "A03 checkValue rejects cross-shadow endpoint retyping" $
      alphaChecked False
  , AuditCase "A04 VAscribe rejects cross-shadow endpoint retyping" $
      alphaChecked True
  , AuditCase "A05 legitimate shadowing remains alpha-equivalent" $
      assert
        (definitionallyEqualSession
          (closedSession (map nm ["outer", "inner"]) (nm "inner"))
          (closedSession (map nm ["x", "x"]) (nm "x")))
        "legitimate nearest-binder shadowing stopped comparing equal"
  , AuditCase "A06 real dependency mismatch remains unequal" $
      assert
        (not (definitionallyEqualSession
          (closedSession (map nm ["a", "b", "c"]) (nm "a"))
          (closedSession (map nm ["x", "y", "z"]) (nm "y"))))
        "different lexical dependencies compared equal"
  , AuditCase "A07 ordinary alpha-renaming remains equal" $
      assert
        (definitionallyEqualSession
          badLeft
          (closedSession (map nm ["x", "y", "z"]) (nm "x")))
        "ordinary alpha-renaming stopped comparing equal"
  , AuditCase "A08 guarded recursive equality still reaches its seen state" $
      let recursive = Rec (nm "R") (Receive (nm "msg") TyBool (SessionVar (nm "R")))
          unfolded = Receive (nm "msg") TyBool recursive
      in assert (definitionallyEqualSession recursive unfolded)
          "guarded recursive session no longer compares with one-step unfolding"
  ]

alphaChecked :: Bool -> Either String ()
alphaChecked ascribe = do
  let name = nm "endpoint"
      source = TyEndpoint badLeft
      target = TyEndpoint badRight
  state <- withBinding Linear name source emptyCheckState
  let result = if ascribe
        then synthValue (VAscribe (VVar name) target) state
        else checkValue (VVar name) target state
  case result of
    Left (ValueTypeMismatch actual expected)
      | actual == source && expected == target -> Right ()
    Left err -> Left ("wrong rejection: " <> show err)
    Right value -> Left ("unexpected acceptance: " <> show value)

closedSession :: [Name] -> Name -> Session
closedSession binders lengthName =
  foldr
    (\binder continuation -> Receive binder (TyUInt 16) continuation)
    (Send
      (nm "body")
      (TyBytes (RefToNat (RefVar lengthName)))
      (End (Outcome "success")))
    binders

badLeft, badRight :: Session
badLeft = closedSession (map nm ["a", "b", "b"]) (nm "a")
badRight = closedSession (map nm ["b", "a", "b"]) (nm "a")

nm :: Text -> Name
nm = Name

withBinding :: Mode -> Name -> Ty -> CheckState -> Either String CheckState
withBinding mode name ty state =
  case insertBinding mode name ty (resourceContext state) of
    Left err -> Left (show err)
    Right context -> Right state { resourceContext = context }

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail
