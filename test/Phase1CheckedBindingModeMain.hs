{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Phil.Core.CheckedBindingMode
import Phil.Core.Context
  ( ResourceContext (..)
  , emptyContext
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Name (..)
  , RefTerm (..)
  , Ty (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  let results =
        [ ("RES-012 term parameter uses checked unrestricted zone", acceptsOrigin TermParameterBinding Unrestricted boolType)
        , ("RES-012 let binding uses checked affine zone", acceptsOrigin LetBinding Affine affineType)
        , ("RES-012 owning pattern uses checked linear zone", acceptsOrigin OwningPatternBinding Linear linearType)
        , ("RES-012 entry value uses checked affine zone", acceptsOrigin EntryValueBinding Affine entryType)
        , ("RES-012 successor binding uses checked linear zone", acceptsOrigin SuccessorBinding Linear successorType)
        , ("RES-012 independently supplied mode cannot reclassify binding", rejectsModeMismatch)
        , ("RES-012 independently supplied type must match checked contract", rejectsTypeMismatch)
        ]
  mapM_ report results
  if all snd results then pure () else exitFailure

acceptsOrigin :: BindingOrigin -> Mode -> Ty -> Bool
acceptsOrigin origin mode ty =
  case insertCheckedBinding origin (CheckedTypeMode ty mode) mode bindingName ty emptyContext of
    Right context -> inExactZone mode bindingName ty context
    Left _ -> False

rejectsModeMismatch :: Bool
rejectsModeMismatch =
  case insertCheckedBinding LetBinding
      (CheckedTypeMode linearType Linear)
      Affine
      bindingName
      linearType
      emptyContext of
    Left (CheckedBindingModeMismatch LetBinding actualName Linear Affine) ->
      actualName == bindingName
    _ -> False

rejectsTypeMismatch :: Bool
rejectsTypeMismatch =
  case insertCheckedBinding TermParameterBinding
      (CheckedTypeMode boolType Unrestricted)
      Unrestricted
      bindingName
      (TyUInt 8)
      emptyContext of
    Left (CheckedBindingTypeMismatch TermParameterBinding actualName expected actual) ->
      actualName == bindingName && expected == boolType && actual == TyUInt 8
    _ -> False

inExactZone :: Mode -> Name -> Ty -> ResourceContext -> Bool
inExactZone mode name ty context =
  let unrestricted = Map.lookup name (unrestrictedBindings context)
      affine = Map.lookup name (affineBindings context)
      linear = Map.lookup name (linearBindings context)
  in case mode of
      Unrestricted -> unrestricted == Just ty && affine == Nothing && linear == Nothing
      Affine -> unrestricted == Nothing && affine == Just ty && linear == Nothing
      Linear -> unrestricted == Nothing && affine == Nothing && linear == Just ty

bindingName :: Name
bindingName = Name "x"

boolType, affineType, entryType, successorType, linearType :: Ty
boolType = TyBool
affineType = TyOpaque "AffineCap@rev1"
entryType = TyOpaque "EntryResource@rev1"
successorType = TyOpaque "SuccessorOwner@rev1"
linearType = TyBytes (RefNat 8)

report :: (String, Bool) -> IO ()
report (label, ok) = putStrLn ((if ok then "PASS: " else "FAIL: ") <> label)
