{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified CheckedBindingModeKernel as Kernel
import qualified Data.Map.Strict as Map
import Phil.Core.CheckedBindingMode
import Phil.Core.Context
  ( CheckError (..)
  , ResourceContext (..)
  , emptyContext
  , insertBinding
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
        [ ("production term parameter accepts exact checked mode", acceptsOrigin TermParameterBinding Unrestricted boolType)
        , ("production let binding accepts exact checked mode", acceptsOrigin LetBinding Affine affineType)
        , ("production owning pattern accepts exact checked mode", acceptsOrigin OwningPatternBinding Linear linearType)
        , ("production entry value accepts exact checked mode", acceptsOrigin EntryValueBinding Affine entryType)
        , ("production successor accepts exact checked mode", acceptsOrigin SuccessorBinding Linear successorType)
        , ("production type mismatch keeps native diagnostic", rejectsTypeMismatch)
        , ("production mode mismatch keeps native diagnostic", rejectsModeMismatch)
        , ("production duplicate keeps native context diagnostic", rejectsDuplicate)
        , ("exact kernel rejects type disagreement", not (Kernel.decideCheckedBindingModeByFacts False True True))
        , ("exact kernel rejects mode disagreement", not (Kernel.decideCheckedBindingModeByFacts True False True))
        , ("exact kernel rejects context disagreement", not (Kernel.decideCheckedBindingModeByFacts True True False))
        ]
  mapM_ report results
  if all snd results then pure () else exitFailure

acceptsOrigin :: BindingOrigin -> Mode -> Ty -> Bool
acceptsOrigin origin mode ty =
  case insertCheckedBinding origin (CheckedTypeMode ty mode) mode bindingName ty emptyContext of
    Right context -> inExactZone mode bindingName ty context
    Left _ -> False

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

rejectsDuplicate :: Bool
rejectsDuplicate =
  case insertBinding Unrestricted bindingName boolType emptyContext of
    Left _ -> False
    Right occupied ->
      case insertCheckedBinding TermParameterBinding
          (CheckedTypeMode boolType Unrestricted)
          Unrestricted
          bindingName
          boolType
          occupied of
        Left (CheckedBindingContextError TermParameterBinding (DuplicateBinding actualName)) ->
          actualName == bindingName
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
