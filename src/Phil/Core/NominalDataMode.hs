{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.NominalDataMode
  ( NominalRestrictionJustification (..)
  , NominalModeError (..)
  , checkNominalMode
  , checkRecordMode
  , checkSumMode
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.DataMode
  ( deriveRecordMode
  , deriveSumMode
  , modeLub
  )
import Phil.Core.Syntax (Mode)

data NominalRestrictionJustification
  = AdmittedResourceObligation Text
  | AdmittedLifecycleObligation Text
  | AdmittedAuthorityLifecycleObligation Text
  | UnadmittedNominalRestriction Text
  deriving (Eq, Show)

data NominalModeError
  = DeclaredModeWeakensDerived Mode Mode
  | StrongerModeMissingJustification Mode Mode
  | StrongerModeUnadmittedJustification Text
  | StrongerModeEmptyJustification
  deriving (Eq, Show)

checkNominalMode
  :: Mode
  -> Maybe Mode
  -> Maybe NominalRestrictionJustification
  -> Either NominalModeError Mode
checkNominalMode derivedMode declaredMode justification =
  case declaredMode of
    Nothing -> Right derivedMode
    Just declared
      | modeLub derivedMode declared /= declared ->
          Left (DeclaredModeWeakensDerived derivedMode declared)
      | declared == derivedMode -> Right declared
      | otherwise -> do
          checkStrengtheningJustification derivedMode declared justification
          Right declared

checkRecordMode
  :: [Mode]
  -> Maybe Mode
  -> Maybe NominalRestrictionJustification
  -> Either NominalModeError Mode
checkRecordMode fieldModes = checkNominalMode (deriveRecordMode fieldModes)

checkSumMode
  :: [[Mode]]
  -> Maybe Mode
  -> Maybe NominalRestrictionJustification
  -> Either NominalModeError Mode
checkSumMode constructorPayloadModes = checkNominalMode (deriveSumMode constructorPayloadModes)

checkStrengtheningJustification
  :: Mode
  -> Mode
  -> Maybe NominalRestrictionJustification
  -> Either NominalModeError ()
checkStrengtheningJustification derived declared justification =
  case justification of
    Nothing -> Left (StrongerModeMissingJustification derived declared)
    Just (UnadmittedNominalRestriction detail) ->
      Left (StrongerModeUnadmittedJustification detail)
    Just admitted
      | Text.null (justificationText admitted) -> Left StrongerModeEmptyJustification
      | otherwise -> Right ()

justificationText :: NominalRestrictionJustification -> Text
justificationText justification = case justification of
  AdmittedResourceObligation detail -> detail
  AdmittedLifecycleObligation detail -> detail
  AdmittedAuthorityLifecycleObligation detail -> detail
  UnadmittedNominalRestriction detail -> detail
