{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.Callable.ModeDeclaration
  ( ClosureModeDeclaration (..)
  , ClosureModeJustification (..)
  , CheckedClosureMode (..)
  , ClosureModeDeclarationError (..)
  , checkClosureModeDeclaration
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Callable
  ( CallableContract (..)
  , ClosureCaptureSummary (..)
  )
import qualified Phil.Core.CallableModeStrengtheningKernelBridge as KernelBridge
import Phil.Core.Static (InterfaceRevision)
import Phil.Core.Syntax (Mode (..))

data ClosureModeDeclaration
  = DerivedClosureMode
  | ExplicitClosureMode Mode (Maybe ClosureModeJustification)
  deriving (Eq, Ord, Show)

data ClosureModeJustification
  = LifecycleModeObligation InterfaceRevision Text
  | AuthorityModeObligation InterfaceRevision Text
  | TargetImplementationModeReason Text
  deriving (Eq, Ord, Show)

data CheckedClosureMode = CheckedClosureMode
  { checkedClosureMinimumMode :: Mode
  , checkedClosureSelectedMode :: Mode
  , checkedClosureModeJustification :: Maybe ClosureModeJustification
  , checkedClosureCaptureSummary :: ClosureCaptureSummary
  }
  deriving (Eq, Ord, Show)

data ClosureModeDeclarationError
  = ExplicitClosureModeWeakensCaptureMinimum Mode Mode
  | StricterClosureModeMissingSemanticJustification Mode Mode
  | StricterClosureModeWrongContract
      InterfaceRevision
      InterfaceRevision
  | StricterClosureModeEmptyJustification Mode
  | TargetImplementationCannotStrengthenClosureMode Text
  | ClosureModeStrengtheningKernelDisagreement Text
  deriving (Eq, Ord, Show)

checkClosureModeDeclaration
  :: CallableContract
  -> ClosureCaptureSummary
  -> ClosureModeDeclaration
  -> Either ClosureModeDeclarationError CheckedClosureMode
checkClosureModeDeclaration contract captures declaration =
  case declaration of
    DerivedClosureMode -> acceptChecked minimumMode Nothing
    ExplicitClosureMode declared justification ->
      let nonWeakening = modeRank declared >= modeRank minimumMode
          equalToMinimum = declared == minimumMode
          ( justificationPresent
            , targetImplementationReason
            , contractMatches
            , detailPresent
            ) = justificationFacts justification
          classification = KernelBridge.classifyExplicitClosureModeFacts
            nonWeakening
            equalToMinimum
            justificationPresent
            targetImplementationReason
            contractMatches
            detailPresent
      in case classification of
          KernelBridge.ExplicitClosureModeWeakeningClassification ->
            Left (ExplicitClosureModeWeakensCaptureMinimum minimumMode declared)
          KernelBridge.ExplicitClosureModeEqualClassification ->
            acceptChecked declared justification
          KernelBridge.ExplicitClosureModeMissingJustificationClassification ->
            Left (StricterClosureModeMissingSemanticJustification minimumMode declared)
          KernelBridge.ExplicitClosureModeTargetImplementationClassification ->
            case justification of
              Just (TargetImplementationModeReason detail) ->
                Left (TargetImplementationCannotStrengthenClosureMode detail)
              _ -> kernelDisagreement
                "extracted target-implementation classification lacked a target reason"
          KernelBridge.ExplicitClosureModeWrongContractClassification ->
            wrongContractError justification
          KernelBridge.ExplicitClosureModeEmptyJustificationClassification ->
            Left (StricterClosureModeEmptyJustification declared)
          KernelBridge.ExplicitClosureModeStrengthenedClassification ->
            acceptChecked declared justification
  where
    minimumMode = closureMinimumStructuralMode captures
    interfaceRevision = callableContractInterfaceRevision contract

    checked selected justification = CheckedClosureMode
      { checkedClosureMinimumMode = minimumMode
      , checkedClosureSelectedMode = selected
      , checkedClosureModeJustification = justification
      , checkedClosureCaptureSummary = captures
      }

    acceptChecked selected justification =
      let result = checked selected justification
          shape = KernelBridge.classifyCheckedClosureModeShapeFacts
            (checkedClosureMinimumMode result == minimumMode)
            (checkedClosureSelectedMode result == selected)
            (checkedClosureModeJustification result == justification)
      in case shape of
          KernelBridge.CheckedClosureModeShapeAcceptedClassification -> Right result
          other -> kernelDisagreement
            ("extracted checked-shape classifier rejected production result: "
              <> Text.pack (show other))

    justificationFacts maybeJustification = case maybeJustification of
      Nothing -> (False, False, False, False)
      Just (TargetImplementationModeReason detail) ->
        (True, True, False, not (Text.null detail))
      Just (LifecycleModeObligation revision detail) ->
        (True, False, revision == interfaceRevision, not (Text.null detail))
      Just (AuthorityModeObligation revision detail) ->
        (True, False, revision == interfaceRevision, not (Text.null detail))

    wrongContractError maybeJustification = case maybeJustification of
      Just (LifecycleModeObligation revision _) ->
        Left (StricterClosureModeWrongContract interfaceRevision revision)
      Just (AuthorityModeObligation revision _) ->
        Left (StricterClosureModeWrongContract interfaceRevision revision)
      _ -> kernelDisagreement
        "extracted wrong-contract classification lacked a semantic justification"

    kernelDisagreement detail =
      Left (ClosureModeStrengtheningKernelDisagreement detail)

modeRank :: Mode -> Int
modeRank mode = case mode of
  Unrestricted -> 0
  Affine -> 1
  Linear -> 2
