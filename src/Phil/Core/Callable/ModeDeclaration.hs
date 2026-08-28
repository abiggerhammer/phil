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
  deriving (Eq, Ord, Show)

checkClosureModeDeclaration
  :: CallableContract
  -> ClosureCaptureSummary
  -> ClosureModeDeclaration
  -> Either ClosureModeDeclarationError CheckedClosureMode
checkClosureModeDeclaration contract captures declaration =
  case declaration of
    DerivedClosureMode -> Right (checked minimumMode Nothing)
    ExplicitClosureMode declared justification
      | modeRank declared < modeRank minimumMode ->
          Left (ExplicitClosureModeWeakensCaptureMinimum minimumMode declared)
      | declared == minimumMode -> Right (checked declared justification)
      | otherwise -> do
          semanticJustification <- maybe
            (Left (StricterClosureModeMissingSemanticJustification minimumMode declared))
            Right
            justification
          validateJustification declared semanticJustification
          Right (checked declared (Just semanticJustification))
  where
    minimumMode = closureMinimumStructuralMode captures
    interfaceRevision = callableContractInterfaceRevision contract
    checked selected justification = CheckedClosureMode
      { checkedClosureMinimumMode = minimumMode
      , checkedClosureSelectedMode = selected
      , checkedClosureModeJustification = justification
      , checkedClosureCaptureSummary = captures
      }

    validateJustification selected justification = case justification of
      TargetImplementationModeReason detail ->
        Left (TargetImplementationCannotStrengthenClosureMode detail)
      LifecycleModeObligation revision detail ->
        validateSemantic selected revision detail
      AuthorityModeObligation revision detail ->
        validateSemantic selected revision detail

    validateSemantic selected revision detail
      | revision /= interfaceRevision =
          Left (StricterClosureModeWrongContract interfaceRevision revision)
      | Text.null detail = Left (StricterClosureModeEmptyJustification selected)
      | otherwise = Right ()

modeRank :: Mode -> Int
modeRank mode = case mode of
  Unrestricted -> 0
  Affine -> 1
  Linear -> 2
