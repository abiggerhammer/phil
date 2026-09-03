module Phil.Core.DataModeKernelBridge
  ( CertifiedNominalDecision (..)
  , certifiedAggregateFormationAccepted
  , certifiedModeLub
  , certifiedNominalDecision
  , certifiedRecordMode
  , certifiedResolvedStrongest
  , certifiedSumMode
  ) where

import qualified DataModeKernel as Kernel
import Phil.Core.Syntax (Mode (..))

data CertifiedNominalDecision
  = CertifiedNominalAccepted Mode
  | CertifiedNominalWeakening
  | CertifiedNominalJustification
  deriving (Eq, Show)

certifiedModeLub :: Mode -> Mode -> Mode
certifiedModeLub left right =
  fromKernelMode (Kernel.modeLub (toKernelMode left) (toKernelMode right))

certifiedRecordMode :: [Mode] -> Mode
certifiedRecordMode =
  fromKernelMode . Kernel.deriveRecordMode . map toKernelMode

certifiedSumMode :: [[Mode]] -> Mode
certifiedSumMode =
  fromKernelMode . Kernel.deriveSumMode . map (map toKernelMode)

certifiedResolvedStrongest :: [Mode] -> Maybe Mode
certifiedResolvedStrongest resolved =
  fromKernelMode <$>
    Kernel.resolvedStrongestMode (map (Just . toKernelMode) resolved)

certifiedNominalDecision :: Mode -> Maybe Mode -> Bool -> CertifiedNominalDecision
certifiedNominalDecision derived declared strictJustificationAccepted =
  case Kernel.decideNominalModeByFact
      (toKernelMode derived)
      (toKernelMode <$> declared)
      strictJustificationAccepted of
    Kernel.NominalModeAcceptedDecision accepted ->
      CertifiedNominalAccepted (fromKernelMode accepted)
    Kernel.NominalModeWeakeningDecision -> CertifiedNominalWeakening
    Kernel.NominalModeJustificationDecision -> CertifiedNominalJustification

certifiedAggregateFormationAccepted :: Bool -> Bool
certifiedAggregateFormationAccepted restrictedOccurrencesUnique =
  case Kernel.decideAggregateFormationByFact restrictedOccurrencesUnique of
    Kernel.AggregateFormationAcceptedDecision -> True
    Kernel.AggregateFormationDuplicateRestrictedDecision -> False

toKernelMode :: Mode -> Kernel.Mode
toKernelMode mode = case mode of
  Unrestricted -> Kernel.Unrestricted
  Affine -> Kernel.Affine
  Linear -> Kernel.Linear

fromKernelMode :: Kernel.Mode -> Mode
fromKernelMode mode = case mode of
  Kernel.Unrestricted -> Unrestricted
  Kernel.Affine -> Affine
  Kernel.Linear -> Linear
