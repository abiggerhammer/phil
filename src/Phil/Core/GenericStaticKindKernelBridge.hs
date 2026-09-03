module Phil.Core.GenericStaticKindKernelBridge
  ( CertifiedDirectStaticActualDecision (..)
  , CertifiedReferencedStaticActualDecision (..)
  , CertifiedCheckedStaticActualShapeDecision (..)
  , certifiedDirectStaticActualDecision
  , certifiedReferencedStaticActualDecision
  , certifiedCheckedStaticActualShapeDecision
  ) where

import qualified GenericStaticKindKernel as Kernel

data CertifiedDirectStaticActualDecision
  = CertifiedDirectStaticActualAccepted
  | CertifiedDirectStaticActualKindMismatch
  | CertifiedDirectStaticActualKernelDisagreement
  deriving (Eq, Show)

certifiedDirectStaticActualDecision
  :: Bool
  -> CertifiedDirectStaticActualDecision
certifiedDirectStaticActualDecision kindMatches =
  case Kernel.decideDirectStaticActualByFact kindMatches of
    Kernel.DirectStaticActualAcceptedDecision
      | kindMatches -> CertifiedDirectStaticActualAccepted
    Kernel.DirectStaticActualKindMismatchDecision
      | not kindMatches -> CertifiedDirectStaticActualKindMismatch
    _ -> CertifiedDirectStaticActualKernelDisagreement

data CertifiedReferencedStaticActualDecision
  = CertifiedReferencedStaticActualAccepted
  | CertifiedReferencedStaticActualUnresolved
  | CertifiedReferencedStaticActualKindMismatch
  | CertifiedReferencedStaticActualAmbiguous
  | CertifiedReferencedStaticActualSemanticFormMismatch
  | CertifiedReferencedStaticActualKernelDisagreement
  deriving (Eq, Show)

certifiedReferencedStaticActualDecision
  :: Bool
  -> Bool
  -> Bool
  -> Bool
  -> CertifiedReferencedStaticActualDecision
certifiedReferencedStaticActualDecision
    nameExists expectedKindPresent expectedKindUnique selectedSemanticFormExact =
  case Kernel.decideReferencedStaticActualByFacts
      nameExists expectedKindPresent expectedKindUnique selectedSemanticFormExact of
    Kernel.ReferencedStaticActualAcceptedDecision
      | nameExists
      , expectedKindPresent
      , expectedKindUnique
      , selectedSemanticFormExact ->
          CertifiedReferencedStaticActualAccepted
    Kernel.ReferencedStaticActualUnresolvedDecision
      | not nameExists ->
          CertifiedReferencedStaticActualUnresolved
    Kernel.ReferencedStaticActualKindMismatchDecision
      | nameExists
      , not expectedKindPresent ->
          CertifiedReferencedStaticActualKindMismatch
    Kernel.ReferencedStaticActualAmbiguousDecision
      | nameExists
      , expectedKindPresent
      , not expectedKindUnique ->
          CertifiedReferencedStaticActualAmbiguous
    Kernel.ReferencedStaticActualSemanticFormMismatchDecision
      | nameExists
      , expectedKindPresent
      , expectedKindUnique
      , not selectedSemanticFormExact ->
          CertifiedReferencedStaticActualSemanticFormMismatch
    _ -> CertifiedReferencedStaticActualKernelDisagreement

data CertifiedCheckedStaticActualShapeDecision
  = CertifiedCheckedStaticActualShapeAccepted
  | CertifiedCheckedStaticActualParameterKeyMismatch
  | CertifiedCheckedStaticActualKindMismatch
  | CertifiedCheckedStaticActualShapeKernelDisagreement
  deriving (Eq, Show)

certifiedCheckedStaticActualShapeDecision
  :: Bool
  -> Bool
  -> CertifiedCheckedStaticActualShapeDecision
certifiedCheckedStaticActualShapeDecision parameterKeyExact kindExact =
  case Kernel.decideCheckedStaticActualShapeByFacts parameterKeyExact kindExact of
    Kernel.CheckedStaticActualShapeAcceptedDecision
      | parameterKeyExact
      , kindExact ->
          CertifiedCheckedStaticActualShapeAccepted
    Kernel.CheckedStaticActualParameterKeyDecision
      | not parameterKeyExact ->
          CertifiedCheckedStaticActualParameterKeyMismatch
    Kernel.CheckedStaticActualKindDecision
      | parameterKeyExact
      , not kindExact ->
          CertifiedCheckedStaticActualKindMismatch
    _ -> CertifiedCheckedStaticActualShapeKernelDisagreement
