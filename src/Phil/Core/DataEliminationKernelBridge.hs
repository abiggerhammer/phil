module Phil.Core.DataEliminationKernelBridge
  ( KernelFieldDisposition (..)
  , KernelAggregateDisposition (..)
  , fieldDispositionAccepted
  , eliminationPlanAccepted
  , aggregateDispositionAccepted
  , consumingEliminationAccepted
  , borrowLifecycleAccepted
  ) where

import qualified DataEliminationKernel as Kernel
import Phil.Core.Syntax (Mode (..))

data KernelFieldDisposition
  = KernelFieldBound
  | KernelFieldOmitted
  deriving (Eq, Show)

data KernelAggregateDisposition
  = KernelWholeAggregate
  | KernelExplicitTypedRemainder
  | KernelImplicitPartialRemainder
  deriving (Eq, Show)

fieldDispositionAccepted :: Mode -> Maybe KernelFieldDisposition -> Bool
fieldDispositionAccepted mode disposition =
  case Kernel.decideFieldDispositionByMode
      (toKernelMode mode)
      (fmap toKernelFieldDisposition disposition) of
    Kernel.FieldDispositionAcceptedDecision -> True
    Kernel.FieldDispositionLinearRequiredDecision -> False

eliminationPlanAccepted :: Bool -> Bool -> Bool
eliminationPlanAccepted allFieldDispositionsAllowed dispositionEntriesDistinct =
  case Kernel.decideEliminationPlanByFacts
      allFieldDispositionsAllowed dispositionEntriesDistinct of
    Kernel.EliminationPlanAcceptedDecision -> True
    Kernel.EliminationPlanFieldDispositionDecision -> False
    Kernel.EliminationPlanDuplicateDispositionDecision -> False

aggregateDispositionAccepted :: KernelAggregateDisposition -> Bool
aggregateDispositionAccepted disposition =
  case Kernel.decideAggregateDispositionKind
      (toKernelAggregateDisposition disposition) of
    Kernel.AggregateDispositionAcceptedDecision -> True
    Kernel.AggregateDispositionImplicitRemainderDecision -> False

consumingEliminationAccepted :: Bool -> Bool -> Bool -> Bool
consumingEliminationAccepted aggregateConsumed successorsExact successorsDistinct =
  case Kernel.decideConsumingEliminationByFacts
      aggregateConsumed successorsExact successorsDistinct of
    Kernel.ConsumingEliminationAcceptedDecision -> True
    Kernel.ConsumingEliminationAggregateDecision -> False
    Kernel.ConsumingEliminationSuccessorDecision -> False
    Kernel.ConsumingEliminationDuplicateSuccessorDecision -> False

borrowLifecycleAccepted :: Bool -> Bool -> Bool -> Bool -> Bool -> Bool
borrowLifecycleAccepted
    fieldDeclared
    loanStarted
    ownerImmobilized
    activeLoanRejectedAtBoundary
    loanEndPreservedOwner =
  case Kernel.decideBorrowLifecycleByFacts
      fieldDeclared
      loanStarted
      ownerImmobilized
      activeLoanRejectedAtBoundary
      loanEndPreservedOwner of
    Kernel.BorrowLifecycleAcceptedDecision -> True
    Kernel.BorrowLifecycleFieldDecision -> False
    Kernel.BorrowLifecycleStartDecision -> False
    Kernel.BorrowLifecycleMovementDecision -> False
    Kernel.BorrowLifecycleBoundaryDecision -> False
    Kernel.BorrowLifecycleEndDecision -> False

toKernelMode :: Mode -> Kernel.Mode
toKernelMode mode = case mode of
  Unrestricted -> Kernel.Unrestricted
  Affine -> Kernel.Affine
  Linear -> Kernel.Linear

toKernelFieldDisposition :: KernelFieldDisposition -> Kernel.FieldDisposition
toKernelFieldDisposition disposition = case disposition of
  KernelFieldBound -> Kernel.FieldBound
  KernelFieldOmitted -> Kernel.FieldOmitted

toKernelAggregateDisposition
  :: KernelAggregateDisposition
  -> Kernel.AggregateDispositionKind
toKernelAggregateDisposition disposition = case disposition of
  KernelWholeAggregate -> Kernel.WholeAggregateKind
  KernelExplicitTypedRemainder -> Kernel.ExplicitTypedRemainderKind
  KernelImplicitPartialRemainder -> Kernel.ImplicitPartialRemainderKind
