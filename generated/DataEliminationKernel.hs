module DataEliminationKernel where

import qualified Prelude

data Mode =
   Unrestricted
 | Affine
 | Linear

data FieldDisposition =
   FieldBound
 | FieldOmitted

data FieldDispositionDecision =
   FieldDispositionAcceptedDecision
 | FieldDispositionLinearRequiredDecision

decideFieldDispositionByMode :: Mode -> (Prelude.Maybe FieldDisposition) ->
                                FieldDispositionDecision
decideFieldDispositionByMode mode disposition =
  case mode of {
   Linear ->
    case disposition of {
     Prelude.Just f ->
      case f of {
       FieldBound -> FieldDispositionAcceptedDecision;
       FieldOmitted -> FieldDispositionLinearRequiredDecision};
     Prelude.Nothing -> FieldDispositionLinearRequiredDecision};
   _ -> FieldDispositionAcceptedDecision}

data EliminationPlanDecision =
   EliminationPlanAcceptedDecision
 | EliminationPlanFieldDispositionDecision
 | EliminationPlanDuplicateDispositionDecision

decideEliminationPlanByFacts :: Prelude.Bool -> Prelude.Bool ->
                                EliminationPlanDecision
decideEliminationPlanByFacts allFieldDispositionsAllowed dispositionEntriesDistinct =
  case allFieldDispositionsAllowed of {
   Prelude.True ->
    case dispositionEntriesDistinct of {
     Prelude.True -> EliminationPlanAcceptedDecision;
     Prelude.False -> EliminationPlanDuplicateDispositionDecision};
   Prelude.False -> EliminationPlanFieldDispositionDecision}

data AggregateDispositionKind =
   WholeAggregateKind
 | ExplicitTypedRemainderKind
 | ImplicitPartialRemainderKind

data AggregateDispositionDecision =
   AggregateDispositionAcceptedDecision
 | AggregateDispositionImplicitRemainderDecision

decideAggregateDispositionKind :: AggregateDispositionKind ->
                                  AggregateDispositionDecision
decideAggregateDispositionKind kind =
  case kind of {
   ImplicitPartialRemainderKind ->
    AggregateDispositionImplicitRemainderDecision;
   _ -> AggregateDispositionAcceptedDecision}

data ConsumingEliminationDecision =
   ConsumingEliminationAcceptedDecision
 | ConsumingEliminationAggregateDecision
 | ConsumingEliminationSuccessorDecision
 | ConsumingEliminationDuplicateSuccessorDecision

decideConsumingEliminationByFacts :: Prelude.Bool -> Prelude.Bool ->
                                     Prelude.Bool ->
                                     ConsumingEliminationDecision
decideConsumingEliminationByFacts aggregateConsumed successorsExact successorsDistinct =
  case aggregateConsumed of {
   Prelude.True ->
    case successorsExact of {
     Prelude.True ->
      case successorsDistinct of {
       Prelude.True -> ConsumingEliminationAcceptedDecision;
       Prelude.False -> ConsumingEliminationDuplicateSuccessorDecision};
     Prelude.False -> ConsumingEliminationSuccessorDecision};
   Prelude.False -> ConsumingEliminationAggregateDecision}

data BorrowLifecycleDecision =
   BorrowLifecycleAcceptedDecision
 | BorrowLifecycleFieldDecision
 | BorrowLifecycleStartDecision
 | BorrowLifecycleMovementDecision
 | BorrowLifecycleBoundaryDecision
 | BorrowLifecycleEndDecision

decideBorrowLifecycleByFacts :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
                                -> Prelude.Bool -> Prelude.Bool ->
                                BorrowLifecycleDecision
decideBorrowLifecycleByFacts fieldDeclared loanStarted ownerImmobilized activeLoanRejectedAtBoundary loanEndPreservedOwner =
  case fieldDeclared of {
   Prelude.True ->
    case loanStarted of {
     Prelude.True ->
      case ownerImmobilized of {
       Prelude.True ->
        case activeLoanRejectedAtBoundary of {
         Prelude.True ->
          case loanEndPreservedOwner of {
           Prelude.True -> BorrowLifecycleAcceptedDecision;
           Prelude.False -> BorrowLifecycleEndDecision};
         Prelude.False -> BorrowLifecycleBoundaryDecision};
       Prelude.False -> BorrowLifecycleMovementDecision};
     Prelude.False -> BorrowLifecycleStartDecision};
   Prelude.False -> BorrowLifecycleFieldDecision}

