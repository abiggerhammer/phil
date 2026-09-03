From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import Syntax DataElimination.

(*
  PHIL-DATA-ELIM-001 — executable implementation-refinement staging.

  Concrete field names, Map construction, aggregate orchestration, and lexical
  scope remain native Haskell responsibilities.  This layer exposes the exact
  representation-neutral disposition decisions plus fail-closed postcondition
  gates over facts established by the real Context operations.
*)

Inductive FieldDispositionDecision : Type :=
| FieldDispositionAcceptedDecision
| FieldDispositionLinearRequiredDecision.

Definition decideFieldDispositionByMode
  (mode : Mode)
  (disposition : option FieldDisposition) : FieldDispositionDecision :=
  match mode with
  | Linear =>
      match disposition with
      | Some FieldBound => FieldDispositionAcceptedDecision
      | _ => FieldDispositionLinearRequiredDecision
      end
  | Affine => FieldDispositionAcceptedDecision
  | Unrestricted => FieldDispositionAcceptedDecision
  end.

Theorem field_disposition_decision_accept_iff_certified :
  forall field disposition,
    decideFieldDispositionByMode (dataFieldMode field) disposition =
      FieldDispositionAcceptedDecision <->
    FieldDispositionAllowed field disposition.
Proof.
  intros [key mode ty] disposition.
  destruct mode;
    destruct disposition as [disposition |];
    try destruct disposition;
    cbn;
    intuition discriminate.
Qed.

Inductive EliminationPlanDecision : Type :=
| EliminationPlanAcceptedDecision
| EliminationPlanFieldDispositionDecision
| EliminationPlanDuplicateDispositionDecision.

Definition decideEliminationPlanByFacts
  (allFieldDispositionsAllowed : bool)
  (dispositionEntriesDistinct : bool) : EliminationPlanDecision :=
  if allFieldDispositionsAllowed then
    if dispositionEntriesDistinct then
      EliminationPlanAcceptedDecision
    else
      EliminationPlanDuplicateDispositionDecision
  else
    EliminationPlanFieldDispositionDecision.

Theorem elimination_plan_decision_accept_iff_facts :
  forall allFieldDispositionsAllowed dispositionEntriesDistinct,
    decideEliminationPlanByFacts
      allFieldDispositionsAllowed dispositionEntriesDistinct =
      EliminationPlanAcceptedDecision <->
    allFieldDispositionsAllowed = true /\
    dispositionEntriesDistinct = true.
Proof.
  intros allFieldDispositionsAllowed dispositionEntriesDistinct.
  destruct allFieldDispositionsAllowed;
    destruct dispositionEntriesDistinct;
    cbn;
    intuition discriminate.
Qed.

Theorem elimination_plan_decision_reflects_certified :
  forall fields dispositions entries
         allFieldDispositionsAllowed dispositionEntriesDistinct,
    (allFieldDispositionsAllowed = true <->
      EliminationPlanAccepted fields dispositions) ->
    (dispositionEntriesDistinct = true <->
      DistinctDispositionEntries entries) ->
    (decideEliminationPlanByFacts
       allFieldDispositionsAllowed dispositionEntriesDistinct =
       EliminationPlanAcceptedDecision <->
     EliminationPlanAccepted fields dispositions /\
     DistinctDispositionEntries entries).
Proof.
  intros fields dispositions entries
    allFieldDispositionsAllowed dispositionEntriesDistinct
    Hfields Hdistinct.
  rewrite elimination_plan_decision_accept_iff_facts.
  rewrite Hfields, Hdistinct.
  reflexivity.
Qed.

Inductive AggregateDispositionKind : Type :=
| WholeAggregateKind
| ExplicitTypedRemainderKind
| ImplicitPartialRemainderKind.

Definition aggregateDispositionKind
  (disposition : AggregateDisposition) : AggregateDispositionKind :=
  match disposition with
  | WholeAggregateConsumed => WholeAggregateKind
  | ExplicitTypedRemainder _ => ExplicitTypedRemainderKind
  | ImplicitPartialRemainder => ImplicitPartialRemainderKind
  end.

Inductive AggregateDispositionDecision : Type :=
| AggregateDispositionAcceptedDecision
| AggregateDispositionImplicitRemainderDecision.

Definition decideAggregateDispositionKind
  (kind : AggregateDispositionKind) : AggregateDispositionDecision :=
  match kind with
  | WholeAggregateKind => AggregateDispositionAcceptedDecision
  | ExplicitTypedRemainderKind => AggregateDispositionAcceptedDecision
  | ImplicitPartialRemainderKind => AggregateDispositionImplicitRemainderDecision
  end.

Theorem aggregate_disposition_decision_accept_iff_certified :
  forall disposition,
    decideAggregateDispositionKind (aggregateDispositionKind disposition) =
      AggregateDispositionAcceptedDecision <->
    AggregateDispositionAccepted disposition.
Proof.
  intros disposition.
  destruct disposition; cbn; intuition discriminate.
Qed.

Inductive ConsumingEliminationDecision : Type :=
| ConsumingEliminationAcceptedDecision
| ConsumingEliminationAggregateDecision
| ConsumingEliminationSuccessorDecision
| ConsumingEliminationDuplicateSuccessorDecision.

Definition decideConsumingEliminationByFacts
  (aggregateConsumed : bool)
  (successorsExact : bool)
  (successorsDistinct : bool) : ConsumingEliminationDecision :=
  if aggregateConsumed then
    if successorsExact then
      if successorsDistinct then
        ConsumingEliminationAcceptedDecision
      else
        ConsumingEliminationDuplicateSuccessorDecision
    else
      ConsumingEliminationSuccessorDecision
  else
    ConsumingEliminationAggregateDecision.

Theorem consuming_elimination_decision_accept_iff_facts :
  forall aggregateConsumed successorsExact successorsDistinct,
    decideConsumingEliminationByFacts
      aggregateConsumed successorsExact successorsDistinct =
      ConsumingEliminationAcceptedDecision <->
    aggregateConsumed = true /\
    successorsExact = true /\
    successorsDistinct = true.
Proof.
  intros aggregateConsumed successorsExact successorsDistinct.
  destruct aggregateConsumed;
    destruct successorsExact;
    destruct successorsDistinct;
    cbn;
    intuition discriminate.
Qed.

Theorem consuming_elimination_decision_reflects_facts :
  forall aggregateConsumed successorsExact successorsDistinct
         AggregateConsumed SuccessorsExact SuccessorsDistinct,
    (aggregateConsumed = true <-> AggregateConsumed) ->
    (successorsExact = true <-> SuccessorsExact) ->
    (successorsDistinct = true <-> SuccessorsDistinct) ->
    (decideConsumingEliminationByFacts
       aggregateConsumed successorsExact successorsDistinct =
       ConsumingEliminationAcceptedDecision <->
     AggregateConsumed /\ SuccessorsExact /\ SuccessorsDistinct).
Proof.
  intros aggregateConsumed successorsExact successorsDistinct
    AggregateConsumed SuccessorsExact SuccessorsDistinct
    Haggregate Hexact Hdistinct.
  rewrite consuming_elimination_decision_accept_iff_facts.
  rewrite Haggregate, Hexact, Hdistinct.
  reflexivity.
Qed.

Inductive BorrowLifecycleDecision : Type :=
| BorrowLifecycleAcceptedDecision
| BorrowLifecycleFieldDecision
| BorrowLifecycleStartDecision
| BorrowLifecycleMovementDecision
| BorrowLifecycleBoundaryDecision
| BorrowLifecycleEndDecision.

Definition decideBorrowLifecycleByFacts
  (fieldDeclared : bool)
  (loanStarted : bool)
  (ownerImmobilized : bool)
  (activeLoanRejectedAtBoundary : bool)
  (loanEndPreservedOwner : bool) : BorrowLifecycleDecision :=
  if fieldDeclared then
    if loanStarted then
      if ownerImmobilized then
        if activeLoanRejectedAtBoundary then
          if loanEndPreservedOwner then
            BorrowLifecycleAcceptedDecision
          else BorrowLifecycleEndDecision
        else BorrowLifecycleBoundaryDecision
      else BorrowLifecycleMovementDecision
    else BorrowLifecycleStartDecision
  else BorrowLifecycleFieldDecision.

Theorem borrow_lifecycle_decision_accept_iff_facts :
  forall fieldDeclared loanStarted ownerImmobilized
         activeLoanRejectedAtBoundary loanEndPreservedOwner,
    decideBorrowLifecycleByFacts
      fieldDeclared loanStarted ownerImmobilized
      activeLoanRejectedAtBoundary loanEndPreservedOwner =
      BorrowLifecycleAcceptedDecision <->
    fieldDeclared = true /\
    loanStarted = true /\
    ownerImmobilized = true /\
    activeLoanRejectedAtBoundary = true /\
    loanEndPreservedOwner = true.
Proof.
  intros fieldDeclared loanStarted ownerImmobilized
    activeLoanRejectedAtBoundary loanEndPreservedOwner.
  destruct fieldDeclared;
    destruct loanStarted;
    destruct ownerImmobilized;
    destruct activeLoanRejectedAtBoundary;
    destruct loanEndPreservedOwner;
    cbn;
    intuition discriminate.
Qed.

Theorem borrow_lifecycle_decision_reflects_facts :
  forall fieldDeclared loanStarted ownerImmobilized
         activeLoanRejectedAtBoundary loanEndPreservedOwner
         FieldDeclared LoanStarted OwnerImmobilized
         ActiveLoanRejectedAtBoundary LoanEndPreservedOwner,
    (fieldDeclared = true <-> FieldDeclared) ->
    (loanStarted = true <-> LoanStarted) ->
    (ownerImmobilized = true <-> OwnerImmobilized) ->
    (activeLoanRejectedAtBoundary = true <-> ActiveLoanRejectedAtBoundary) ->
    (loanEndPreservedOwner = true <-> LoanEndPreservedOwner) ->
    (decideBorrowLifecycleByFacts
       fieldDeclared loanStarted ownerImmobilized
       activeLoanRejectedAtBoundary loanEndPreservedOwner =
       BorrowLifecycleAcceptedDecision <->
     FieldDeclared /\ LoanStarted /\ OwnerImmobilized /\
     ActiveLoanRejectedAtBoundary /\ LoanEndPreservedOwner).
Proof.
  intros fieldDeclared loanStarted ownerImmobilized
    activeLoanRejectedAtBoundary loanEndPreservedOwner
    FieldDeclared LoanStarted OwnerImmobilized
    ActiveLoanRejectedAtBoundary LoanEndPreservedOwner
    Hfield Hstart Hmovement Hboundary Hend.
  rewrite borrow_lifecycle_decision_accept_iff_facts.
  rewrite Hfield, Hstart, Hmovement, Hboundary, Hend.
  reflexivity.
Qed.
