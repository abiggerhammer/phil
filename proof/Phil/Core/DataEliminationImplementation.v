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
    split;
    intro H;
    try reflexivity;
    try discriminate;
    auto.
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
  destruct allFieldDispositionsAllowed;
    destruct dispositionEntriesDistinct;
    cbn.
  - split; intro H.
    + split.
      * apply (proj1 Hfields). reflexivity.
      * apply (proj1 Hdistinct). reflexivity.
    + reflexivity.
  - split; intro H.
    + discriminate.
    + destruct H as [_ HdistinctProp].
      pose proof ((proj2 Hdistinct) HdistinctProp) as Htrue.
      discriminate.
  - split; intro H.
    + discriminate.
    + destruct H as [HfieldsProp _].
      pose proof ((proj2 Hfields) HfieldsProp) as Htrue.
      discriminate.
  - split; intro H.
    + discriminate.
    + destruct H as [HfieldsProp _].
      pose proof ((proj2 Hfields) HfieldsProp) as Htrue.
      discriminate.
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
  destruct disposition; cbn; split; intro H; try exact I; try discriminate.
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
  destruct aggregateConsumed;
    destruct successorsExact;
    destruct successorsDistinct;
    cbn.
  - split; intro H.
    + repeat split.
      * apply (proj1 Haggregate). reflexivity.
      * apply (proj1 Hexact). reflexivity.
      * apply (proj1 Hdistinct). reflexivity.
    + reflexivity.
  - split; intro H.
    + discriminate.
    + destruct H as [_ [_ Hprop]].
      pose proof ((proj2 Hdistinct) Hprop) as Htrue.
      discriminate.
  - split; intro H.
    + discriminate.
    + destruct H as [_ [Hprop _]].
      pose proof ((proj2 Hexact) Hprop) as Htrue.
      discriminate.
  - split; intro H.
    + discriminate.
    + destruct H as [_ [Hprop _]].
      pose proof ((proj2 Hexact) Hprop) as Htrue.
      discriminate.
  - all: split; intro H.
    + discriminate.
    + destruct H as [Hprop _].
      pose proof ((proj2 Haggregate) Hprop) as Htrue.
      discriminate.
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
  destruct fieldDeclared;
    destruct loanStarted;
    destruct ownerImmobilized;
    destruct activeLoanRejectedAtBoundary;
    destruct loanEndPreservedOwner;
    cbn.
  - split; intro H.
    + repeat split.
      * apply (proj1 Hfield). reflexivity.
      * apply (proj1 Hstart). reflexivity.
      * apply (proj1 Hmovement). reflexivity.
      * apply (proj1 Hboundary). reflexivity.
      * apply (proj1 Hend). reflexivity.
    + reflexivity.
  - split; intro H.
    + discriminate.
    + destruct H as [_ [_ [_ [_ Hprop]]]].
      pose proof ((proj2 Hend) Hprop) as Htrue.
      discriminate.
  - all: split; intro H.
    + discriminate.
    + destruct H as [HfieldProp [HstartProp [HmovementProp [HboundaryProp HendProp]]]].
      first
        [ pose proof ((proj2 Hfield) HfieldProp) as Htrue
        | pose proof ((proj2 Hstart) HstartProp) as Htrue
        | pose proof ((proj2 Hmovement) HmovementProp) as Htrue
        | pose proof ((proj2 Hboundary) HboundaryProp) as Htrue
        | pose proof ((proj2 Hend) HendProp) as Htrue ];
      discriminate.
Qed.
