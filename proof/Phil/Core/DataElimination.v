From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Strings.String.
Import ListNotations.

From Phil.Core Require Import Syntax Context.

(*
  PHIL-DATA-ELIM-001 — consuming aggregate elimination and scoped borrowing.

  The aggregate-specific semantics are kept separate from the already
  mechanized Core resource context. Linear aggregate consumption and fresh
  successor insertion reuse Context.v. Field disposition and borrowed-view
  scope are modeled here in a representation-neutral form.
*)

Inductive FieldDisposition : Type :=
| FieldBound
| FieldOmitted.

Record DataField : Type := mkDataField {
  dataFieldKey : nat;
  dataFieldMode : Mode;
  dataFieldType : Ty
}.

Definition FieldDispositionAllowed
  (field : DataField)
  (disposition : option FieldDisposition) : Prop :=
  match dataFieldMode field with
  | Linear => disposition = Some FieldBound
  | Affine =>
      disposition = Some FieldBound \/
      disposition = Some FieldOmitted \/
      disposition = None
  | Unrestricted => True
  end.

Definition EliminationPlanAccepted
  (fields : list DataField)
  (dispositions : nat -> option FieldDisposition) : Prop :=
  forall field,
    In field fields ->
    FieldDispositionAllowed field (dispositions (dataFieldKey field)).

Theorem accepted_plan_binds_every_linear_field :
  forall fields dispositions field,
    EliminationPlanAccepted fields dispositions ->
    In field fields ->
    dataFieldMode field = Linear ->
    dispositions (dataFieldKey field) = Some FieldBound.
Proof.
  intros fields dispositions field Hplan Hin Hlinear.
  pose proof (Hplan field Hin) as Hallowed.
  unfold FieldDispositionAllowed in Hallowed.
  rewrite Hlinear in Hallowed.
  exact Hallowed.
Qed.

Theorem accepted_plan_affine_field_is_at_most_once_or_omitted :
  forall fields dispositions field,
    EliminationPlanAccepted fields dispositions ->
    In field fields ->
    dataFieldMode field = Affine ->
    dispositions (dataFieldKey field) = Some FieldBound \/
    dispositions (dataFieldKey field) = Some FieldOmitted \/
    dispositions (dataFieldKey field) = None.
Proof.
  intros fields dispositions field Hplan Hin Haffine.
  pose proof (Hplan field Hin) as Hallowed.
  unfold FieldDispositionAllowed in Hallowed.
  rewrite Haffine in Hallowed.
  exact Hallowed.
Qed.

Definition DispositionEntry : Type := (nat * FieldDisposition)%type.

Definition DistinctDispositionEntries (entries : list DispositionEntry) : Prop :=
  NoDup (map fst entries).

Theorem duplicate_field_dispositions_reject :
  forall key first second rest,
    ~ DistinctDispositionEntries
        ((key, first) :: (key, second) :: rest).
Proof.
  intros key first second rest Hnodup.
  unfold DistinctDispositionEntries in Hnodup.
  simpl in Hnodup.
  inversion Hnodup as [| head tail Hnotin Htail].
  apply Hnotin.
  simpl.
  left.
  reflexivity.
Qed.

Inductive AggregateDisposition : Type :=
| WholeAggregateConsumed
| ExplicitTypedRemainder (remainderType : Ty)
| ImplicitPartialRemainder.

Definition AggregateDispositionAccepted (disposition : AggregateDisposition) : Prop :=
  match disposition with
  | WholeAggregateConsumed => True
  | ExplicitTypedRemainder _ => True
  | ImplicitPartialRemainder => False
  end.

Theorem implicit_partial_remainder_rejects :
  ~ AggregateDispositionAccepted ImplicitPartialRemainder.
Proof.
  simpl.
  intros H.
  exact H.
Qed.

Theorem accepted_partial_remainder_is_explicitly_typed :
  forall disposition,
    AggregateDispositionAccepted disposition ->
    disposition <> WholeAggregateConsumed ->
    exists remainderType,
      disposition = ExplicitTypedRemainder remainderType.
Proof.
  intros disposition Haccepted HnotWhole.
  destruct disposition.
  - exfalso.
    apply HnotWhole.
    reflexivity.
  - exists remainderType.
    reflexivity.
  - simpl in Haccepted.
    contradiction.
Qed.

(* Core one-shot ownership supplies the consuming aggregate step. *)
Theorem consuming_linear_aggregate_removes_owner :
  forall aggregate context next aggregateType,
    consumeLinear aggregate context = Consumed aggregateType next ->
    linearBindings next aggregate = None.
Proof.
  intros aggregate context next aggregateType Hconsume.
  eapply consumeLinear_success_consumes_owner.
  exact Hconsume.
Qed.

(* A bound linear payload is restored in exactly the linear zone. *)
Theorem bound_linear_successor_is_exact :
  forall successor fieldType context next,
    insertBinding Linear successor fieldType context = Inserted next ->
    linearBindings next successor = Some fieldType.
Proof.
  intros successor fieldType context next Hinsert.
  pose proof
    (insertBinding_success_exact Linear successor fieldType context next Hinsert)
    as H.
  destruct H as [_ [_ [_ [Hinstalled _]]]].
  simpl in Hinstalled.
  destruct Hinstalled as [_ [_ Hlinear]].
  exact Hlinear.
Qed.

(* Fresh insertion prevents one successor occurrence from being restored twice. *)
Theorem bound_linear_successor_cannot_be_inserted_twice :
  forall successor firstType secondType context first next,
    insertBinding Linear successor firstType context = Inserted first ->
    insertBinding Linear successor secondType first <> Inserted next.
Proof.
  intros successor firstType secondType context first next Hfirst Hsecond.
  pose proof
    (bound_linear_successor_is_exact
      successor firstType context first Hfirst) as Hpresent.
  pose proof
    (insertBinding_success_name_was_fresh
      Linear successor secondType first next Hsecond) as Hfresh.
  destruct Hfresh as [_ [_ HlinearNone]].
  rewrite Hpresent in HlinearNone.
  discriminate.
Qed.

(*
  Borrowed aggregate inspection is a scoped loan on the aggregate owner.  It
  never inserts another owner for the selected field.  The proof model mirrors
  only the loan bit and leaves all binding maps unchanged.
*)
Definition setLoan
  (owner : Name) (active : bool) (loans : LoanSet) : LoanSet :=
  fun candidate =>
    if String.eqb candidate owner then active else loans candidate.

Definition beginAggregateBorrow
  (owner : Name) (context : ResourceContext) : option ResourceContext :=
  if sharedLoans context owner then
    None
  else
    match linearBindings context owner with
    | Some _ =>
        Some
          (mkResourceContext
            (unrestrictedBindings context)
            (affineBindings context)
            (linearBindings context)
            (setLoan owner true (sharedLoans context)))
    | None =>
        match affineBindings context owner with
        | Some _ =>
            Some
              (mkResourceContext
                (unrestrictedBindings context)
                (affineBindings context)
                (linearBindings context)
                (setLoan owner true (sharedLoans context)))
        | None => None
        end
    end.

Definition endAggregateBorrow
  (owner : Name) (context : ResourceContext) : option ResourceContext :=
  if sharedLoans context owner then
    Some
      (mkResourceContext
        (unrestrictedBindings context)
        (affineBindings context)
        (linearBindings context)
        (setLoan owner false (sharedLoans context)))
  else
    None.

Definition LoanBoundarySafe (context : ResourceContext) : Prop :=
  forall name, sharedLoans context name = false.

Theorem begin_borrow_preserves_all_binding_maps :
  forall owner context loaned,
    beginAggregateBorrow owner context = Some loaned ->
    unrestrictedBindings loaned = unrestrictedBindings context /\
    affineBindings loaned = affineBindings context /\
    linearBindings loaned = linearBindings context.
Proof.
  intros owner context loaned Hbegin.
  unfold beginAggregateBorrow in Hbegin.
  destruct (sharedLoans context owner) eqn:Hactive; try discriminate.
  destruct (linearBindings context owner) as [linearType |] eqn:Hlinear.
  - inversion Hbegin; subst loaned; clear Hbegin.
    repeat split; reflexivity.
  - destruct (affineBindings context owner) as [affineType |] eqn:Haffine.
    + inversion Hbegin; subst loaned; clear Hbegin.
      repeat split; reflexivity.
    + discriminate.
Qed.

Theorem begin_borrow_marks_exact_owner_active :
  forall owner context loaned,
    beginAggregateBorrow owner context = Some loaned ->
    sharedLoans loaned owner = true.
Proof.
  intros owner context loaned Hbegin.
  unfold beginAggregateBorrow in Hbegin.
  destruct (sharedLoans context owner) eqn:Hactive; try discriminate.
  destruct (linearBindings context owner) as [linearType |] eqn:Hlinear.
  - inversion Hbegin; subst loaned; clear Hbegin.
    simpl.
    unfold setLoan.
    now rewrite String.eqb_refl.
  - destruct (affineBindings context owner) as [affineType |] eqn:Haffine.
    + inversion Hbegin; subst loaned; clear Hbegin.
      simpl.
      unfold setLoan.
      now rewrite String.eqb_refl.
    + discriminate.
Qed.

Theorem borrowed_linear_aggregate_owner_cannot_move :
  forall owner context loaned ownerType,
    linearBindings context owner = Some ownerType ->
    beginAggregateBorrow owner context = Some loaned ->
    consumeLinear owner loaned = ConsumeError (OwnerBorrowed owner).
Proof.
  intros owner context loaned ownerType Hlinear Hbegin.
  pose proof (begin_borrow_marks_exact_owner_active owner context loaned Hbegin)
    as Hactive.
  unfold consumeLinear.
  rewrite Hactive.
  reflexivity.
Qed.

Theorem active_aggregate_borrow_cannot_cross_boundary :
  forall owner context loaned,
    beginAggregateBorrow owner context = Some loaned ->
    ~ LoanBoundarySafe loaned.
Proof.
  intros owner context loaned Hbegin Hsafe.
  pose proof (begin_borrow_marks_exact_owner_active owner context loaned Hbegin)
    as Hactive.
  specialize (Hsafe owner).
  rewrite Hactive in Hsafe.
  discriminate.
Qed.

Theorem end_borrow_clears_loan_and_preserves_bindings :
  forall owner context restored,
    sharedLoans context owner = true ->
    endAggregateBorrow owner context = Some restored ->
    sharedLoans restored owner = false /\
    unrestrictedBindings restored = unrestrictedBindings context /\
    affineBindings restored = affineBindings context /\
    linearBindings restored = linearBindings context.
Proof.
  intros owner context restored Hactive Hend.
  unfold endAggregateBorrow in Hend.
  rewrite Hactive in Hend.
  inversion Hend; subst restored; clear Hend.
  split.
  - simpl.
    unfold setLoan.
    now rewrite String.eqb_refl.
  - repeat split; reflexivity.
Qed.

Fixpoint lookupField
  (key : nat) (fields : list DataField) : option DataField :=
  match fields with
  | [] => None
  | field :: rest =>
      if Nat.eqb key (dataFieldKey field)
      then Some field
      else lookupField key rest
  end.

Definition beginFieldBorrow
  (fields : list DataField)
  (key : nat)
  (owner : Name)
  (context : ResourceContext)
  : option (DataField * ResourceContext) :=
  match lookupField key fields with
  | None => None
  | Some field =>
      match beginAggregateBorrow owner context with
      | None => None
      | Some loaned => Some (field, loaned)
      end
  end.

Theorem undeclared_field_borrow_rejects :
  forall fields key owner context,
    lookupField key fields = None ->
    beginFieldBorrow fields key owner context = None.
Proof.
  intros fields key owner context Hmissing.
  unfold beginFieldBorrow.
  rewrite Hmissing.
  reflexivity.
Qed.

Theorem successful_field_borrow_uses_exact_declared_field :
  forall fields key owner context field loaned,
    beginFieldBorrow fields key owner context = Some (field, loaned) ->
    lookupField key fields = Some field /\
    beginAggregateBorrow owner context = Some loaned.
Proof.
  intros fields key owner context field loaned Hbegin.
  unfold beginFieldBorrow in Hbegin.
  destruct (lookupField key fields) as [declared |] eqn:Hlookup;
    try discriminate.
  destruct (beginAggregateBorrow owner context) as [next |] eqn:Hborrow;
    try discriminate.
  inversion Hbegin; subst field loaned; clear Hbegin.
  split.
  - exact Hlookup.
  - exact Hborrow.
Qed.
