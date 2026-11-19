From Stdlib Require Import Lists.List Arith.PeanoNat.
Import ListNotations.

From Phil.Core Require Import Syntax Context DataElimination.

(*
  FSEM-01 REC-01: conditional original-source record field disposition bridge.
  The original parsed record identity, checked intrinsic field modes, source
  label => destination Core owner correspondence, and Haskell native execution
  remain separately tested *premises*. This is not a TyRecord or a full
  Source/Surface/Rocq refinement theorem. No new trust axioms are introduced.
*)
Module E := DataElimination.
Module C := Context.

Definition SourceRecordPlanAccepted
    (fields : list E.DataField)
    (dispositions : nat -> option E.FieldDisposition) : Prop :=
  E.EliminationPlanAccepted fields dispositions.

Theorem rec01_accepted_record_binds_every_linear_field :
  forall fields dispositions field,
    SourceRecordPlanAccepted fields dispositions ->
    In field fields ->
    E.dataFieldMode field = Linear ->
    dispositions (E.dataFieldKey field) = Some E.FieldBound.
Proof.
  intros fields dispositions field Haccepted Hin Hmode.
  unfold SourceRecordPlanAccepted in Haccepted.
  eapply E.accepted_plan_binds_every_linear_field; eauto.
Qed.

Theorem rec01_missing_linear_field_rejects :
  forall fields dispositions field,
    In field fields ->
    E.dataFieldMode field = Linear ->
    dispositions (E.dataFieldKey field) <> Some E.FieldBound ->
    ~ SourceRecordPlanAccepted fields dispositions.
Proof.
  intros fields dispositions field Hin Hmode Hnot Haccepted.
  apply Hnot.
  eapply rec01_accepted_record_binds_every_linear_field; eauto.
Qed.

Theorem rec01_duplicated_record_field_disposition_rejects :
  forall label first second rest,
    ~ E.DistinctDispositionEntries
        ((label,first) :: (label,second) :: rest).
Proof.
  intros.
  apply E.duplicate_field_dispositions_reject.
Qed.

Theorem rec01_consuming_linear_record_forgets_original_owner :
  forall owner before after carrier,
    C.consumeLinear owner before = C.Consumed carrier after ->
    C.linearBindings after owner = None.
Proof.
  intros owner before after carrier Hconsume.
  eapply E.consuming_linear_aggregate_removes_owner; eauto.
Qed.

Theorem rec01_bound_linear_record_field_restores_exact_destination :
  forall destination ty before after,
    C.insertBinding Linear destination ty before = C.Inserted after ->
    C.linearBindings after destination = Some ty.
Proof.
  intros destination ty before after Hinsert.
  eapply E.bound_linear_successor_is_exact; eauto.
Qed.

Theorem rec01_restored_linear_record_destination_is_one_shot :
  forall destination firstTy secondTy before first after,
    C.insertBinding Linear destination firstTy before = C.Inserted first ->
    C.insertBinding Linear destination secondTy first <> C.Inserted after.
Proof.
  intros destination firstTy secondTy before first after Hfirst.
  eapply E.bound_linear_successor_cannot_be_inserted_twice; eauto.
Qed.

Print Assumptions rec01_accepted_record_binds_every_linear_field.
Print Assumptions rec01_missing_linear_field_rejects.
Print Assumptions rec01_duplicated_record_field_disposition_rejects.
Print Assumptions rec01_consuming_linear_record_forgets_original_owner.
Print Assumptions rec01_bound_linear_record_field_restores_exact_destination.
Print Assumptions rec01_restored_linear_record_destination_is_one_shot.
