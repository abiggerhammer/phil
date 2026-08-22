From Phil.LLVM Require Import Preservation.

(*
  PHIL-LLVM-FIELD-PROJ-001 — specialization of PHIL-LLVM-PRESERVE-001 for
  the ordinary semantic operation introduced by the Begin.length field-
  projection slice.

  The current Systems representation deliberately lowers the projection as an
  ordinary semantic operation (`project recognized Begin.length`).  It is not
  yet a concrete record-layout load.  Therefore this theorem proves exact
  preservation of the conservative ordinary-operation projection digest and
  nothing about an i64 load, pointer arithmetic, or a recognized-record ABI.

  Concrete rendering of the semantic runtime-call name, list projection into
  LLVM text, and correspondence to Phil.LLVM.Lower / Phil.LLVM.Verify remain
  implementation boundaries already owned by PHIL-LLVM-PRESERVE-001.
*)

Record LLVMFieldProjectionModel : Type := mkLLVMFieldProjectionModel {
  fieldProjectionPreservationModel : LLVMPreservationModel;
  fieldProjectionBlock : BlockId;
  fieldProjectionExpectedDigest : ProjectionDigest
}.

Definition LLVMFieldProjectionVerificationSuccess
  (model : LLVMFieldProjectionModel) : Prop :=
  LLVMPreservationVerificationSuccess
    (fieldProjectionPreservationModel model) /\
  preservationExpectedOrdinaryOps
    (fieldProjectionPreservationModel model)
    (fieldProjectionBlock model) =
    fieldProjectionExpectedDigest model.

Theorem verified_llvm_field_projection_rechecks_systems_source :
  forall model,
    LLVMFieldProjectionVerificationSuccess model ->
    preservationSystemsSourceReverified
      (fieldProjectionPreservationModel model) = true.
Proof.
  intros model Hverified.
  destruct Hverified as [Hpreservation _].
  exact
    (verified_llvm_rechecks_source_systems_artifact
      (fieldProjectionPreservationModel model)
      Hpreservation).
Qed.

Theorem verified_llvm_field_projection_preserves_exact_ordinary_operation :
  forall model,
    LLVMFieldProjectionVerificationSuccess model ->
    preservationActualOrdinaryOps
      (fieldProjectionPreservationModel model)
      (fieldProjectionBlock model) =
    fieldProjectionExpectedDigest model.
Proof.
  intros model Hverified.
  destruct Hverified as [Hpreservation Hexpected].
  pose proof
    (verified_llvm_matches_conservative_ordinary_projection
      (fieldProjectionPreservationModel model)
      (fieldProjectionBlock model)
      Hpreservation) as Hordinary.
  destruct Hordinary as [Hops _].
  rewrite <- Hexpected.
  symmetry.
  exact Hops.
Qed.

Theorem llvm_field_projection_loss_or_drift_is_rejected :
  forall model,
    preservationActualOrdinaryOps
      (fieldProjectionPreservationModel model)
      (fieldProjectionBlock model) <>
    fieldProjectionExpectedDigest model ->
    ~ LLVMFieldProjectionVerificationSuccess model.
Proof.
  intros model Hdrift Hverified.
  apply Hdrift.
  apply verified_llvm_field_projection_preserves_exact_ordinary_operation.
  exact Hverified.
Qed.

Theorem llvm_field_projection_requires_generic_preservation_boundary :
  forall model,
    ~ LLVMPreservationVerificationSuccess
        (fieldProjectionPreservationModel model) ->
    ~ LLVMFieldProjectionVerificationSuccess model.
Proof.
  intros model HnotPreserved Hverified.
  apply HnotPreserved.
  destruct Hverified as [Hpreservation _].
  exact Hpreservation.
Qed.
