From Stdlib Require Import Bool.Bool.

(*
  PHIL-TARGET-RUNTIME-PRIM-001 — target-neutral runtime primitive identity.

  A selected runtime primitive is identified by its physical operation family
  and exact target profile/signature.  The backend-visible entry identity may be
  a linker symbol, WebAssembly import/function/table identity, VM opcode or
  precompile identity, SBF syscall/CPI target, or another target-specific entry
  representation.  Assurance revision/evidence/use identity and claim-set
  cardinality remain verifier metadata and cannot, by themselves, rename the
  primitive entry.

  This theorem deliberately says nothing about one particular target's calling
  convention, linker, instruction encoding, table layout, or runtime behavior.
  Those remain target-profile refinement obligations.
*)

Definition RuntimePrimitiveId := nat.
Definition RuntimePrimitiveProfileId := nat.
Definition RuntimeTargetEntryId := nat.
Definition RuntimeAssuranceRevisionId := nat.
Definition RuntimeAssuranceEvidenceId := nat.
Definition RuntimeAssuranceUseId := nat.

Record RuntimePrimitiveIdentityModel : Type := mkRuntimePrimitiveIdentityModel {
  runtimePrimitiveIdentity : RuntimePrimitiveId;
  runtimePrimitiveProfile : RuntimePrimitiveProfileId;
  runtimePrimitiveEntryBuilder :
    RuntimePrimitiveId -> RuntimePrimitiveProfileId -> RuntimeTargetEntryId;
  runtimePrimitiveActualEntry : RuntimeTargetEntryId;
  runtimePrimitiveAssuranceRevision : RuntimeAssuranceRevisionId;
  runtimePrimitiveAssuranceEvidence : RuntimeAssuranceEvidenceId;
  runtimePrimitiveAssuranceUse : RuntimeAssuranceUseId;
  runtimePrimitiveClaimCount : nat;
  runtimePrimitiveAssuranceIdentityEncoded : bool
}.

Definition targetEntryFor
  (model : RuntimePrimitiveIdentityModel)
  (_revision : RuntimeAssuranceRevisionId)
  (_evidence : RuntimeAssuranceEvidenceId)
  (_use : RuntimeAssuranceUseId)
  (_claimCount : nat) : RuntimeTargetEntryId :=
  runtimePrimitiveEntryBuilder model
    (runtimePrimitiveIdentity model)
    (runtimePrimitiveProfile model).

Record RuntimePrimitiveIdentityVerificationSuccess
  (model : RuntimePrimitiveIdentityModel) : Prop :=
  mkRuntimePrimitiveIdentityVerificationSuccess {
    runtime_primitive_identity_success_physical_identity :
      runtimePrimitiveActualEntry model =
        runtimePrimitiveEntryBuilder model
          (runtimePrimitiveIdentity model)
          (runtimePrimitiveProfile model);
    runtime_primitive_identity_success_no_assurance_encoding :
      runtimePrimitiveAssuranceIdentityEncoded model = false
  }.

Theorem verified_runtime_primitive_uses_physical_identity_and_profile :
  forall model,
    RuntimePrimitiveIdentityVerificationSuccess model ->
    runtimePrimitiveActualEntry model =
      runtimePrimitiveEntryBuilder model
        (runtimePrimitiveIdentity model)
        (runtimePrimitiveProfile model).
Proof.
  intros model H.
  exact (runtime_primitive_identity_success_physical_identity model H).
Qed.

Theorem runtime_primitive_entry_is_independent_of_assurance_metadata :
  forall model revisionA evidenceA useA countA
         revisionB evidenceB useB countB,
    targetEntryFor model revisionA evidenceA useA countA =
    targetEntryFor model revisionB evidenceB useB countB.
Proof.
  intros.
  reflexivity.
Qed.

Theorem verified_runtime_primitive_does_not_encode_assurance_identity :
  forall model,
    RuntimePrimitiveIdentityVerificationSuccess model ->
    runtimePrimitiveAssuranceIdentityEncoded model = false.
Proof.
  intros model H.
  exact (runtime_primitive_identity_success_no_assurance_encoding model H).
Qed.

Theorem assurance_derived_runtime_entry_is_rejected :
  forall model,
    runtimePrimitiveAssuranceIdentityEncoded model = true ->
    ~ RuntimePrimitiveIdentityVerificationSuccess model.
Proof.
  intros model Hencoded H.
  rewrite
    (runtime_primitive_identity_success_no_assurance_encoding model H)
    in Hencoded.
  discriminate.
Qed.

Theorem runtime_primitive_entry_drift_is_rejected :
  forall model,
    runtimePrimitiveActualEntry model <>
      runtimePrimitiveEntryBuilder model
        (runtimePrimitiveIdentity model)
        (runtimePrimitiveProfile model) ->
    ~ RuntimePrimitiveIdentityVerificationSuccess model.
Proof.
  intros model Hdrift H.
  apply Hdrift.
  exact (runtime_primitive_identity_success_physical_identity model H).
Qed.
