From Phil.LLVM Require Import Preservation.

(*
  PHIL-LLVM-RUNTIME-SYM-001 — normalized proof model of the recognized-record
  ABI v1 rule introduced by PR #43.

  Linker-visible runtime symbols are functions of physical primitive identity
  and ABI signature only.  Revision/evidence/use identities and claim-set
  cardinality remain verifier metadata and cannot, by themselves, rename the
  primitive or multiply the physical call.  The current RuntimeSiteRef is a
  singleton-claim special case; arbitrary nonempty claim-set preservation is
  deliberately outside this theorem.
*)

Definition RuntimePrimitiveId := nat.
Definition RuntimeSignatureId := nat.
Definition RuntimeSymbolId := nat.
Definition RuntimeRevisionId := nat.
Definition RuntimeEvidenceId := nat.
Definition RuntimeUseId := nat.

Record RuntimeSymbolModel : Type := mkRuntimeSymbolModel {
  runtimeSymbolPreservation : LLVMPreservationModel;
  runtimeSymbolSite : RuntimeSiteId;
  runtimeSymbolPrimitive : RuntimePrimitiveId;
  runtimeSymbolSignature : RuntimeSignatureId;
  runtimeSymbolBuilder : RuntimePrimitiveId -> RuntimeSignatureId -> RuntimeSymbolId;
  runtimeSymbolActual : RuntimeSymbolId;
  runtimeSymbolRevision : RuntimeRevisionId;
  runtimeSymbolEvidence : RuntimeEvidenceId;
  runtimeSymbolUse : RuntimeUseId;
  runtimeSymbolClaimCount : nat;
  runtimeSymbolAssuranceIdentityEncoded : bool
}.

Definition linkerSymbolFor
  (model : RuntimeSymbolModel)
  (_revision : RuntimeRevisionId)
  (_evidence : RuntimeEvidenceId)
  (_use : RuntimeUseId)
  (_claimCount : nat) : RuntimeSymbolId :=
  runtimeSymbolBuilder model
    (runtimeSymbolPrimitive model)
    (runtimeSymbolSignature model).

Record RuntimeSymbolVerificationSuccess
  (model : RuntimeSymbolModel) : Prop := mkRuntimeSymbolVerificationSuccess {
  runtime_symbol_success_preservation :
    LLVMPreservationVerificationSuccess (runtimeSymbolPreservation model);
  runtime_symbol_success_source_site_once :
    preservationSourceRuntimeCount
      (runtimeSymbolPreservation model)
      (runtimeSymbolSite model) = 1;
  runtime_symbol_success_physical_identity :
    runtimeSymbolActual model =
      runtimeSymbolBuilder model
        (runtimeSymbolPrimitive model)
        (runtimeSymbolSignature model);
  runtime_symbol_success_no_assurance_encoding :
    runtimeSymbolAssuranceIdentityEncoded model = false
}.

Theorem verified_runtime_symbol_uses_physical_primitive_and_signature :
  forall model,
    RuntimeSymbolVerificationSuccess model ->
    runtimeSymbolActual model =
      runtimeSymbolBuilder model
        (runtimeSymbolPrimitive model)
        (runtimeSymbolSignature model).
Proof.
  intros model H.
  exact (runtime_symbol_success_physical_identity model H).
Qed.

Theorem runtime_symbol_is_independent_of_revision_evidence_use_and_claim_count :
  forall model revisionA evidenceA useA countA revisionB evidenceB useB countB,
    linkerSymbolFor model revisionA evidenceA useA countA =
    linkerSymbolFor model revisionB evidenceB useB countB.
Proof.
  intros.
  reflexivity.
Qed.

Theorem verified_singleton_runtime_site_remains_one_llvm_call :
  forall model,
    RuntimeSymbolVerificationSuccess model ->
    preservationTargetRuntimeCount
      (runtimeSymbolPreservation model)
      (runtimeSymbolSite model) = 1.
Proof.
  intros model H.
  pose proof
    (verified_llvm_preserves_runtime_site_multiplicity
      (runtimeSymbolPreservation model)
      (runtimeSymbolSite model)
      (runtime_symbol_success_preservation model H)) as Hcount.
  rewrite <- Hcount.
  exact (runtime_symbol_success_source_site_once model H).
Qed.

Theorem verified_runtime_symbol_does_not_encode_assurance_identity :
  forall model,
    RuntimeSymbolVerificationSuccess model ->
    runtimeSymbolAssuranceIdentityEncoded model = false.
Proof.
  intros model H.
  exact (runtime_symbol_success_no_assurance_encoding model H).
Qed.

Theorem evidence_derived_runtime_symbol_is_rejected :
  forall model,
    runtimeSymbolAssuranceIdentityEncoded model = true ->
    ~ RuntimeSymbolVerificationSuccess model.
Proof.
  intros model Hencoded H.
  rewrite (runtime_symbol_success_no_assurance_encoding model H) in Hencoded.
  discriminate.
Qed.

Theorem runtime_symbol_drift_is_rejected :
  forall model,
    runtimeSymbolActual model <>
      runtimeSymbolBuilder model
        (runtimeSymbolPrimitive model)
        (runtimeSymbolSignature model) ->
    ~ RuntimeSymbolVerificationSuccess model.
Proof.
  intros model Hdrift H.
  apply Hdrift.
  exact (runtime_symbol_success_physical_identity model H).
Qed.

Theorem runtime_call_duplication_is_rejected :
  forall model,
    preservationTargetRuntimeCount
      (runtimeSymbolPreservation model)
      (runtimeSymbolSite model) <> 1 ->
    ~ RuntimeSymbolVerificationSuccess model.
Proof.
  intros model Hduplicate H.
  apply Hduplicate.
  exact (verified_singleton_runtime_site_remains_one_llvm_call model H).
Qed.
