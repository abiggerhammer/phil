From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import RuntimePrimitiveIdentity.

(*
  Machine-facing decision surface for PHIL-TARGET-RUNTIME-PRIM-001.

  The Certified target-neutral runtime-primitive identity boundary has exactly
  two acceptance facts:

  - the selected target entry is the entry determined by exact physical
    primitive identity plus exact target profile/signature; and
  - assurance revision/evidence/use/claim-count metadata is not encoded into
    that target-entry identity.

  This surface deliberately contains no LLVM symbol, WebAssembly import,
  VM opcode, scheduler, assurance-revision, evidence, use, or claim-count input.
  Concrete target-entry realization remains a target-specific refinement.
*)

Definition RuntimePrimitiveIdentityFacts
  (model : RuntimePrimitiveIdentityModel) : Prop :=
  runtimePrimitiveActualEntry model =
    runtimePrimitiveEntryBuilder model
      (runtimePrimitiveIdentity model)
      (runtimePrimitiveProfile model) /\
  runtimePrimitiveAssuranceIdentityEncoded model = false.

Theorem runtime_primitive_identity_facts_exact :
  forall model,
    RuntimePrimitiveIdentityFacts model <->
    RuntimePrimitiveIdentityVerificationSuccess model.
Proof.
  intros model.
  split.
  - intros [Hentry HnoAssurance].
    constructor; assumption.
  - intros Hsuccess.
    split.
    + exact
        (runtime_primitive_identity_success_physical_identity model Hsuccess).
    + exact
        (runtime_primitive_identity_success_no_assurance_encoding model Hsuccess).
Qed.

Definition decideRuntimePrimitiveIdentityByFacts
  (physicalProfileExact noAssuranceEncoding : bool) : bool :=
  andb physicalProfileExact noAssuranceEncoding.

Theorem decideRuntimePrimitiveIdentityByFacts_classifies :
  forall model physicalProfileExact noAssuranceEncoding,
    (physicalProfileExact = true <->
      runtimePrimitiveActualEntry model =
        runtimePrimitiveEntryBuilder model
          (runtimePrimitiveIdentity model)
          (runtimePrimitiveProfile model)) ->
    (noAssuranceEncoding = true <->
      runtimePrimitiveAssuranceIdentityEncoded model = false) ->
    decideRuntimePrimitiveIdentityByFacts
      physicalProfileExact noAssuranceEncoding = true <->
    RuntimePrimitiveIdentityVerificationSuccess model.
Proof.
  intros model physicalProfileExact noAssuranceEncoding Hentry HnoAssurance.
  unfold decideRuntimePrimitiveIdentityByFacts.
  rewrite andb_true_iff.
  rewrite Hentry, HnoAssurance.
  apply runtime_primitive_identity_facts_exact.
Qed.
