From Stdlib Require Import Arith.PeanoNat.

From Phil.Core Require Import ArchitectureIdentity SystemsStageClosure.
From Phil.Systems Require Import Identity.

(*
  PHIL-SYS-REV-001 — canonical SystemsArtifact / StageContract revision algebra.

  This is a representation-neutral model of the Phase-1 identity boundary in
  Phil.Systems.Phase1Stage.  Concrete Text/Map/Set/list normalization,
  canonical SemanticForm serialization, SHA-256 construction, and digest
  collision resistance remain explicit implementation/cryptographic
  correspondence boundaries.

  The model separates identity-bearing semantic inputs from presentation-only
  metadata.  Canonical revisions are defined over the semantic projection only.
  Thus reconstruction and presentation/order changes are provably inert, while
  changing any identity-bearing component changes the abstract canonical
  revision.  Reflection of those abstract inequalities through concrete
  serialization/hash values remains the ADR-019 residual boundary.
*)

Record SystemsRevisionInput : Type := mkSystemsRevisionInput {
  systemsRevisionSourceSemantics : nat;
  systemsRevisionProgramSemantics : nat;
  systemsRevisionStageContractSemantics : nat;
  systemsRevisionLoweringSemantics : nat;

  (* Deliberately non-identity-bearing metadata. *)
  systemsRevisionSourceFormatting : nat;
  systemsRevisionDiagnosticPresentation : nat;
  systemsRevisionContainerOrder : nat;
  systemsRevisionBackendSymbolSpelling : nat
}.

Record SystemsCanonicalRevision : Type := mkSystemsCanonicalRevision {
  canonicalSystemsSourceSemantics : nat;
  canonicalSystemsProgramSemantics : nat;
  canonicalSystemsStageContractSemantics : nat;
  canonicalSystemsLoweringSemantics : nat
}.

Definition deriveSystemsCanonicalRevision
  (input : SystemsRevisionInput) : SystemsCanonicalRevision :=
  mkSystemsCanonicalRevision
    (systemsRevisionSourceSemantics input)
    (systemsRevisionProgramSemantics input)
    (systemsRevisionStageContractSemantics input)
    (systemsRevisionLoweringSemantics input).

Theorem systems_revision_ignores_nonsemantic_metadata :
  forall first second,
    systemsRevisionSourceSemantics first = systemsRevisionSourceSemantics second ->
    systemsRevisionProgramSemantics first = systemsRevisionProgramSemantics second ->
    systemsRevisionStageContractSemantics first =
      systemsRevisionStageContractSemantics second ->
    systemsRevisionLoweringSemantics first = systemsRevisionLoweringSemantics second ->
    deriveSystemsCanonicalRevision first = deriveSystemsCanonicalRevision second.
Proof.
  intros first second Hsource Hprogram Hstage Hlowering.
  unfold deriveSystemsCanonicalRevision.
  rewrite Hsource, Hprogram, Hstage, Hlowering.
  reflexivity.
Qed.

Theorem identical_systems_reconstruction_is_deterministic :
  forall input,
    deriveSystemsCanonicalRevision input = deriveSystemsCanonicalRevision input.
Proof.
  reflexivity.
Qed.

Theorem systems_revision_equality_reflects_identity_bearing_semantics :
  forall first second,
    deriveSystemsCanonicalRevision first = deriveSystemsCanonicalRevision second ->
    systemsRevisionSourceSemantics first = systemsRevisionSourceSemantics second /\
    systemsRevisionProgramSemantics first = systemsRevisionProgramSemantics second /\
    systemsRevisionStageContractSemantics first =
      systemsRevisionStageContractSemantics second /\
    systemsRevisionLoweringSemantics first = systemsRevisionLoweringSemantics second.
Proof.
  intros first second Heq.
  repeat split.
  - exact (f_equal canonicalSystemsSourceSemantics Heq).
  - exact (f_equal canonicalSystemsProgramSemantics Heq).
  - exact (f_equal canonicalSystemsStageContractSemantics Heq).
  - exact (f_equal canonicalSystemsLoweringSemantics Heq).
Qed.

Theorem systems_source_semantic_change_revises_identity :
  forall first second,
    systemsRevisionSourceSemantics first <> systemsRevisionSourceSemantics second ->
    deriveSystemsCanonicalRevision first <> deriveSystemsCanonicalRevision second.
Proof.
  intros first second Hdifferent Heq.
  apply Hdifferent.
  exact (f_equal canonicalSystemsSourceSemantics Heq).
Qed.

Theorem systems_program_semantic_change_revises_identity :
  forall first second,
    systemsRevisionProgramSemantics first <> systemsRevisionProgramSemantics second ->
    deriveSystemsCanonicalRevision first <> deriveSystemsCanonicalRevision second.
Proof.
  intros first second Hdifferent Heq.
  apply Hdifferent.
  exact (f_equal canonicalSystemsProgramSemantics Heq).
Qed.

Theorem systems_stage_contract_semantic_change_revises_identity :
  forall first second,
    systemsRevisionStageContractSemantics first <>
      systemsRevisionStageContractSemantics second ->
    deriveSystemsCanonicalRevision first <> deriveSystemsCanonicalRevision second.
Proof.
  intros first second Hdifferent Heq.
  apply Hdifferent.
  exact (f_equal canonicalSystemsStageContractSemantics Heq).
Qed.

Theorem systems_lowering_semantic_change_revises_identity :
  forall first second,
    systemsRevisionLoweringSemantics first <> systemsRevisionLoweringSemantics second ->
    deriveSystemsCanonicalRevision first <> deriveSystemsCanonicalRevision second.
Proof.
  intros first second Hdifferent Heq.
  apply Hdifferent.
  exact (f_equal canonicalSystemsLoweringSemantics Heq).
Qed.

Record StageRevisionInput : Type := mkStageRevisionInput {
  stageRevisionArchitectureInstance : ArchitectureInstanceIdentity;
  stageRevisionRealization : nat;
  stageRevisionSystems : SystemsCanonicalRevision;
  stageRevisionVerifierProfile : nat;
  stageRevisionSourceFacts : nat;
  stageRevisionDispositions : nat;
  stageRevisionMechanisms : nat;
  stageRevisionJustifications : nat;

  (* Deliberately non-identity-bearing metadata. *)
  stageRevisionSourceFormatting : nat;
  stageRevisionDiagnosticPresentation : nat;
  stageRevisionContainerOrder : nat;
  stageRevisionBackendSymbolSpelling : nat
}.

Record StageCanonicalRevision : Type := mkStageCanonicalRevision {
  canonicalStageArchitectureInstance : ArchitectureInstanceIdentity;
  canonicalStageRealization : nat;
  canonicalStageSystems : SystemsCanonicalRevision;
  canonicalStageVerifierProfile : nat;
  canonicalStageSourceFacts : nat;
  canonicalStageDispositions : nat;
  canonicalStageMechanisms : nat;
  canonicalStageJustifications : nat
}.

Definition deriveStageCanonicalRevision
  (input : StageRevisionInput) : StageCanonicalRevision :=
  mkStageCanonicalRevision
    (stageRevisionArchitectureInstance input)
    (stageRevisionRealization input)
    (stageRevisionSystems input)
    (stageRevisionVerifierProfile input)
    (stageRevisionSourceFacts input)
    (stageRevisionDispositions input)
    (stageRevisionMechanisms input)
    (stageRevisionJustifications input).

Theorem stage_revision_ignores_nonsemantic_metadata :
  forall first second,
    stageRevisionArchitectureInstance first = stageRevisionArchitectureInstance second ->
    stageRevisionRealization first = stageRevisionRealization second ->
    stageRevisionSystems first = stageRevisionSystems second ->
    stageRevisionVerifierProfile first = stageRevisionVerifierProfile second ->
    stageRevisionSourceFacts first = stageRevisionSourceFacts second ->
    stageRevisionDispositions first = stageRevisionDispositions second ->
    stageRevisionMechanisms first = stageRevisionMechanisms second ->
    stageRevisionJustifications first = stageRevisionJustifications second ->
    deriveStageCanonicalRevision first = deriveStageCanonicalRevision second.
Proof.
  intros first second Hinstance Hrealization Hsystems Hprofile
    Hfacts Hdispositions Hmechanisms Hjustifications.
  unfold deriveStageCanonicalRevision.
  rewrite Hinstance, Hrealization, Hsystems, Hprofile,
    Hfacts, Hdispositions, Hmechanisms, Hjustifications.
  reflexivity.
Qed.

Theorem identical_stage_reconstruction_is_deterministic :
  forall input,
    deriveStageCanonicalRevision input = deriveStageCanonicalRevision input.
Proof.
  reflexivity.
Qed.

Theorem stage_revision_equality_reflects_identity_bearing_semantics :
  forall first second,
    deriveStageCanonicalRevision first = deriveStageCanonicalRevision second ->
    stageRevisionArchitectureInstance first = stageRevisionArchitectureInstance second /\
    stageRevisionRealization first = stageRevisionRealization second /\
    stageRevisionSystems first = stageRevisionSystems second /\
    stageRevisionVerifierProfile first = stageRevisionVerifierProfile second /\
    stageRevisionSourceFacts first = stageRevisionSourceFacts second /\
    stageRevisionDispositions first = stageRevisionDispositions second /\
    stageRevisionMechanisms first = stageRevisionMechanisms second /\
    stageRevisionJustifications first = stageRevisionJustifications second.
Proof.
  intros first second Heq.
  repeat split.
  - exact (f_equal canonicalStageArchitectureInstance Heq).
  - exact (f_equal canonicalStageRealization Heq).
  - exact (f_equal canonicalStageSystems Heq).
  - exact (f_equal canonicalStageVerifierProfile Heq).
  - exact (f_equal canonicalStageSourceFacts Heq).
  - exact (f_equal canonicalStageDispositions Heq).
  - exact (f_equal canonicalStageMechanisms Heq).
  - exact (f_equal canonicalStageJustifications Heq).
Qed.

Theorem architecture_instance_change_revises_stage_identity :
  forall first second,
    stageRevisionArchitectureInstance first <> stageRevisionArchitectureInstance second ->
    deriveStageCanonicalRevision first <> deriveStageCanonicalRevision second.
Proof.
  intros first second Hdifferent Heq.
  apply Hdifferent.
  exact (f_equal canonicalStageArchitectureInstance Heq).
Qed.

Theorem realization_change_revises_stage_identity :
  forall first second,
    stageRevisionRealization first <> stageRevisionRealization second ->
    deriveStageCanonicalRevision first <> deriveStageCanonicalRevision second.
Proof.
  intros first second Hdifferent Heq.
  apply Hdifferent.
  exact (f_equal canonicalStageRealization Heq).
Qed.

Theorem systems_revision_change_revises_stage_identity :
  forall first second,
    stageRevisionSystems first <> stageRevisionSystems second ->
    deriveStageCanonicalRevision first <> deriveStageCanonicalRevision second.
Proof.
  intros first second Hdifferent Heq.
  apply Hdifferent.
  exact (f_equal canonicalStageSystems Heq).
Qed.

Theorem verifier_profile_change_revises_stage_identity :
  forall first second,
    stageRevisionVerifierProfile first <> stageRevisionVerifierProfile second ->
    deriveStageCanonicalRevision first <> deriveStageCanonicalRevision second.
Proof.
  intros first second Hdifferent Heq.
  apply Hdifferent.
  exact (f_equal canonicalStageVerifierProfile Heq).
Qed.

Theorem source_fact_change_revises_stage_identity :
  forall first second,
    stageRevisionSourceFacts first <> stageRevisionSourceFacts second ->
    deriveStageCanonicalRevision first <> deriveStageCanonicalRevision second.
Proof.
  intros first second Hdifferent Heq.
  apply Hdifferent.
  exact (f_equal canonicalStageSourceFacts Heq).
Qed.

Theorem disposition_change_revises_stage_identity :
  forall first second,
    stageRevisionDispositions first <> stageRevisionDispositions second ->
    deriveStageCanonicalRevision first <> deriveStageCanonicalRevision second.
Proof.
  intros first second Hdifferent Heq.
  apply Hdifferent.
  exact (f_equal canonicalStageDispositions Heq).
Qed.

Theorem mechanism_change_revises_stage_identity :
  forall first second,
    stageRevisionMechanisms first <> stageRevisionMechanisms second ->
    deriveStageCanonicalRevision first <> deriveStageCanonicalRevision second.
Proof.
  intros first second Hdifferent Heq.
  apply Hdifferent.
  exact (f_equal canonicalStageMechanisms Heq).
Qed.

Theorem justification_change_revises_stage_identity :
  forall first second,
    stageRevisionJustifications first <> stageRevisionJustifications second ->
    deriveStageCanonicalRevision first <> deriveStageCanonicalRevision second.
Proof.
  intros first second Hdifferent Heq.
  apply Hdifferent.
  exact (f_equal canonicalStageJustifications Heq).
Qed.

(* PHIL-ARCH-ID-001 composes at the ArchitectureInstanceIdentity field: once
   that predecessor says two presentations denote one exact instance identity,
   all remaining equal semantic fields produce one exact stage revision. *)
Theorem certified_architecture_identity_can_flow_without_stage_rekeying :
  forall first second,
    stageRevisionArchitectureInstance first = stageRevisionArchitectureInstance second ->
    stageRevisionRealization first = stageRevisionRealization second ->
    stageRevisionSystems first = stageRevisionSystems second ->
    stageRevisionVerifierProfile first = stageRevisionVerifierProfile second ->
    stageRevisionSourceFacts first = stageRevisionSourceFacts second ->
    stageRevisionDispositions first = stageRevisionDispositions second ->
    stageRevisionMechanisms first = stageRevisionMechanisms second ->
    stageRevisionJustifications first = stageRevisionJustifications second ->
    deriveStageCanonicalRevision first = deriveStageCanonicalRevision second.
Proof.
  exact stage_revision_ignores_nonsemantic_metadata.
Qed.

(* PHIL-SYS-ID-001 and PHIL-SYS-STAGE-CLOSURE-001 jointly bind the abstract
   canonical revision to the already verified artifact and final closure gates.
   Digests remain opaque: this theorem states equality composition only. *)
Theorem certified_identity_predecessors_bind_recomputed_revisions :
  forall model closure systemsDigest finalRevision,
    ArtifactIdentityVerified model ->
    StageClosureIdentityValid closure ->
    computedSystemsArtifact model = systemsDigest ->
    closureRecomputedSystemsRevision closure = systemsDigest ->
    closureRecomputedFinalRevision closure = finalRevision ->
    manifestImplementationArtifact model = systemsDigest /\
    closureStoredSystemsRevision closure = systemsDigest /\
    closureStoredFinalRevision closure = finalRevision.
Proof.
  intros model closure systemsDigest finalRevision Hartifact Hclosure
    Hcomputed HrecomputedSystems HrecomputedFinal.
  split.
  - etransitivity.
    + apply verified_manifest_binds_complete_systems_artifact.
      exact Hartifact.
    + exact Hcomputed.
  - destruct (final_stage_closure_recomputes_stored_identities closure Hclosure)
      as [HstoredSystems HstoredFinal].
    split.
    + rewrite <- HstoredSystems.
      exact HrecomputedSystems.
    + rewrite <- HstoredFinal.
      exact HrecomputedFinal.
Qed.
