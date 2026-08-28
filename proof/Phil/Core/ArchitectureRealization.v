From Phil.Core Require Import ArchitectureInstantiation.
From Phil.Core Require ProviderReplacementQualification.

(*
  PHIL-ARCH-REALIZE-001 — representation-neutral ARCH-010 realization
  replacement semantics.

  The abstract architecture occurrence is identity-bearing independently of
  the selected realization.  A realization revision records that exact
  architecture instance together with the selected realization semantics.
  Provider replacement supplies the independently Certified replacement
  invariants: exact InstanceRevision preservation, new RealizationRevision,
  fresh qualification/evidence/admission lineage, and explicit scoped reuse
  for any shared evidence.
*)

Record ArchitectureRealizationRevision : Type := {
  realizationRevisionInstanceKey : InstanceKey;
  realizationRevisionInstance : InstanceRevision;
  realizationRevisionSemantics : nat
}.

Definition deriveArchitectureRealizationRevision
  (instance : ArchitectureInstanceIdentity)
  (semantics : nat) : ArchitectureRealizationRevision :=
  {| realizationRevisionInstanceKey := identityInstanceKey instance;
     realizationRevisionInstance := identityInstanceRevision instance;
     realizationRevisionSemantics := semantics |}.

Theorem realization_preserves_exact_architecture_instance_key :
  forall instance semantics,
    realizationRevisionInstanceKey
      (deriveArchitectureRealizationRevision instance semantics) =
    identityInstanceKey instance.
Proof.
  reflexivity.
Qed.

Theorem realization_preserves_exact_architecture_instance_revision :
  forall instance semantics,
    realizationRevisionInstance
      (deriveArchitectureRealizationRevision instance semantics) =
    identityInstanceRevision instance.
Proof.
  reflexivity.
Qed.

Theorem identical_selected_realization_rebuild_is_deterministic :
  forall instance semantics,
    deriveArchitectureRealizationRevision instance semantics =
    deriveArchitectureRealizationRevision instance semantics.
Proof.
  reflexivity.
Qed.

Theorem selected_realization_change_revises_realization :
  forall instance priorSemantics replacementSemantics,
    priorSemantics <> replacementSemantics ->
    deriveArchitectureRealizationRevision instance priorSemantics <>
    deriveArchitectureRealizationRevision instance replacementSemantics.
Proof.
  intros instance priorSemantics replacementSemantics Hneq Heq.
  apply Hneq.
  exact (f_equal realizationRevisionSemantics Heq).
Qed.

Theorem abstract_instance_key_change_revises_realization :
  forall priorInstance replacementInstance semantics,
    identityInstanceKey priorInstance <> identityInstanceKey replacementInstance ->
    deriveArchitectureRealizationRevision priorInstance semantics <>
    deriveArchitectureRealizationRevision replacementInstance semantics.
Proof.
  intros priorInstance replacementInstance semantics Hneq Heq.
  apply Hneq.
  exact (f_equal realizationRevisionInstanceKey Heq).
Qed.

Theorem abstract_instance_revision_change_revises_realization :
  forall priorInstance replacementInstance semantics,
    identityInstanceRevision priorInstance <>
      identityInstanceRevision replacementInstance ->
    deriveArchitectureRealizationRevision priorInstance semantics <>
    deriveArchitectureRealizationRevision replacementInstance semantics.
Proof.
  intros priorInstance replacementInstance semantics Hneq Heq.
  apply Hneq.
  exact (f_equal realizationRevisionInstance Heq).
Qed.

Definition ProviderSideMatchesArchitectureRealization
  (side : ProviderReplacementQualification.ProviderReplacementSide)
  (instance : ArchitectureInstanceIdentity)
  (realization : ArchitectureRealizationRevision)
  (encodeInstance : InstanceRevision -> nat)
  (encodeRealization : ArchitectureRealizationRevision -> nat) : Prop :=
  ProviderReplacementQualification.replacementSideInstance side =
      encodeInstance (identityInstanceRevision instance) /\
  ProviderReplacementQualification.replacementSideRealization side =
      encodeRealization realization.

Theorem certified_provider_replacement_preserves_instance_revision :
  forall prior replacement reuseWitness,
    ProviderReplacementQualification.ValidProviderReplacement
      prior replacement reuseWitness ->
    ProviderReplacementQualification.replacementSideInstance prior =
    ProviderReplacementQualification.replacementSideInstance replacement.
Proof.
  intros prior replacement reuseWitness Hvalid.
  exact (ProviderReplacementQualification.replacement_preserves_architecture_instance
    prior replacement reuseWitness Hvalid).
Qed.

Theorem certified_provider_replacement_requires_new_realization_revision :
  forall prior replacement reuseWitness,
    ProviderReplacementQualification.ValidProviderReplacement
      prior replacement reuseWitness ->
    ProviderReplacementQualification.replacementSideRealization prior <>
    ProviderReplacementQualification.replacementSideRealization replacement.
Proof.
  intros prior replacement reuseWitness Hvalid.
  exact (ProviderReplacementQualification.replacement_requires_new_realization_revision
    prior replacement reuseWitness Hvalid).
Qed.

Theorem provider_replacement_bridge_changes_architecture_realization :
  forall prior replacement reuseWitness instance
         priorSemantics replacementSemantics encodeInstance encodeRealization,
    ProviderReplacementQualification.ValidProviderReplacement
      prior replacement reuseWitness ->
    ProviderSideMatchesArchitectureRealization
      prior instance
      (deriveArchitectureRealizationRevision instance priorSemantics)
      encodeInstance encodeRealization ->
    ProviderSideMatchesArchitectureRealization
      replacement instance
      (deriveArchitectureRealizationRevision instance replacementSemantics)
      encodeInstance encodeRealization ->
    deriveArchitectureRealizationRevision instance priorSemantics <>
    deriveArchitectureRealizationRevision instance replacementSemantics.
Proof.
  intros prior replacement reuseWitness instance
    priorSemantics replacementSemantics encodeInstance encodeRealization
    Hvalid Hprior Hreplacement Heq.
  destruct Hprior as [_ HpriorRealization].
  destruct Hreplacement as [_ HreplacementRealization].
  apply (ProviderReplacementQualification.replacement_requires_new_realization_revision
    prior replacement reuseWitness Hvalid).
  rewrite HpriorRealization, HreplacementRealization.
  rewrite Heq.
  reflexivity.
Qed.

Theorem provider_replacement_bridge_preserves_exact_instance_revision :
  forall prior replacement reuseWitness priorInstance replacementInstance
         priorRealization replacementRealization encodeInstance encodeRealization,
    (forall left right,
      encodeInstance left = encodeInstance right -> left = right) ->
    ProviderReplacementQualification.ValidProviderReplacement
      prior replacement reuseWitness ->
    ProviderSideMatchesArchitectureRealization
      prior priorInstance priorRealization encodeInstance encodeRealization ->
    ProviderSideMatchesArchitectureRealization
      replacement replacementInstance replacementRealization
      encodeInstance encodeRealization ->
    identityInstanceRevision priorInstance =
    identityInstanceRevision replacementInstance.
Proof.
  intros prior replacement reuseWitness priorInstance replacementInstance
    priorRealization replacementRealization encodeInstance encodeRealization
    HencodeInjective Hvalid Hprior Hreplacement.
  destruct Hprior as [HpriorInstance _].
  destruct Hreplacement as [HreplacementInstance _].
  apply HencodeInjective.
  rewrite <- HpriorInstance, <- HreplacementInstance.
  exact (ProviderReplacementQualification.replacement_preserves_architecture_instance
    prior replacement reuseWitness Hvalid).
Qed.

Theorem topology_change_cannot_validate_as_provider_replacement :
  forall prior replacement reuseWitness,
    ProviderReplacementQualification.replacementSideInstance prior <>
      ProviderReplacementQualification.replacementSideInstance replacement ->
    ~ ProviderReplacementQualification.ValidProviderReplacement
        prior replacement reuseWitness.
Proof.
  intros prior replacement reuseWitness Hinstance Hvalid.
  apply Hinstance.
  exact (ProviderReplacementQualification.replacement_preserves_architecture_instance
    prior replacement reuseWitness Hvalid).
Qed.

Theorem provider_replacement_requires_fresh_qualification_lineage :
  forall prior replacement reuseWitness,
    ProviderReplacementQualification.ValidProviderReplacement
      prior replacement reuseWitness ->
    ProviderReplacementQualification.replacementSideClaim prior <>
      ProviderReplacementQualification.replacementSideClaim replacement /\
    ProviderReplacementQualification.replacementSideEvidence prior <>
      ProviderReplacementQualification.replacementSideEvidence replacement /\
    ProviderReplacementQualification.replacementSideAdmission prior <>
      ProviderReplacementQualification.replacementSideAdmission replacement.
Proof.
  intros prior replacement reuseWitness Hvalid.
  repeat split.
  - exact (ProviderReplacementQualification.replacement_requires_new_claim_lineage
      prior replacement reuseWitness Hvalid).
  - exact (ProviderReplacementQualification.replacement_requires_new_evidence_lineage
      prior replacement reuseWitness Hvalid).
  - exact (ProviderReplacementQualification.replacement_requires_new_admission_lineage
      prior replacement reuseWitness Hvalid).
Qed.

Theorem predecessor_evidence_cannot_be_inherited :
  forall prior replacement reuseWitness,
    ProviderReplacementQualification.replacementSideEvidence prior =
      ProviderReplacementQualification.replacementSideEvidence replacement ->
    ~ ProviderReplacementQualification.ValidProviderReplacement
        prior replacement reuseWitness.
Proof.
  intros prior replacement reuseWitness Hsame.
  exact (ProviderReplacementQualification.inherited_evidence_lineage_cannot_be_replacement
    prior replacement reuseWitness Hsame).
Qed.

Theorem shared_provider_evidence_requires_explicit_scoped_reuse :
  forall prior replacement reuseWitness reference,
    ProviderReplacementQualification.ValidProviderReplacement
      prior replacement reuseWitness ->
    ProviderReplacementQualification.SharedEvidence prior replacement reference ->
    exists reuse,
      reuseWitness reference = Some reuse /\
      ProviderReplacementQualification.replacementReuseReference reuse = reference /\
      ProviderReplacementQualification.ValidEvidenceReuse prior replacement reuse.
Proof.
  intros prior replacement reuseWitness reference Hvalid Hshared.
  exact (ProviderReplacementQualification.shared_evidence_requires_explicit_reuse
    prior replacement reuseWitness reference Hvalid Hshared).
Qed.
