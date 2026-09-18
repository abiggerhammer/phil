From Phil.Core Require Import ArchitectureRealization.

(*
  PHIL-P1-REPLACE-001 — provider replacement integration witness.

  The aggregate row does not invent new provider-replacement semantics.  It
  composes the already Certified PHIL-PROV-REPLACE-001 qualification relation
  with the already Certified/Implementation-Refined PHIL-ARCH-REALIZE-001
  bridge for both sides of one exact architecture instance.

  Concrete Haskell identity derivation, Text/Map/Set representation,
  qualification evidence truth, target/provider behavior, and toolchain
  correctness remain explicit predecessor/correspondence boundaries.
*)

Definition ProviderReplacementIntegrationValid
  (prior replacement : ProviderReplacementSide)
  (reuseWitness : EvidenceReference -> option ProviderReplacementEvidenceReuse)
  (instance : ArchitectureInstanceIdentity)
  (priorSemantics replacementSemantics : nat)
  (encodeInstance : InstanceRevision -> nat)
  (encodeRealization : ArchitectureRealizationRevision -> nat) : Prop :=
  ValidProviderReplacement prior replacement reuseWitness /\
  ProviderSideMatchesArchitectureRealization
    prior
    instance
    (deriveArchitectureRealizationRevision instance priorSemantics)
    encodeInstance
    encodeRealization /\
  ProviderSideMatchesArchitectureRealization
    replacement
    instance
    (deriveArchitectureRealizationRevision instance replacementSemantics)
    encodeInstance
    encodeRealization.

Theorem integrated_replacement_has_two_independently_admitted_sides :
  forall prior replacement reuseWitness instance priorSemantics replacementSemantics
         encodeInstance encodeRealization,
    ProviderReplacementIntegrationValid
      prior replacement reuseWitness instance priorSemantics replacementSemantics
      encodeInstance encodeRealization ->
    replacementSideAdmitted prior = true /\
    replacementSideAdmitted replacement = true.
Proof.
  intros prior replacement reuseWitness instance priorSemantics replacementSemantics
    encodeInstance encodeRealization Hvalid.
  destruct Hvalid as [Hreplacement _].
  split.
  - apply prior_side_is_independently_admitted with
      (replacement := replacement) (reuseWitness := reuseWitness).
    exact Hreplacement.
  - apply replacement_side_is_independently_admitted with
      (prior := prior) (reuseWitness := reuseWitness).
    exact Hreplacement.
Qed.

Theorem integrated_replacement_preserves_exact_architecture_instance :
  forall prior replacement reuseWitness instance priorSemantics replacementSemantics
         encodeInstance encodeRealization,
    ProviderReplacementIntegrationValid
      prior replacement reuseWitness instance priorSemantics replacementSemantics
      encodeInstance encodeRealization ->
    replacementSideInstance prior =
      encodeInstance (identityInstanceRevision instance) /\
    replacementSideInstance replacement =
      encodeInstance (identityInstanceRevision instance) /\
    replacementSideInstance prior = replacementSideInstance replacement.
Proof.
  intros prior replacement reuseWitness instance priorSemantics replacementSemantics
    encodeInstance encodeRealization Hvalid.
  destruct Hvalid as [Hreplacement [Hprior Hnew]].
  destruct Hprior as [HpriorInstance _].
  destruct Hnew as [HnewInstance _].
  split.
  - exact HpriorInstance.
  - split.
    + exact HnewInstance.
    + exact (replacement_preserves_architecture_instance
        prior replacement reuseWitness Hreplacement).
Qed.

Theorem integrated_replacement_changes_architecture_realization :
  forall prior replacement reuseWitness instance priorSemantics replacementSemantics
         encodeInstance encodeRealization,
    ProviderReplacementIntegrationValid
      prior replacement reuseWitness instance priorSemantics replacementSemantics
      encodeInstance encodeRealization ->
    deriveArchitectureRealizationRevision instance priorSemantics <>
    deriveArchitectureRealizationRevision instance replacementSemantics.
Proof.
  intros prior replacement reuseWitness instance priorSemantics replacementSemantics
    encodeInstance encodeRealization Hvalid.
  destruct Hvalid as [Hreplacement [Hprior Hnew]].
  eapply provider_replacement_bridge_changes_architecture_realization.
  - exact Hreplacement.
  - exact Hprior.
  - exact Hnew.
Qed.

Theorem integrated_replacement_has_fresh_qualification_lineage :
  forall prior replacement reuseWitness instance priorSemantics replacementSemantics
         encodeInstance encodeRealization,
    ProviderReplacementIntegrationValid
      prior replacement reuseWitness instance priorSemantics replacementSemantics
      encodeInstance encodeRealization ->
    replacementSideClaim prior <> replacementSideClaim replacement /\
    replacementSideEvidence prior <> replacementSideEvidence replacement /\
    replacementSideAdmission prior <> replacementSideAdmission replacement.
Proof.
  intros prior replacement reuseWitness instance priorSemantics replacementSemantics
    encodeInstance encodeRealization Hvalid.
  destruct Hvalid as [Hreplacement _].
  exact (provider_replacement_requires_fresh_qualification_lineage
    prior replacement reuseWitness Hreplacement).
Qed.

Theorem integrated_replacement_preserves_public_interface_and_occurrence :
  forall prior replacement reuseWitness instance priorSemantics replacementSemantics
         encodeInstance encodeRealization,
    ProviderReplacementIntegrationValid
      prior replacement reuseWitness instance priorSemantics replacementSemantics
      encodeInstance encodeRealization ->
    replacementSideInterface prior = replacementSideInterface replacement /\
    replacementSideOccurrence prior = replacementSideOccurrence replacement.
Proof.
  intros prior replacement reuseWitness instance priorSemantics replacementSemantics
    encodeInstance encodeRealization Hvalid.
  destruct Hvalid as [Hreplacement _].
  split.
  - apply replacement_preserves_public_interface with
      (reuseWitness := reuseWitness).
    exact Hreplacement.
  - apply replacement_preserves_provider_occurrence with
      (reuseWitness := reuseWitness).
    exact Hreplacement.
Qed.

Theorem integrated_replacement_rejects_predecessor_evidence_inheritance :
  forall prior replacement reuseWitness instance priorSemantics replacementSemantics
         encodeInstance encodeRealization,
    replacementSideEvidence prior = replacementSideEvidence replacement ->
    ~ ProviderReplacementIntegrationValid
        prior replacement reuseWitness instance priorSemantics replacementSemantics
        encodeInstance encodeRealization.
Proof.
  intros prior replacement reuseWitness instance priorSemantics replacementSemantics
    encodeInstance encodeRealization Hsame Hvalid.
  destruct Hvalid as [Hreplacement _].
  eapply (predecessor_evidence_cannot_be_inherited
    prior replacement reuseWitness Hsame).
  exact Hreplacement.
Qed.

Theorem integrated_replacement_rejects_topology_change :
  forall prior replacement reuseWitness instance priorSemantics replacementSemantics
         encodeInstance encodeRealization,
    replacementSideInstance prior <> replacementSideInstance replacement ->
    ~ ProviderReplacementIntegrationValid
        prior replacement reuseWitness instance priorSemantics replacementSemantics
        encodeInstance encodeRealization.
Proof.
  intros prior replacement reuseWitness instance priorSemantics replacementSemantics
    encodeInstance encodeRealization Hdifferent Hvalid.
  destruct Hvalid as [Hreplacement _].
  eapply (topology_change_cannot_validate_as_provider_replacement
    prior replacement reuseWitness Hdifferent).
  exact Hreplacement.
Qed.

Theorem integrated_shared_evidence_requires_exact_scoped_reuse :
  forall prior replacement reuseWitness instance priorSemantics replacementSemantics
         encodeInstance encodeRealization reference,
    ProviderReplacementIntegrationValid
      prior replacement reuseWitness instance priorSemantics replacementSemantics
      encodeInstance encodeRealization ->
    SharedEvidence prior replacement reference ->
    exists reuse,
      reuseWitness reference = Some reuse /\
      replacementReuseReference reuse = reference /\
      ValidEvidenceReuse prior replacement reuse.
Proof.
  intros prior replacement reuseWitness instance priorSemantics replacementSemantics
    encodeInstance encodeRealization reference Hvalid Hshared.
  destruct Hvalid as [Hreplacement _].
  exact (shared_provider_evidence_requires_explicit_scoped_reuse
    prior replacement reuseWitness reference Hreplacement Hshared).
Qed.

Theorem integrated_replacement_deterministic_rebuild :
  forall instance semantics,
    deriveArchitectureRealizationRevision instance semantics =
    deriveArchitectureRealizationRevision instance semantics.
Proof.
  apply identical_selected_realization_rebuild_is_deterministic.
Qed.
