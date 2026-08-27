From Stdlib Require Import Bool.Bool.

(*
  PHIL-PROV-REPLACE-001 — bounded PROV-015 replacement qualification.

  A replacement is checked as two independently admitted provider subjects.
  The public interface, provider occurrence, and ArchitectureInstance stay
  fixed; subject, claim/evidence/admission lineage, and RealizationRevision
  must change. Evidence shared across the two claims is rejected unless one
  explicit reuse record binds that exact reference to both exact claim
  revisions under a nonempty validity scope.
*)

Definition InterfaceRevision := nat.
Definition ProviderOccurrence := nat.
Definition InstanceRevision := nat.
Definition RealizationRevision := nat.
Definition ProviderSubject := nat.
Definition QualificationLayer := nat.
Definition QualificationClaimRevision := nat.
Definition QualificationEvidenceRevision := nat.
Definition QualificationAdmissionRevision := nat.
Definition EvidenceReference := nat.

Record ProviderReplacementSide : Type := mkProviderReplacementSide {
  replacementSideInterface : InterfaceRevision;
  replacementSideOccurrence : ProviderOccurrence;
  replacementSideInstance : InstanceRevision;
  replacementSideRealization : RealizationRevision;
  replacementSideSubject : ProviderSubject;
  replacementSideLayer : QualificationLayer;
  replacementSideClaim : QualificationClaimRevision;
  replacementSideEvidence : QualificationEvidenceRevision;
  replacementSideAdmission : QualificationAdmissionRevision;
  replacementSideAdmitted : bool;
  replacementSideHasEvidence : EvidenceReference -> bool
}.

Record ProviderReplacementEvidenceReuse : Type := mkProviderReplacementEvidenceReuse {
  replacementReuseReference : EvidenceReference;
  replacementReusePriorClaim : QualificationClaimRevision;
  replacementReuseNewClaim : QualificationClaimRevision;
  replacementReuseHasValidityScope : bool
}.

Definition SharedEvidence
  (prior replacement : ProviderReplacementSide)
  (reference : EvidenceReference) : Prop :=
  replacementSideHasEvidence prior reference = true /\
  replacementSideHasEvidence replacement reference = true.

Record ValidEvidenceReuse
  (prior replacement : ProviderReplacementSide)
  (reuse : ProviderReplacementEvidenceReuse) : Prop :=
  mkValidEvidenceReuse {
    valid_reuse_prior_has_reference :
      replacementSideHasEvidence prior (replacementReuseReference reuse) = true;
    valid_reuse_new_has_reference :
      replacementSideHasEvidence replacement (replacementReuseReference reuse) = true;
    valid_reuse_prior_claim_exact :
      replacementReusePriorClaim reuse = replacementSideClaim prior;
    valid_reuse_new_claim_exact :
      replacementReuseNewClaim reuse = replacementSideClaim replacement;
    valid_reuse_scope_present :
      replacementReuseHasValidityScope reuse = true
  }.

Record ValidProviderReplacement
  (prior replacement : ProviderReplacementSide)
  (reuseWitness : EvidenceReference -> option ProviderReplacementEvidenceReuse) : Prop :=
  mkValidProviderReplacement {
    replacement_prior_admitted : replacementSideAdmitted prior = true;
    replacement_new_admitted : replacementSideAdmitted replacement = true;
    replacement_interface_fixed :
      replacementSideInterface prior = replacementSideInterface replacement;
    replacement_occurrence_fixed :
      replacementSideOccurrence prior = replacementSideOccurrence replacement;
    replacement_instance_fixed :
      replacementSideInstance prior = replacementSideInstance replacement;
    replacement_subject_changes :
      replacementSideSubject prior <> replacementSideSubject replacement;
    replacement_realization_changes :
      replacementSideRealization prior <> replacementSideRealization replacement;
    replacement_claim_changes :
      replacementSideClaim prior <> replacementSideClaim replacement;
    replacement_evidence_changes :
      replacementSideEvidence prior <> replacementSideEvidence replacement;
    replacement_admission_changes :
      replacementSideAdmission prior <> replacementSideAdmission replacement;
    replacement_shared_evidence_scoped :
      forall reference,
        SharedEvidence prior replacement reference ->
        exists reuse,
          reuseWitness reference = Some reuse /\
          replacementReuseReference reuse = reference /\
          ValidEvidenceReuse prior replacement reuse;
    replacement_no_spurious_reuse :
      forall reference reuse,
        reuseWitness reference = Some reuse ->
        replacementReuseReference reuse = reference /\
        ValidEvidenceReuse prior replacement reuse
  }.

Theorem prior_side_is_independently_admitted :
  forall prior replacement reuseWitness,
    ValidProviderReplacement prior replacement reuseWitness ->
    replacementSideAdmitted prior = true.
Proof.
  intros prior replacement reuseWitness Hvalid.
  exact (replacement_prior_admitted prior replacement reuseWitness Hvalid).
Qed.

Theorem replacement_side_is_independently_admitted :
  forall prior replacement reuseWitness,
    ValidProviderReplacement prior replacement reuseWitness ->
    replacementSideAdmitted replacement = true.
Proof.
  intros prior replacement reuseWitness Hvalid.
  exact (replacement_new_admitted prior replacement reuseWitness Hvalid).
Qed.

Theorem replacement_preserves_public_interface :
  forall prior replacement reuseWitness,
    ValidProviderReplacement prior replacement reuseWitness ->
    replacementSideInterface prior = replacementSideInterface replacement.
Proof.
  intros prior replacement reuseWitness Hvalid.
  exact (replacement_interface_fixed prior replacement reuseWitness Hvalid).
Qed.

Theorem replacement_preserves_provider_occurrence :
  forall prior replacement reuseWitness,
    ValidProviderReplacement prior replacement reuseWitness ->
    replacementSideOccurrence prior = replacementSideOccurrence replacement.
Proof.
  intros prior replacement reuseWitness Hvalid.
  exact (replacement_occurrence_fixed prior replacement reuseWitness Hvalid).
Qed.

Theorem replacement_preserves_architecture_instance :
  forall prior replacement reuseWitness,
    ValidProviderReplacement prior replacement reuseWitness ->
    replacementSideInstance prior = replacementSideInstance replacement.
Proof.
  intros prior replacement reuseWitness Hvalid.
  exact (replacement_instance_fixed prior replacement reuseWitness Hvalid).
Qed.

Theorem replacement_requires_distinct_subject :
  forall prior replacement reuseWitness,
    ValidProviderReplacement prior replacement reuseWitness ->
    replacementSideSubject prior <> replacementSideSubject replacement.
Proof.
  intros prior replacement reuseWitness Hvalid.
  exact (replacement_subject_changes prior replacement reuseWitness Hvalid).
Qed.

Theorem replacement_requires_new_realization_revision :
  forall prior replacement reuseWitness,
    ValidProviderReplacement prior replacement reuseWitness ->
    replacementSideRealization prior <> replacementSideRealization replacement.
Proof.
  intros prior replacement reuseWitness Hvalid.
  exact (replacement_realization_changes prior replacement reuseWitness Hvalid).
Qed.

Theorem replacement_requires_new_claim_lineage :
  forall prior replacement reuseWitness,
    ValidProviderReplacement prior replacement reuseWitness ->
    replacementSideClaim prior <> replacementSideClaim replacement.
Proof.
  intros prior replacement reuseWitness Hvalid.
  exact (replacement_claim_changes prior replacement reuseWitness Hvalid).
Qed.

Theorem replacement_requires_new_evidence_lineage :
  forall prior replacement reuseWitness,
    ValidProviderReplacement prior replacement reuseWitness ->
    replacementSideEvidence prior <> replacementSideEvidence replacement.
Proof.
  intros prior replacement reuseWitness Hvalid.
  exact (replacement_evidence_changes prior replacement reuseWitness Hvalid).
Qed.

Theorem replacement_requires_new_admission_lineage :
  forall prior replacement reuseWitness,
    ValidProviderReplacement prior replacement reuseWitness ->
    replacementSideAdmission prior <> replacementSideAdmission replacement.
Proof.
  intros prior replacement reuseWitness Hvalid.
  exact (replacement_admission_changes prior replacement reuseWitness Hvalid).
Qed.

Theorem same_subject_cannot_be_replacement :
  forall prior replacement reuseWitness,
    replacementSideSubject prior = replacementSideSubject replacement ->
    ~ ValidProviderReplacement prior replacement reuseWitness.
Proof.
  intros prior replacement reuseWitness Hsame Hvalid.
  apply (replacement_subject_changes prior replacement reuseWitness Hvalid).
  exact Hsame.
Qed.

Theorem unchanged_realization_cannot_be_replacement :
  forall prior replacement reuseWitness,
    replacementSideRealization prior = replacementSideRealization replacement ->
    ~ ValidProviderReplacement prior replacement reuseWitness.
Proof.
  intros prior replacement reuseWitness Hsame Hvalid.
  apply (replacement_realization_changes prior replacement reuseWitness Hvalid).
  exact Hsame.
Qed.

Theorem inherited_claim_lineage_cannot_be_replacement :
  forall prior replacement reuseWitness,
    replacementSideClaim prior = replacementSideClaim replacement ->
    ~ ValidProviderReplacement prior replacement reuseWitness.
Proof.
  intros prior replacement reuseWitness Hsame Hvalid.
  apply (replacement_claim_changes prior replacement reuseWitness Hvalid).
  exact Hsame.
Qed.

Theorem inherited_evidence_lineage_cannot_be_replacement :
  forall prior replacement reuseWitness,
    replacementSideEvidence prior = replacementSideEvidence replacement ->
    ~ ValidProviderReplacement prior replacement reuseWitness.
Proof.
  intros prior replacement reuseWitness Hsame Hvalid.
  apply (replacement_evidence_changes prior replacement reuseWitness Hvalid).
  exact Hsame.
Qed.

Theorem inherited_admission_lineage_cannot_be_replacement :
  forall prior replacement reuseWitness,
    replacementSideAdmission prior = replacementSideAdmission replacement ->
    ~ ValidProviderReplacement prior replacement reuseWitness.
Proof.
  intros prior replacement reuseWitness Hsame Hvalid.
  apply (replacement_admission_changes prior replacement reuseWitness Hvalid).
  exact Hsame.
Qed.

Theorem rejected_replacement_cannot_be_selected :
  forall prior replacement reuseWitness,
    replacementSideAdmitted replacement = false ->
    ~ ValidProviderReplacement prior replacement reuseWitness.
Proof.
  intros prior replacement reuseWitness Hrejected Hvalid.
  pose proof (replacement_new_admitted prior replacement reuseWitness Hvalid)
    as Hadmitted.
  rewrite Hrejected in Hadmitted.
  discriminate.
Qed.

Theorem shared_evidence_requires_explicit_reuse :
  forall prior replacement reuseWitness reference,
    ValidProviderReplacement prior replacement reuseWitness ->
    SharedEvidence prior replacement reference ->
    exists reuse,
      reuseWitness reference = Some reuse /\
      replacementReuseReference reuse = reference /\
      ValidEvidenceReuse prior replacement reuse.
Proof.
  intros prior replacement reuseWitness reference Hvalid Hshared.
  apply (replacement_shared_evidence_scoped
    prior replacement reuseWitness Hvalid reference).
  exact Hshared.
Qed.

Theorem shared_evidence_without_reuse_rejects :
  forall prior replacement reuseWitness reference,
    SharedEvidence prior replacement reference ->
    reuseWitness reference = None ->
    ~ ValidProviderReplacement prior replacement reuseWitness.
Proof.
  intros prior replacement reuseWitness reference Hshared Hnone Hvalid.
  pose proof (shared_evidence_requires_explicit_reuse
    prior replacement reuseWitness reference Hvalid Hshared) as Hexists.
  destruct Hexists as [reuse [Hsome _]].
  rewrite Hnone in Hsome.
  discriminate.
Qed.

Theorem reuse_requires_nonempty_validity_scope :
  forall prior replacement reuse,
    ValidEvidenceReuse prior replacement reuse ->
    replacementReuseHasValidityScope reuse = true.
Proof.
  intros prior replacement reuse Hreuse.
  exact (valid_reuse_scope_present prior replacement reuse Hreuse).
Qed.

Theorem reuse_binds_exact_claim_pair :
  forall prior replacement reuse,
    ValidEvidenceReuse prior replacement reuse ->
    replacementReusePriorClaim reuse = replacementSideClaim prior /\
    replacementReuseNewClaim reuse = replacementSideClaim replacement.
Proof.
  intros prior replacement reuse Hreuse.
  split.
  - exact (valid_reuse_prior_claim_exact prior replacement reuse Hreuse).
  - exact (valid_reuse_new_claim_exact prior replacement reuse Hreuse).
Qed.

Theorem reuse_justification_names_actually_shared_evidence :
  forall prior replacement reuse,
    ValidEvidenceReuse prior replacement reuse ->
    SharedEvidence prior replacement (replacementReuseReference reuse).
Proof.
  intros prior replacement reuse Hreuse.
  split.
  - exact (valid_reuse_prior_has_reference prior replacement reuse Hreuse).
  - exact (valid_reuse_new_has_reference prior replacement reuse Hreuse).
Qed.

Theorem unexpected_reuse_justification_cannot_validate :
  forall prior replacement reuseWitness reference reuse,
    reuseWitness reference = Some reuse ->
    ~ SharedEvidence prior replacement reference ->
    ~ ValidProviderReplacement prior replacement reuseWitness.
Proof.
  intros prior replacement reuseWitness reference reuse Hlookup HnotShared Hvalid.
  pose proof (replacement_no_spurious_reuse
    prior replacement reuseWitness Hvalid reference reuse Hlookup)
    as Hvalidated.
  destruct Hvalidated as [Href Hreuse].
  pose proof (reuse_justification_names_actually_shared_evidence
    prior replacement reuse Hreuse) as HsharedReuse.
  destruct HsharedReuse as [Hprior Hnew].
  apply HnotShared.
  unfold SharedEvidence.
  rewrite <- Href.
  split; assumption.
Qed.

Definition withReplacementLayer
  (layer : QualificationLayer)
  (side : ProviderReplacementSide) : ProviderReplacementSide :=
  mkProviderReplacementSide
    (replacementSideInterface side)
    (replacementSideOccurrence side)
    (replacementSideInstance side)
    (replacementSideRealization side)
    (replacementSideSubject side)
    layer
    (replacementSideClaim side)
    (replacementSideEvidence side)
    (replacementSideAdmission side)
    (replacementSideAdmitted side)
    (replacementSideHasEvidence side).

Theorem qualification_layer_is_not_a_replacement_invariant :
  forall prior replacement reuseWitness priorLayer replacementLayer,
    ValidProviderReplacement prior replacement reuseWitness ->
    ValidProviderReplacement
      (withReplacementLayer priorLayer prior)
      (withReplacementLayer replacementLayer replacement)
      reuseWitness.
Proof.
  intros prior replacement reuseWitness priorLayer replacementLayer Hvalid.
  destruct Hvalid as
    [HpriorAdmitted HnewAdmitted Hinterface Hoccurrence Hinstance Hsubject
     Hrealization Hclaim Hevidence Hadmission Hshared Hreuse].
  constructor; simpl in *; try assumption.
  - intros reference Hshared'.
    apply Hshared.
    exact Hshared'.
  - intros reference reuse Hlookup.
    apply Hreuse.
    exact Hlookup.
Qed.
