From Stdlib Require Import Arith.PeanoNat.

From Phil.Assurance Require Import ValidityScope GenericAssurance.

(*
  PHIL-VERIFY-REUSE-001 — exact evidence reuse and invalidation.

  VER-006 stores already-checked proof evidence together with:

  - the exact target obligation revision;
  - the exact direct dependency-revision set captured from the graph where the
    evidence was accepted; and
  - an explicit ADR-010 validity scope.

  Reuse deliberately does not require whole-graph identity.  A current graph
  may contain unrelated edits and an effective validity context may contain
  extra unbound dimensions.  Reuse remains sound exactly while the target is
  still present and in certification scope, the target's direct dependency set
  is extensionally unchanged, and every validity dimension bound by the cached
  evidence still has its exact expected value.

  The concrete Haskell representation uses Digest/RevisionId, Set, Map, and
  ValidityScope.  This file owns the normalized semantic relation; concrete
  hashing, Text/Map/Set correspondence, diagnostic ordering, and checker truth
  remain explicit representation/predecessor boundaries.
*)

Definition VerificationGraphRevision := nat.
Definition VerificationRevision := nat.
Definition VerificationRevisionSet := VerificationRevision -> Prop.

Definition VerificationRevisionSetEquivalent
  (left right : VerificationRevisionSet) : Prop :=
  forall revision, left revision <-> right revision.

Record CheckedVerificationEvidence : Type := mkCheckedVerificationEvidence {
  checkedVerificationGraphRevision : VerificationGraphRevision;
  checkedVerificationTargetRevision : VerificationRevision
}.

Record ReusableVerificationEvidence : Type := mkReusableVerificationEvidence {
  reusableVerificationCheckedEvidence : CheckedVerificationEvidence;
  reusableVerificationDependencies : VerificationRevisionSet;
  reusableVerificationValidityScope : ValidityMap
}.

Record VerificationReuseContext : Type := mkVerificationReuseContext {
  verificationReuseGraphRevision : VerificationGraphRevision;
  verificationReuseRevisions : VerificationRevisionSet;
  verificationReuseCertificationScope : VerificationRevisionSet;
  verificationReuseDependencies : VerificationRevision -> VerificationRevisionSet;
  verificationReuseValidityContext : ValidityMap
}.

Definition PreparedReusableVerificationEvidence
  (source : VerificationReuseContext)
  (validityScope : ValidityMap)
  (checked : CheckedVerificationEvidence)
  (reusable : ReusableVerificationEvidence) : Prop :=
  reusableVerificationCheckedEvidence reusable = checked /\
  checkedVerificationGraphRevision checked = verificationReuseGraphRevision source /\
  verificationReuseRevisions source (checkedVerificationTargetRevision checked) /\
  verificationReuseCertificationScope source (checkedVerificationTargetRevision checked) /\
  VerificationRevisionSetEquivalent
    (reusableVerificationDependencies reusable)
    (verificationReuseDependencies source (checkedVerificationTargetRevision checked)) /\
  reusableVerificationValidityScope reusable = validityScope.

Definition VerificationEvidenceReusable
  (reusable : ReusableVerificationEvidence)
  (current : VerificationReuseContext) : Prop :=
  let target :=
    checkedVerificationTargetRevision
      (reusableVerificationCheckedEvidence reusable) in
  verificationReuseRevisions current target /\
  verificationReuseCertificationScope current target /\
  VerificationRevisionSetEquivalent
    (reusableVerificationDependencies reusable)
    (verificationReuseDependencies current target) /\
  ScopeMatches
    (reusableVerificationValidityScope reusable)
    (verificationReuseValidityContext current).

Theorem preparation_binds_the_exact_acceptance_graph_revision :
  forall source validityScope checked reusable,
    PreparedReusableVerificationEvidence source validityScope checked reusable ->
    checkedVerificationGraphRevision checked = verificationReuseGraphRevision source.
Proof.
  intros source validityScope checked reusable Hprepared.
  destruct Hprepared as [_ [Hgraph _]].
  exact Hgraph.
Qed.

Theorem changed_graph_cannot_rebind_checked_evidence_during_preparation :
  forall source validityScope checked reusable,
    checkedVerificationGraphRevision checked <>
      verificationReuseGraphRevision source ->
    ~ PreparedReusableVerificationEvidence source validityScope checked reusable.
Proof.
  intros source validityScope checked reusable Hchanged Hprepared.
  apply Hchanged.
  eapply preparation_binds_the_exact_acceptance_graph_revision.
  exact Hprepared.
Qed.

Theorem preparation_captures_the_exact_direct_dependency_set :
  forall source validityScope checked reusable,
    PreparedReusableVerificationEvidence source validityScope checked reusable ->
    VerificationRevisionSetEquivalent
      (reusableVerificationDependencies reusable)
      (verificationReuseDependencies source (checkedVerificationTargetRevision checked)).
Proof.
  intros source validityScope checked reusable Hprepared.
  destruct Hprepared as [_ [_ [_ [_ [Hdependencies _]]]]].
  exact Hdependencies.
Qed.

Theorem reusable_evidence_requires_target_presence :
  forall reusable current,
    VerificationEvidenceReusable reusable current ->
    verificationReuseRevisions current
      (checkedVerificationTargetRevision
        (reusableVerificationCheckedEvidence reusable)).
Proof.
  intros reusable current Hreusable.
  unfold VerificationEvidenceReusable in Hreusable.
  exact (proj1 Hreusable).
Qed.

Theorem reusable_evidence_requires_target_in_certification_scope :
  forall reusable current,
    VerificationEvidenceReusable reusable current ->
    verificationReuseCertificationScope current
      (checkedVerificationTargetRevision
        (reusableVerificationCheckedEvidence reusable)).
Proof.
  intros reusable current Hreusable.
  unfold VerificationEvidenceReusable in Hreusable.
  exact (proj1 (proj2 Hreusable)).
Qed.

Theorem reusable_evidence_requires_exact_direct_dependencies :
  forall reusable current,
    VerificationEvidenceReusable reusable current ->
    VerificationRevisionSetEquivalent
      (reusableVerificationDependencies reusable)
      (verificationReuseDependencies current
        (checkedVerificationTargetRevision
          (reusableVerificationCheckedEvidence reusable))).
Proof.
  intros reusable current Hreusable.
  unfold VerificationEvidenceReusable in Hreusable.
  exact (proj1 (proj2 (proj2 Hreusable))).
Qed.

Theorem reusable_evidence_requires_exact_declared_validity_dimensions :
  forall reusable current,
    VerificationEvidenceReusable reusable current ->
    ScopeMatches
      (reusableVerificationValidityScope reusable)
      (verificationReuseValidityContext current).
Proof.
  intros reusable current Hreusable.
  unfold VerificationEvidenceReusable in Hreusable.
  exact (proj2 (proj2 (proj2 Hreusable))).
Qed.

Theorem missing_target_revision_invalidates_reuse :
  forall reusable current,
    ~ verificationReuseRevisions current
        (checkedVerificationTargetRevision
          (reusableVerificationCheckedEvidence reusable)) ->
    ~ VerificationEvidenceReusable reusable current.
Proof.
  intros reusable current Hmissing Hreusable.
  apply Hmissing.
  eapply reusable_evidence_requires_target_presence.
  exact Hreusable.
Qed.

Theorem target_outside_certification_scope_invalidates_reuse :
  forall reusable current,
    ~ verificationReuseCertificationScope current
        (checkedVerificationTargetRevision
          (reusableVerificationCheckedEvidence reusable)) ->
    ~ VerificationEvidenceReusable reusable current.
Proof.
  intros reusable current Houtside Hreusable.
  apply Houtside.
  eapply reusable_evidence_requires_target_in_certification_scope.
  exact Hreusable.
Qed.

Theorem changed_direct_dependency_set_invalidates_reuse :
  forall reusable current,
    ~ VerificationRevisionSetEquivalent
        (reusableVerificationDependencies reusable)
        (verificationReuseDependencies current
          (checkedVerificationTargetRevision
            (reusableVerificationCheckedEvidence reusable))) ->
    ~ VerificationEvidenceReusable reusable current.
Proof.
  intros reusable current Hchanged Hreusable.
  apply Hchanged.
  eapply reusable_evidence_requires_exact_direct_dependencies.
  exact Hreusable.
Qed.

Theorem changed_bound_validity_dimension_invalidates_reuse :
  forall reusable current dimension expected,
    reusableVerificationValidityScope reusable dimension = Some expected ->
    verificationReuseValidityContext current dimension <> Some expected ->
    ~ VerificationEvidenceReusable reusable current.
Proof.
  intros reusable current dimension expected Hbound Hchanged Hreusable.
  pose proof
    (reusable_evidence_requires_exact_declared_validity_dimensions
      reusable current Hreusable) as Hmatches.
  eapply changed_bound_dimension_cannot_match.
  - exact Hbound.
  - exact Hchanged.
  - exact Hmatches.
Qed.

Definition replaceVerificationReuseGraphRevision
  (context : VerificationReuseContext)
  (revision : VerificationGraphRevision) : VerificationReuseContext :=
  mkVerificationReuseContext
    revision
    (verificationReuseRevisions context)
    (verificationReuseCertificationScope context)
    (verificationReuseDependencies context)
    (verificationReuseValidityContext context).

Theorem whole_graph_revision_change_alone_does_not_invalidate_reuse :
  forall reusable current newGraphRevision,
    VerificationEvidenceReusable reusable current ->
    VerificationEvidenceReusable
      reusable
      (replaceVerificationReuseGraphRevision current newGraphRevision).
Proof.
  intros reusable current newGraphRevision Hreusable.
  unfold VerificationEvidenceReusable,
    replaceVerificationReuseGraphRevision in *.
  simpl in *.
  exact Hreusable.
Qed.

Definition ReuseRelevantInputsAgree
  (reusable : ReusableVerificationEvidence)
  (before after : VerificationReuseContext) : Prop :=
  let target :=
    checkedVerificationTargetRevision
      (reusableVerificationCheckedEvidence reusable) in
  (verificationReuseRevisions before target <->
    verificationReuseRevisions after target) /\
  (verificationReuseCertificationScope before target <->
    verificationReuseCertificationScope after target) /\
  VerificationRevisionSetEquivalent
    (verificationReuseDependencies before target)
    (verificationReuseDependencies after target) /\
  (forall dimension expected,
    reusableVerificationValidityScope reusable dimension = Some expected ->
    verificationReuseValidityContext before dimension =
      verificationReuseValidityContext after dimension).

Theorem unrelated_context_changes_preserve_reuse :
  forall reusable before after,
    VerificationEvidenceReusable reusable before ->
    ReuseRelevantInputsAgree reusable before after ->
    VerificationEvidenceReusable reusable after.
Proof.
  intros reusable before after Hreusable Hagree.
  unfold VerificationEvidenceReusable in Hreusable.
  unfold ReuseRelevantInputsAgree in Hagree.
  unfold VerificationEvidenceReusable.
  destruct Hreusable as
    [Htarget [Hscope [Hdependencies Hvalidity]]].
  destruct Hagree as
    [HtargetAgree [HscopeAgree [HdependencyAgree HvalidityAgree]]].
  split.
  - apply (proj1 HtargetAgree).
    exact Htarget.
  - split.
    + apply (proj1 HscopeAgree).
      exact Hscope.
    + split.
      * intros revision.
        split.
        -- intros Hcached.
           apply (proj1 (HdependencyAgree revision)).
           apply (proj1 (Hdependencies revision)).
           exact Hcached.
        -- intros Hafter.
           apply (proj2 (Hdependencies revision)).
           apply (proj2 (HdependencyAgree revision)).
           exact Hafter.
      * unfold ScopeMatches in *.
        intros dimension expected Hbound.
        rewrite <- (HvalidityAgree dimension expected Hbound).
        eapply Hvalidity.
        exact Hbound.
Qed.

Theorem extra_unbound_validity_dimensions_do_not_invalidate_reuse :
  forall reusable current extendedValidity changedDimension,
    VerificationEvidenceReusable reusable current ->
    reusableVerificationValidityScope reusable changedDimension = None ->
    ContextDiffersOnlyAt
      changedDimension
      (verificationReuseValidityContext current)
      extendedValidity ->
    VerificationEvidenceReusable
      reusable
      (mkVerificationReuseContext
        (verificationReuseGraphRevision current)
        (verificationReuseRevisions current)
        (verificationReuseCertificationScope current)
        (verificationReuseDependencies current)
        extendedValidity).
Proof.
  intros reusable current extendedValidity changedDimension
    Hreusable Hunbound Honly.
  unfold VerificationEvidenceReusable in *.
  simpl.
  destruct Hreusable as
    [Htarget [Hscope [Hdependencies Hvalidity]]].
  split; [exact Htarget |].
  split; [exact Hscope |].
  split; [exact Hdependencies |].
  eapply unbound_dimension_change_preserves_match.
  - exact Hvalidity.
  - exact Hunbound.
  - exact Honly.
Qed.

Theorem reusable_verification_evidence_composes_with_generic_body_assurance :
  forall reusable current policy body currentRequirements currentRequirementRevisions
    lineage assurance,
    VerificationEvidenceReusable reusable current ->
    CheckedGenericApplicationAssurance
      policy body currentRequirements currentRequirementRevisions lineage assurance ->
    VerificationEvidenceReusable reusable current /\
    genericApplicationAssuranceBody assurance = body.
Proof.
  intros reusable current policy body currentRequirements currentRequirementRevisions
    lineage assurance Hreusable Hgeneric.
  split.
  - exact Hreusable.
  - eapply checked_generic_application_retains_exact_reusable_body.
    exact Hgeneric.
Qed.
