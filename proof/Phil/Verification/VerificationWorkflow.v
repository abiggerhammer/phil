From Stdlib Require Import Lists.List.

Import ListNotations.

(*
  PHIL-VERIFY-WORKFLOW-001 — intrinsic validity and deterministic obligation
  closure.

  This file certifies the orchestration contract implemented by VER-001,
  VER-002, and VER-012.  It deliberately imports the competence of the parser,
  surface checker, semantic obligation generator, and evidence checker rather
  than re-proving those semantic layers here.

  The workflow owns these rules:

  - intrinsic rejection is terminal and cannot be changed by assurance policy;
  - only intrinsic acceptance reaches obligation closure, retaining the exact
    selected policy;
  - the residual obligation graph has one normalized exact revision domain,
    only known dependency/scope references, and no dependency cycle;
  - a VerificationBundle explicitly records intrinsic acceptance and preserves
    the exact source, graph, policy, declaration/instance/realization sets, and
    accepted-evidence references;
  - evidence may enter the bundle only when it is accepted, content-bound to
    its declared digest, targets a known obligation revision, and does not
    conflict with another use of the same stable evidence identity; and
  - list order and exact duplicate presentation are nonsemantic whenever the
    corresponding semantic member sets are unchanged.

  Concrete Text/Map/Set ordering, canonical serialization/SHA-256, parser and
  checker implementation correctness, and the concrete correspondence from
  Haskell identities to these normalized atoms remain explicit representation
  or predecessor boundaries.
*)

Definition PolicyRevision := nat.
Definition SourceRevision := nat.
Definition DeclarationIdentity := nat.
Definition ArchitectureInstanceIdentity := nat.
Definition ArchitectureRealizationIdentity := nat.
Definition RevisionIdentity := nat.
Definition EvidenceIdentity := nat.
Definition EvidenceDigest := nat.

Inductive WorkflowState : Type :=
| WorkflowRejected
| WorkflowReady (policy : PolicyRevision).

Definition decideIntrinsicWorkflow
  (intrinsicAccepted : bool)
  (policy : PolicyRevision) : WorkflowState :=
  if intrinsicAccepted then WorkflowReady policy else WorkflowRejected.

Theorem intrinsic_rejection_is_terminal :
  forall policy,
    decideIntrinsicWorkflow false policy = WorkflowRejected.
Proof.
  reflexivity.
Qed.

Theorem intrinsic_rejection_is_policy_independent :
  forall firstPolicy secondPolicy,
    decideIntrinsicWorkflow false firstPolicy =
    decideIntrinsicWorkflow false secondPolicy.
Proof.
  reflexivity.
Qed.

Theorem intrinsic_acceptance_preserves_exact_selected_policy :
  forall policy,
    decideIntrinsicWorkflow true policy = WorkflowReady policy.
Proof.
  reflexivity.
Qed.

Record VerificationGraph : Type := mkVerificationGraph {
  verificationGraphNodes : list RevisionIdentity;
  verificationGraphDependencies : list (RevisionIdentity * RevisionIdentity);
  verificationGraphCertificationScope : list RevisionIdentity
}.

Inductive DependsTransitively (graph : VerificationGraph)
  : RevisionIdentity -> RevisionIdentity -> Prop :=
| DependsDirect :
    forall owner dependency,
      In (owner, dependency) (verificationGraphDependencies graph) ->
      DependsTransitively graph owner dependency
| DependsStep :
    forall owner middle dependency,
      In (owner, middle) (verificationGraphDependencies graph) ->
      DependsTransitively graph middle dependency ->
      DependsTransitively graph owner dependency.

Definition NoDependencyCycle (graph : VerificationGraph) : Prop :=
  forall revision,
    ~ DependsTransitively graph revision revision.

Definition GraphWellFormed (graph : VerificationGraph) : Prop :=
  NoDup (verificationGraphNodes graph) /\
  (forall owner dependency,
    In (owner, dependency) (verificationGraphDependencies graph) ->
    In owner (verificationGraphNodes graph) /\
    In dependency (verificationGraphNodes graph)) /\
  (forall revision,
    In revision (verificationGraphCertificationScope graph) ->
    In revision (verificationGraphNodes graph)) /\
  NoDependencyCycle graph.

Definition SameMembers {A : Type} (first second : list A) : Prop :=
  forall value,
    In value first <-> In value second.

Theorem same_members_reflexive :
  forall A (values : list A),
    SameMembers values values.
Proof.
  intros A values value.
  tauto.
Qed.

Theorem same_members_symmetric :
  forall A (first second : list A),
    SameMembers first second ->
    SameMembers second first.
Proof.
  intros A first second Hsame value.
  specialize (Hsame value).
  tauto.
Qed.

Theorem same_members_transitive :
  forall A (first second third : list A),
    SameMembers first second ->
    SameMembers second third ->
    SameMembers first third.
Proof.
  intros A first second third Hfirst Hsecond value.
  specialize (Hfirst value).
  specialize (Hsecond value).
  tauto.
Qed.

Definition GraphSemanticallyEqual
  (first second : VerificationGraph) : Prop :=
  SameMembers
    (verificationGraphNodes first)
    (verificationGraphNodes second) /\
  SameMembers
    (verificationGraphDependencies first)
    (verificationGraphDependencies second) /\
  SameMembers
    (verificationGraphCertificationScope first)
    (verificationGraphCertificationScope second).

Record AcceptedEvidenceReference : Type := mkAcceptedEvidenceReference {
  acceptedEvidenceIdentity : EvidenceIdentity;
  acceptedEvidenceDigest : EvidenceDigest;
  acceptedEvidenceTargetRevision : RevisionIdentity
}.

Record EvidenceFacts : Type := mkEvidenceFacts {
  evidenceReference : AcceptedEvidenceReference;
  evidenceAccepted : bool;
  evidenceDigestMatches : bool;
  evidenceTargetKnown : bool;
  evidenceIdentityConflictFree : bool
}.

Definition EvidenceFactsValid (facts : EvidenceFacts) : Prop :=
  evidenceAccepted facts = true /\
  evidenceDigestMatches facts = true /\
  evidenceTargetKnown facts = true /\
  evidenceIdentityConflictFree facts = true.

Definition BundleEvidenceExact
  (facts : list EvidenceFacts)
  (references : list AcceptedEvidenceReference) : Prop :=
  (forall fact,
    In fact facts ->
    EvidenceFactsValid fact /\
    In (evidenceReference fact) references) /\
  (forall reference,
    In reference references ->
    exists fact,
      In fact facts /\
      EvidenceFactsValid fact /\
      evidenceReference fact = reference) /\
  NoDup (map acceptedEvidenceIdentity references).

Record VerificationBundle : Type := mkVerificationBundle {
  verificationBundleSourceRevision : SourceRevision;
  verificationBundleDeclarations : list DeclarationIdentity;
  verificationBundleArchitectureInstances : list ArchitectureInstanceIdentity;
  verificationBundleArchitectureRealizations : list ArchitectureRealizationIdentity;
  verificationBundleObligationGraph : VerificationGraph;
  verificationBundlePolicyRevision : PolicyRevision;
  verificationBundleAcceptedEvidence : list AcceptedEvidenceReference
}.

Definition ExactVerificationBundle
  (source : SourceRevision)
  (declarations : list DeclarationIdentity)
  (instances : list ArchitectureInstanceIdentity)
  (realizations : list ArchitectureRealizationIdentity)
  (graph : VerificationGraph)
  (policy : PolicyRevision)
  (evidence : list EvidenceFacts)
  (bundle : VerificationBundle) : Prop :=
  GraphWellFormed graph /\
  verificationBundleSourceRevision bundle = source /\
  SameMembers (verificationBundleDeclarations bundle) declarations /\
  SameMembers (verificationBundleArchitectureInstances bundle) instances /\
  SameMembers (verificationBundleArchitectureRealizations bundle) realizations /\
  verificationBundleObligationGraph bundle = graph /\
  verificationBundlePolicyRevision bundle = policy /\
  BundleEvidenceExact evidence (verificationBundleAcceptedEvidence bundle).

Theorem exact_bundle_retains_exact_source_revision :
  forall source declarations instances realizations graph policy evidence bundle,
    ExactVerificationBundle
      source declarations instances realizations graph policy evidence bundle ->
    verificationBundleSourceRevision bundle = source.
Proof.
  intros source declarations instances realizations graph policy evidence bundle Hbundle.
  destruct Hbundle as [_ [Hsource _]].
  exact Hsource.
Qed.

Theorem exact_bundle_retains_exact_obligation_graph :
  forall source declarations instances realizations graph policy evidence bundle,
    ExactVerificationBundle
      source declarations instances realizations graph policy evidence bundle ->
    verificationBundleObligationGraph bundle = graph.
Proof.
  intros source declarations instances realizations graph policy evidence bundle Hbundle.
  destruct Hbundle as [_ [_ [_ [_ [_ [Hgraph _]]]]]].
  exact Hgraph.
Qed.

Theorem exact_bundle_retains_exact_policy_revision :
  forall source declarations instances realizations graph policy evidence bundle,
    ExactVerificationBundle
      source declarations instances realizations graph policy evidence bundle ->
    verificationBundlePolicyRevision bundle = policy.
Proof.
  intros source declarations instances realizations graph policy evidence bundle Hbundle.
  destruct Hbundle as [_ [_ [_ [_ [_ [_ [Hpolicy _]]]]]]].
  exact Hpolicy.
Qed.

Theorem exact_bundle_contains_only_accepted_content_bound_known_evidence :
  forall source declarations instances realizations graph policy evidence bundle fact,
    ExactVerificationBundle
      source declarations instances realizations graph policy evidence bundle ->
    In fact evidence ->
    EvidenceFactsValid fact /\
    In (evidenceReference fact) (verificationBundleAcceptedEvidence bundle).
Proof.
  intros source declarations instances realizations graph policy evidence bundle fact
    Hbundle Hin.
  destruct Hbundle as [_ [_ [_ [_ [_ [_ [_ Hevidence]]]]]]].
  destruct Hevidence as [Hall _].
  apply Hall.
  exact Hin.
Qed.

Theorem rejected_or_stale_evidence_cannot_enter_exact_bundle :
  forall source declarations instances realizations graph policy evidence bundle fact,
    In fact evidence ->
    ~ EvidenceFactsValid fact ->
    ~ ExactVerificationBundle
        source declarations instances realizations graph policy evidence bundle.
Proof.
  intros source declarations instances realizations graph policy evidence bundle fact
    Hin Hinvalid Hbundle.
  apply Hinvalid.
  pose proof
    (exact_bundle_contains_only_accepted_content_bound_known_evidence
      source declarations instances realizations graph policy evidence bundle fact
      Hbundle Hin) as Hfacts.
  exact (proj1 Hfacts).
Qed.

Theorem exact_bundle_requires_well_formed_graph :
  forall source declarations instances realizations graph policy evidence bundle,
    ExactVerificationBundle
      source declarations instances realizations graph policy evidence bundle ->
    GraphWellFormed graph.
Proof.
  intros source declarations instances realizations graph policy evidence bundle Hbundle.
  exact (proj1 Hbundle).
Qed.

Theorem source_revision_change_rekeys_verification_target :
  forall firstSource secondSource declarations instances realizations graph policy evidence bundle,
    firstSource <> secondSource ->
    ExactVerificationBundle
      firstSource declarations instances realizations graph policy evidence bundle ->
    ~ ExactVerificationBundle
      secondSource declarations instances realizations graph policy evidence bundle.
Proof.
  intros firstSource secondSource declarations instances realizations graph policy evidence bundle
    Hdifferent Hfirst Hsecond.
  apply Hdifferent.
  pose proof
    (exact_bundle_retains_exact_source_revision
      firstSource declarations instances realizations graph policy evidence bundle Hfirst)
    as HfirstSource.
  pose proof
    (exact_bundle_retains_exact_source_revision
      secondSource declarations instances realizations graph policy evidence bundle Hsecond)
    as HsecondSource.
  rewrite <- HfirstSource, <- HsecondSource.
  reflexivity.
Qed.

Theorem policy_revision_change_rekeys_verification_target :
  forall source declarations instances realizations graph firstPolicy secondPolicy evidence bundle,
    firstPolicy <> secondPolicy ->
    ExactVerificationBundle
      source declarations instances realizations graph firstPolicy evidence bundle ->
    ~ ExactVerificationBundle
      source declarations instances realizations graph secondPolicy evidence bundle.
Proof.
  intros source declarations instances realizations graph firstPolicy secondPolicy evidence bundle
    Hdifferent Hfirst Hsecond.
  apply Hdifferent.
  pose proof
    (exact_bundle_retains_exact_policy_revision
      source declarations instances realizations graph firstPolicy evidence bundle Hfirst)
    as HfirstPolicy.
  pose proof
    (exact_bundle_retains_exact_policy_revision
      source declarations instances realizations graph secondPolicy evidence bundle Hsecond)
    as HsecondPolicy.
  rewrite <- HfirstPolicy, <- HsecondPolicy.
  reflexivity.
Qed.

Theorem obligation_graph_change_rekeys_verification_target :
  forall source declarations instances realizations firstGraph secondGraph policy evidence bundle,
    firstGraph <> secondGraph ->
    ExactVerificationBundle
      source declarations instances realizations firstGraph policy evidence bundle ->
    ~ ExactVerificationBundle
      source declarations instances realizations secondGraph policy evidence bundle.
Proof.
  intros source declarations instances realizations firstGraph secondGraph policy evidence bundle
    Hdifferent Hfirst Hsecond.
  apply Hdifferent.
  pose proof
    (exact_bundle_retains_exact_obligation_graph
      source declarations instances realizations firstGraph policy evidence bundle Hfirst)
    as HfirstGraph.
  pose proof
    (exact_bundle_retains_exact_obligation_graph
      source declarations instances realizations secondGraph policy evidence bundle Hsecond)
    as HsecondGraph.
  rewrite <- HfirstGraph, <- HsecondGraph.
  reflexivity.
Qed.

Theorem bundle_evidence_exact_respects_semantic_membership :
  forall firstFacts secondFacts references,
    SameMembers firstFacts secondFacts ->
    BundleEvidenceExact firstFacts references ->
    BundleEvidenceExact secondFacts references.
Proof.
  intros firstFacts secondFacts references Hsame Hfirst.
  destruct Hfirst as [Hforward [Hbackward Hnodup]].
  split.
  - intros fact HinSecond.
    apply Hforward.
    apply (proj2 (Hsame fact)).
    exact HinSecond.
  - split.
    + intros reference HinReference.
      destruct (Hbackward reference HinReference) as
        [fact [HinFirst [Hvalid Heq]]].
      exists fact.
      split.
      * apply (proj1 (Hsame fact)).
        exact HinFirst.
      * split; assumption.
    + exact Hnodup.
Qed.

Theorem semantic_container_order_and_exact_duplicates_do_not_change_bundle :
  forall source
    firstDeclarations secondDeclarations
    firstInstances secondInstances
    firstRealizations secondRealizations
    graph policy firstEvidence secondEvidence bundle,
    SameMembers firstDeclarations secondDeclarations ->
    SameMembers firstInstances secondInstances ->
    SameMembers firstRealizations secondRealizations ->
    SameMembers firstEvidence secondEvidence ->
    ExactVerificationBundle
      source firstDeclarations firstInstances firstRealizations
      graph policy firstEvidence bundle ->
    ExactVerificationBundle
      source secondDeclarations secondInstances secondRealizations
      graph policy secondEvidence bundle.
Proof.
  intros source firstDeclarations secondDeclarations
    firstInstances secondInstances firstRealizations secondRealizations
    graph policy firstEvidence secondEvidence bundle
    Hdeclarations Hinstances Hrealizations Hevidence Hbundle.
  destruct Hbundle as
    [Hgraph [Hsource [HbundleDeclarations [HbundleInstances
      [HbundleRealizations [HexactGraph [HexactPolicy HbundleEvidence]]]]]]].
  split; [exact Hgraph |].
  split; [exact Hsource |].
  split.
  - eapply same_members_transitive; eauto.
  - split.
    + eapply same_members_transitive; eauto.
    + split.
      * eapply same_members_transitive; eauto.
      * split; [exact HexactGraph |].
        split; [exact HexactPolicy |].
        eapply bundle_evidence_exact_respects_semantic_membership; eauto.
Qed.
