From Stdlib Require Import Bool.Bool Lists.List Arith.PeanoNat.

Import ListNotations.

From Phil.Verification Require Import ManifestClosure.

Inductive ManifestClosureDecision : Type :=
| ManifestClosureAccepted
| ManifestClosureRejected.

Definition manifestClosureFactsb
  (intrinsicAccepted policyExact architectureExact obligationDomainExact
   revisionBodiesExact acceptedEvidenceRefsExact selectedEvidenceCurrent
   selectedEvidenceAccepted selectedEvidenceValidityExact
   assumptionDependenciesExplicit noUnusedAssumptions
   exportsExplicit exportsPermitted exportsValidityExact
   usesExplicit manifestVerifierAccepted : bool) : bool :=
  intrinsicAccepted &&
  policyExact &&
  architectureExact &&
  obligationDomainExact &&
  revisionBodiesExact &&
  acceptedEvidenceRefsExact &&
  selectedEvidenceCurrent &&
  selectedEvidenceAccepted &&
  selectedEvidenceValidityExact &&
  assumptionDependenciesExplicit &&
  noUnusedAssumptions &&
  exportsExplicit &&
  exportsPermitted &&
  exportsValidityExact &&
  usesExplicit &&
  manifestVerifierAccepted.

Definition decideManifestClosure
  (intrinsicAccepted policyExact architectureExact obligationDomainExact
   revisionBodiesExact acceptedEvidenceRefsExact selectedEvidenceCurrent
   selectedEvidenceAccepted selectedEvidenceValidityExact
   assumptionDependenciesExplicit noUnusedAssumptions
   exportsExplicit exportsPermitted exportsValidityExact
   usesExplicit manifestVerifierAccepted : bool) : ManifestClosureDecision :=
  if manifestClosureFactsb
      intrinsicAccepted policyExact architectureExact obligationDomainExact
      revisionBodiesExact acceptedEvidenceRefsExact selectedEvidenceCurrent
      selectedEvidenceAccepted selectedEvidenceValidityExact
      assumptionDependenciesExplicit noUnusedAssumptions
      exportsExplicit exportsPermitted exportsValidityExact
      usesExplicit manifestVerifierAccepted
  then ManifestClosureAccepted
  else ManifestClosureRejected.

Theorem exact_manifest_closure_accepts :
  decideManifestClosure
    true true true true true true true true
    true true true true true true true true =
  ManifestClosureAccepted.
Proof. reflexivity. Qed.

Theorem intrinsic_rejection_cannot_be_closed :
  decideManifestClosure
    false true true true true true true true
    true true true true true true true true =
  ManifestClosureRejected.
Proof. reflexivity. Qed.

Theorem policy_or_architecture_substitution_rejects :
  decideManifestClosure
    true false true true true true true true
    true true true true true true true true =
      ManifestClosureRejected /\
  decideManifestClosure
    true true false true true true true true
    true true true true true true true true =
      ManifestClosureRejected.
Proof. split; reflexivity. Qed.

Theorem obligation_or_revision_substitution_rejects :
  decideManifestClosure
    true true true false true true true true
    true true true true true true true true =
      ManifestClosureRejected /\
  decideManifestClosure
    true true true true false true true true
    true true true true true true true true =
      ManifestClosureRejected.
Proof. split; reflexivity. Qed.

Theorem stale_or_foreign_evidence_rejects :
  decideManifestClosure
    true true true true true false true true
    true true true true true true true true =
      ManifestClosureRejected /\
  decideManifestClosure
    true true true true true true false true
    true true true true true true true true =
      ManifestClosureRejected /\
  decideManifestClosure
    true true true true true true true false
    true true true true true true true true =
      ManifestClosureRejected.
Proof. repeat split; reflexivity. Qed.

Theorem evidence_validity_mismatch_rejects :
  decideManifestClosure
    true true true true true true true true
    false true true true true true true true =
  ManifestClosureRejected.
Proof. reflexivity. Qed.

Theorem hidden_or_unused_assumption_rejects :
  decideManifestClosure
    true true true true true true true true
    true false true true true true true true =
      ManifestClosureRejected /\
  decideManifestClosure
    true true true true true true true true
    true true false true true true true true =
      ManifestClosureRejected.
Proof. split; reflexivity. Qed.

Theorem invalid_export_rejects :
  decideManifestClosure
    true true true true true true true true
    true true true false true true true true =
      ManifestClosureRejected /\
  decideManifestClosure
    true true true true true true true true
    true true true true false true true true =
      ManifestClosureRejected /\
  decideManifestClosure
    true true true true true true true true
    true true true true true false true true =
      ManifestClosureRejected.
Proof. repeat split; reflexivity. Qed.

Theorem missing_use_or_manifest_verifier_rejection_rejects :
  decideManifestClosure
    true true true true true true true true
    true true true true true true false true =
      ManifestClosureRejected /\
  decideManifestClosure
    true true true true true true true true
    true true true true true true true false =
      ManifestClosureRejected.
Proof. split; reflexivity. Qed.


(*
  PHIL-AUD-MANIFEST-EVIDENCE-MEMBERSHIP-001 — selected-evidence
  membership correspondence.

  Production closeVerificationBundle enumerates the exact selected evidence
  keys and checks each one for membership in the current bundle's accepted
  evidence map.  The bundle-reference traversal separately checks the concrete
  reference ID, digest, target revision, and accepted ledger record.

  This layer closes the previously missing direction of quantification:
  every selected key must be a current-bundle key.  It deliberately does not
  require every bundle key to be selected, so a valid selected subset of a
  larger exact bundle remains admissible.
*)

Definition p1EnvironmentEvidenceSelected
  (environment : P1ManifestEnvironment)
  (evidence : P1EvidenceKey) : bool :=
  match p1ManifestEvidence environment evidence with
  | Some facts => p1EvidenceSelected facts
  | None => false
  end.

Definition selectedEvidenceMembershipFactsb
  (bundleContains : P1EvidenceKey -> bool)
  (selectedEvidence : list P1EvidenceKey) : bool :=
  forallb bundleContains selectedEvidence.

Record ManifestEvidenceMembershipReflection
  (bundle : P1BundleFacts)
  (environment : P1ManifestEnvironment)
  (selectedEvidence : list P1EvidenceKey)
  (bundleContains : P1EvidenceKey -> bool) : Prop :=
  mkManifestEvidenceMembershipReflection {
    manifestEvidenceSelectedEnumerationComplete :
      forall evidence,
        p1EnvironmentEvidenceSelected environment evidence = true <->
        In evidence selectedEvidence;
    manifestEvidenceBundleMembershipReflects :
      forall evidence,
        bundleContains evidence = true <->
        p1BundleAcceptedEvidence bundle evidence = true
  }.

Theorem selected_evidence_membership_factsb_true_iff_semantic_subset :
  forall bundle environment selectedEvidence bundleContains,
    ManifestEvidenceMembershipReflection
      bundle environment selectedEvidence bundleContains ->
    (selectedEvidenceMembershipFactsb bundleContains selectedEvidence = true <->
      forall evidence,
        p1EnvironmentEvidenceSelected environment evidence = true ->
        p1BundleAcceptedEvidence bundle evidence = true).
Proof.
  intros bundle environment selectedEvidence bundleContains Hreflection.
  destruct Hreflection as [Hselected Hbundle].
  split.
  - intros Hfacts evidence HselectedEvidence.
    unfold selectedEvidenceMembershipFactsb in Hfacts.
    pose proof
      (proj1
        (@forallb_forall
          P1EvidenceKey bundleContains selectedEvidence)
        Hfacts)
      as Hall.
    apply (proj1 (Hbundle evidence)).
    apply Hall.
    apply (proj1 (Hselected evidence)).
    exact HselectedEvidence.
  - intros Hsubset.
    unfold selectedEvidenceMembershipFactsb.
    apply forallb_forall.
    intros evidence Hin.
    apply (proj2 (Hbundle evidence)).
    apply Hsubset.
    apply (proj2 (Hselected evidence)).
    exact Hin.
Qed.

Definition P1EvidenceValidExceptBundleMembership
  (manifest : P1ManifestFacts)
  (environment : P1ManifestEnvironment)
  (revision : nat)
  (evidence : P1EvidenceKey)
  (runtimeRequired : bool) : Prop :=
  exists facts,
    p1ManifestEvidence environment evidence = Some facts /\
    p1EvidenceCurrentLedger facts = true /\
    p1EvidenceSelected facts = true /\
    p1EvidenceAccepted facts = true /\
    p1EvidenceTargetRevision facts = revision /\
    p1EvidenceRuntimeEnforced facts = runtimeRequired /\
    ScopeMatches
      (p1EvidenceScope facts)
      (p1ManifestEffectiveValidity manifest).

Theorem checked_selected_membership_completes_evidence_validity :
  forall bundle manifest environment selectedEvidence bundleContains
         revision evidence runtimeRequired,
    ManifestEvidenceMembershipReflection
      bundle environment selectedEvidence bundleContains ->
    selectedEvidenceMembershipFactsb bundleContains selectedEvidence = true ->
    P1EvidenceValidExceptBundleMembership
      manifest environment revision evidence runtimeRequired ->
    P1EvidenceValidFor
      bundle manifest environment revision evidence runtimeRequired.
Proof.
  intros bundle manifest environment selectedEvidence bundleContains
    revision evidence runtimeRequired
    Hreflection Hmembership Hpartial.
  unfold P1EvidenceValidExceptBundleMembership in Hpartial.
  destruct Hpartial as
    [facts
      [Hlookup
        [Hledger
          [Hselected
            [Haccepted
              [Hrevision
                [Hruntime Hscope]]]]]]].
  assert
    (Hselection :
      p1EnvironmentEvidenceSelected environment evidence = true).
  {
    unfold p1EnvironmentEvidenceSelected.
    rewrite Hlookup.
    exact Hselected.
  }
  pose proof
    (proj1
      (selected_evidence_membership_factsb_true_iff_semantic_subset
        bundle environment selectedEvidence bundleContains Hreflection)
      Hmembership evidence Hselection)
    as Hbundle.
  unfold P1EvidenceValidFor.
  exists facts.
  repeat split; assumption.
Qed.

Theorem checked_selected_membership_completes_static_disposition :
  forall bundle manifest environment selectedEvidence bundleContains
         revision evidence,
    ManifestEvidenceMembershipReflection
      bundle environment selectedEvidence bundleContains ->
    selectedEvidenceMembershipFactsb bundleContains selectedEvidence = true ->
    P1EvidenceValidExceptBundleMembership
      manifest environment revision evidence false ->
    P1DispositionValid
      bundle manifest environment revision
      (P1EvidenceDisposition evidence).
Proof.
  intros.
  unfold P1DispositionValid.
  eapply checked_selected_membership_completes_evidence_validity; eauto.
Qed.

Theorem checked_selected_membership_completes_runtime_disposition :
  forall bundle manifest environment selectedEvidence bundleContains
         revision evidence,
    ManifestEvidenceMembershipReflection
      bundle environment selectedEvidence bundleContains ->
    selectedEvidenceMembershipFactsb bundleContains selectedEvidence = true ->
    P1EvidenceValidExceptBundleMembership
      manifest environment revision evidence true ->
    P1DispositionValid
      bundle manifest environment revision
      (P1RuntimeDisposition evidence).
Proof.
  intros.
  unfold P1DispositionValid.
  eapply checked_selected_membership_completes_evidence_validity; eauto.
Qed.

Theorem missing_selected_bundle_member_rejects_membership_check :
  forall bundle environment selectedEvidence bundleContains evidence,
    ManifestEvidenceMembershipReflection
      bundle environment selectedEvidence bundleContains ->
    p1EnvironmentEvidenceSelected environment evidence = true ->
    p1BundleAcceptedEvidence bundle evidence = false ->
    selectedEvidenceMembershipFactsb bundleContains selectedEvidence = false.
Proof.
  intros bundle environment selectedEvidence bundleContains evidence
    Hreflection Hselected Habsent.
  destruct
    (selectedEvidenceMembershipFactsb bundleContains selectedEvidence)
    eqn:Hmembership.
  - pose proof
      (proj1
        (selected_evidence_membership_factsb_true_iff_semantic_subset
          bundle environment selectedEvidence bundleContains Hreflection)
        Hmembership evidence Hselected)
      as Hpresent.
    rewrite Habsent in Hpresent.
    discriminate.
  - reflexivity.
Qed.

Theorem empty_bundle_rejects_nonempty_selected_evidence :
  selectedEvidenceMembershipFactsb (fun _ => false) [0] = false.
Proof.
  reflexivity.
Qed.

Theorem distinct_bundle_evidence_cannot_authorize_selected_evidence :
  selectedEvidenceMembershipFactsb
    (fun evidence => Nat.eqb evidence 0)
    [1] = false.
Proof.
  reflexivity.
Qed.

Theorem selected_subset_of_larger_bundle_is_allowed :
  selectedEvidenceMembershipFactsb
    (fun evidence =>
      orb (Nat.eqb evidence 0) (Nat.eqb evidence 1))
    [0] = true.
Proof.
  reflexivity.
Qed.

Theorem alternate_selected_subset_of_larger_bundle_is_allowed :
  selectedEvidenceMembershipFactsb
    (fun evidence =>
      orb (Nat.eqb evidence 0) (Nat.eqb evidence 1))
    [1] = true.
Proof.
  reflexivity.
Qed.

Theorem empty_selection_requires_no_bundle_membership :
  forall bundleContains,
    selectedEvidenceMembershipFactsb bundleContains [] = true.
Proof.
  reflexivity.
Qed.
