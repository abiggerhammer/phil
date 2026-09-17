From Stdlib Require Import Bool.Bool Lists.List.

Import ListNotations.

From Phil.Assurance Require Import
  ValidityScopeImplementation
  VerificationReuse.

(*
  PHIL-VERIFY-REUSE-001 — executable correspondence for VER-006 reuse.

  Production evaluateReusableProofEvidence obtains three primitive graph facts:

    target revision present;
    target revision still in certification scope;
    direct dependency-revision set extensionally unchanged.

  It then checks every entry bound by the cached ValidityScope.  This file
  proves that the finite conjunction of those reflected native facts accepts
  exactly the semantic VerificationEvidenceReusable relation.

  Concrete Digest/RevisionId/Text/Map/Set equality, enumeration order, and the
  construction of detailed EvidenceReuseStaleness diagnostics remain native
  representation/diagnostic boundaries.  They cannot turn a rejected kernel
  fact conjunction into semantic reuse.
*)

Definition verificationReuseFactsb
  (targetPresent targetInScope dependenciesExact : bool)
  (validityFacts : list bool) : bool :=
  andb targetPresent
    (andb targetInScope
      (andb dependenciesExact (validityScopeFactsb validityFacts))).

Inductive VerificationReuseDecision : Type :=
| VerificationReuseAccepted
| VerificationReuseRejected.

Definition decideVerificationReuse
  (targetPresent targetInScope dependenciesExact : bool)
  (validityFacts : list bool) : VerificationReuseDecision :=
  if verificationReuseFactsb
      targetPresent targetInScope dependenciesExact validityFacts
  then VerificationReuseAccepted
  else VerificationReuseRejected.

Record VerificationReuseFactReflection
  (reusable : ReusableVerificationEvidence)
  (current : VerificationReuseContext)
  (entries : list ScopeEntry)
  (validityFacts : list bool)
  (targetPresent targetInScope dependenciesExact : bool) : Prop :=
  mkVerificationReuseFactReflection {
    verificationReuseTargetPresentReflects :
      targetPresent = true <->
      verificationReuseRevisions current
        (checkedVerificationTargetRevision
          (reusableVerificationCheckedEvidence reusable));
    verificationReuseTargetScopeReflects :
      targetInScope = true <->
      verificationReuseCertificationScope current
        (checkedVerificationTargetRevision
          (reusableVerificationCheckedEvidence reusable));
    verificationReuseDependenciesReflect :
      dependenciesExact = true <->
      VerificationRevisionSetEquivalent
        (reusableVerificationDependencies reusable)
        (verificationReuseDependencies current
          (checkedVerificationTargetRevision
            (reusableVerificationCheckedEvidence reusable)));
    verificationReuseScopeEntriesComplete :
      ScopeEntriesComplete
        (reusableVerificationValidityScope reusable)
        entries;
    verificationReuseValidityFactsReflect :
      ScopeFactReflection
        (verificationReuseValidityContext current)
        entries
        validityFacts
  }.

Theorem verification_reuse_factsb_true_iff_semantic_reuse :
  forall reusable current entries validityFacts
    targetPresent targetInScope dependenciesExact,
    VerificationReuseFactReflection
      reusable current entries validityFacts
      targetPresent targetInScope dependenciesExact ->
    (verificationReuseFactsb
      targetPresent targetInScope dependenciesExact validityFacts = true <->
      VerificationEvidenceReusable reusable current).
Proof.
  intros reusable current entries validityFacts
    targetPresent targetInScope dependenciesExact Hreflection.
  destruct Hreflection as
    [Htarget Hscope Hdependencies Hcomplete Hvalidity].
  split.
  - intros Hfacts.
    unfold verificationReuseFactsb in Hfacts.
    apply andb_true_iff in Hfacts.
    destruct Hfacts as [HtargetFact Hrest].
    apply andb_true_iff in Hrest.
    destruct Hrest as [HscopeFact Hrest].
    apply andb_true_iff in Hrest.
    destruct Hrest as [HdependencyFact HvalidityFacts].
    unfold VerificationEvidenceReusable.
    split.
    + apply (proj1 Htarget).
      exact HtargetFact.
    + split.
      * apply (proj1 Hscope).
        exact HscopeFact.
      * split.
        -- apply (proj1 Hdependencies).
           exact HdependencyFact.
        -- apply (proj1
             (validity_scope_factsb_true_iff_scope_matches
               (reusableVerificationValidityScope reusable)
               (verificationReuseValidityContext current)
               entries validityFacts Hcomplete Hvalidity)).
           exact HvalidityFacts.
  - intros Hreusable.
    unfold VerificationEvidenceReusable in Hreusable.
    destruct Hreusable as
      [HtargetCurrent [HscopeCurrent [HdependenciesCurrent HvalidityCurrent]]].
    unfold verificationReuseFactsb.
    apply andb_true_iff.
    split.
    + apply (proj2 Htarget).
      exact HtargetCurrent.
    + apply andb_true_iff.
      split.
      * apply (proj2 Hscope).
        exact HscopeCurrent.
      * apply andb_true_iff.
        split.
        -- apply (proj2 Hdependencies).
           exact HdependenciesCurrent.
        -- apply (proj2
             (validity_scope_factsb_true_iff_scope_matches
               (reusableVerificationValidityScope reusable)
               (verificationReuseValidityContext current)
               entries validityFacts Hcomplete Hvalidity)).
           exact HvalidityCurrent.
Qed.

Theorem verification_reuse_decision_accept_iff_facts_true :
  forall targetPresent targetInScope dependenciesExact validityFacts,
    decideVerificationReuse
      targetPresent targetInScope dependenciesExact validityFacts =
      VerificationReuseAccepted <->
    verificationReuseFactsb
      targetPresent targetInScope dependenciesExact validityFacts = true.
Proof.
  intros targetPresent targetInScope dependenciesExact validityFacts.
  unfold decideVerificationReuse.
  destruct
    (verificationReuseFactsb
      targetPresent targetInScope dependenciesExact validityFacts)
    eqn:Hfacts; cbn;
    split; intro H; try reflexivity; try discriminate.
Qed.

Theorem verification_reuse_decision_accept_iff_semantic_reuse :
  forall reusable current entries validityFacts
    targetPresent targetInScope dependenciesExact,
    VerificationReuseFactReflection
      reusable current entries validityFacts
      targetPresent targetInScope dependenciesExact ->
    (decideVerificationReuse
      targetPresent targetInScope dependenciesExact validityFacts =
      VerificationReuseAccepted <->
      VerificationEvidenceReusable reusable current).
Proof.
  intros reusable current entries validityFacts
    targetPresent targetInScope dependenciesExact Hreflection.
  split.
  - intros Hdecision.
    apply (proj1
      (verification_reuse_factsb_true_iff_semantic_reuse
        reusable current entries validityFacts
        targetPresent targetInScope dependenciesExact Hreflection)).
    apply (proj1
      (verification_reuse_decision_accept_iff_facts_true
        targetPresent targetInScope dependenciesExact validityFacts)).
    exact Hdecision.
  - intros Hreusable.
    apply (proj2
      (verification_reuse_decision_accept_iff_facts_true
        targetPresent targetInScope dependenciesExact validityFacts)).
    apply (proj2
      (verification_reuse_factsb_true_iff_semantic_reuse
        reusable current entries validityFacts
        targetPresent targetInScope dependenciesExact Hreflection)).
    exact Hreusable.
Qed.

Theorem missing_target_fact_rejects_reuse :
  forall targetInScope dependenciesExact validityFacts,
    decideVerificationReuse
      false targetInScope dependenciesExact validityFacts =
      VerificationReuseRejected.
Proof.
  reflexivity.
Qed.

Theorem out_of_scope_target_fact_rejects_reuse :
  forall dependenciesExact validityFacts,
    decideVerificationReuse
      true false dependenciesExact validityFacts =
      VerificationReuseRejected.
Proof.
  reflexivity.
Qed.

Theorem changed_dependency_fact_rejects_reuse :
  forall validityFacts,
    decideVerificationReuse
      true true false validityFacts =
      VerificationReuseRejected.
Proof.
  reflexivity.
Qed.

Theorem matching_empty_validity_scope_accepts_reuse :
  decideVerificationReuse true true true [] = VerificationReuseAccepted.
Proof.
  reflexivity.
Qed.

Theorem mismatching_validity_fact_rejects_reuse :
  decideVerificationReuse true true true [false] = VerificationReuseRejected.
Proof.
  reflexivity.
Qed.
