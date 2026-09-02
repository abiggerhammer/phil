From Stdlib Require Import Arith.PeanoNat Strings.String.

From Phil.Surface Require Import Grammar.

Open Scope string_scope.

(*
  PHIL-SURFACE-REV-001 — exact concrete-grammar revision binding.

  Grammar.v is deterministically generated from grammar/phase1-surface.ebnf by
  scripts/derive_phase1_surface_grammar.py.  The exact source SHA-256 carried by
  that generated artifact is therefore the proof-facing concrete-grammar
  identity used below.

  The Phase-1 portable SourceBundle checker has no implicit compatibility or
  migration relation: one well-formed grammar-revision record is accepted only
  when it equals the explicitly selected front-end revision.  Missing,
  duplicate, malformed, and incompatible records reject before source lineage
  is resolved.

  SHA-256 collision resistance, the Python EBNF-to-Rocq derivation, concrete
  Haskell Text decoding/equality, and source parser correctness remain explicit
  correspondence/tooling boundaries.
*)

Definition GrammarRevision := string.

Definition canonicalPhase1GrammarRevision : GrammarRevision :=
  String.append "sha256:" phase1_surface_grammar_source_sha256.

Inductive GrammarRevisionRecord : Type :=
| GrammarRevisionMissing
| GrammarRevisionDuplicate : GrammarRevision -> GrammarRevision -> GrammarRevisionRecord
| GrammarRevisionMalformed : string -> GrammarRevisionRecord
| GrammarRevisionPresent : GrammarRevision -> GrammarRevisionRecord.

Inductive GrammarBindingDecision : Type :=
| GrammarRevisionBound : GrammarRevision -> GrammarBindingDecision
| GrammarRevisionRejected.

Definition decideGrammarRevisionBinding
  (expected : GrammarRevision)
  (record : GrammarRevisionRecord) : GrammarBindingDecision :=
  match record with
  | GrammarRevisionPresent actual =>
      if string_dec expected actual
      then GrammarRevisionBound actual
      else GrammarRevisionRejected
  | _ => GrammarRevisionRejected
  end.

Record SourceBundleModel : Type := mkSourceBundleModel {
  bundleGrammarRecord : GrammarRevisionRecord;
  bundleSourcePayloadIdentity : nat
}.

Definition decideSourceBundleGrammar
  (expected : GrammarRevision)
  (bundle : SourceBundleModel) : GrammarBindingDecision :=
  decideGrammarRevisionBinding expected (bundleGrammarRecord bundle).

Definition ExplicitGrammarCompatibilityPolicy : Type :=
  GrammarRevision -> GrammarRevision -> Prop.

Definition ExtendedGrammarAdmission
  (policy : ExplicitGrammarCompatibilityPolicy)
  (expected actual : GrammarRevision) : Prop :=
  expected = actual \/ policy expected actual.

Theorem canonical_revision_is_exact_derived_grammar_digest :
  canonicalPhase1GrammarRevision =
    String.append "sha256:" phase1_surface_grammar_source_sha256.
Proof.
  reflexivity.
Qed.

Theorem exact_grammar_revision_is_admitted :
  forall expected,
    decideGrammarRevisionBinding
      expected (GrammarRevisionPresent expected) =
    GrammarRevisionBound expected.
Proof.
  intros expected.
  unfold decideGrammarRevisionBinding.
  destruct (string_dec expected expected) as [_ | Hneq].
  - reflexivity.
  - contradiction.
Qed.

Theorem missing_grammar_revision_rejects :
  forall expected,
    decideGrammarRevisionBinding expected GrammarRevisionMissing =
    GrammarRevisionRejected.
Proof.
  reflexivity.
Qed.

Theorem duplicate_grammar_revision_rejects :
  forall expected first second,
    decideGrammarRevisionBinding
      expected (GrammarRevisionDuplicate first second) =
    GrammarRevisionRejected.
Proof.
  reflexivity.
Qed.

Theorem malformed_grammar_revision_rejects :
  forall expected raw,
    decideGrammarRevisionBinding
      expected (GrammarRevisionMalformed raw) =
    GrammarRevisionRejected.
Proof.
  reflexivity.
Qed.

Theorem incompatible_grammar_revision_rejects :
  forall expected actual,
    expected <> actual ->
    decideGrammarRevisionBinding
      expected (GrammarRevisionPresent actual) =
    GrammarRevisionRejected.
Proof.
  intros expected actual Hdifferent.
  unfold decideGrammarRevisionBinding.
  destruct (string_dec expected actual) as [Hequal | _].
  - contradiction.
  - reflexivity.
Qed.

Theorem accepted_binding_is_exact :
  forall expected record actual,
    decideGrammarRevisionBinding expected record = GrammarRevisionBound actual ->
    record = GrammarRevisionPresent expected /\ actual = expected.
Proof.
  intros expected record actual Haccepted.
  destruct record as [|first second|raw|present]; simpl in Haccepted;
    try discriminate.
  destruct (string_dec expected present) as [Hequal | Hneq].
  - subst present.
    injection Haccepted as Hactual.
    subst actual.
    split; reflexivity.
  - discriminate.
Qed.

Theorem accepted_bundle_retains_selected_revision :
  forall expected payload actual,
    decideSourceBundleGrammar
      expected
      (mkSourceBundleModel (GrammarRevisionPresent actual) payload) =
      GrammarRevisionBound expected ->
    actual = expected.
Proof.
  intros expected payload actual Haccepted.
  unfold decideSourceBundleGrammar in Haccepted.
  pose proof (accepted_binding_is_exact
    expected (GrammarRevisionPresent actual) expected Haccepted) as Hexact.
  destruct Hexact as [Hrecord _].
  injection Hrecord.
  trivial.
Qed.

Theorem source_payload_cannot_rebind_grammar_revision :
  forall expected record firstPayload secondPayload,
    decideSourceBundleGrammar
      expected (mkSourceBundleModel record firstPayload) =
    decideSourceBundleGrammar
      expected (mkSourceBundleModel record secondPayload).
Proof.
  reflexivity.
Qed.

Theorem revision_change_reopens_old_bundle :
  forall priorRevision nextRevision payload,
    priorRevision <> nextRevision ->
    decideSourceBundleGrammar
      nextRevision
      (mkSourceBundleModel
        (GrammarRevisionPresent priorRevision)
        payload) =
    GrammarRevisionRejected.
Proof.
  intros priorRevision nextRevision payload Hdifferent.
  unfold decideSourceBundleGrammar.
  apply incompatible_grammar_revision_rejects.
  intro Hequal.
  apply Hdifferent.
  symmetry.
  exact Hequal.
Qed.

Theorem one_bundle_cannot_bind_two_distinct_selected_revisions :
  forall firstExpected secondExpected record firstActual secondActual,
    decideGrammarRevisionBinding firstExpected record =
      GrammarRevisionBound firstActual ->
    decideGrammarRevisionBinding secondExpected record =
      GrammarRevisionBound secondActual ->
    firstExpected = secondExpected.
Proof.
  intros firstExpected secondExpected record firstActual secondActual
    Hfirst Hsecond.
  pose proof (accepted_binding_is_exact
    firstExpected record firstActual Hfirst) as HfirstExact.
  pose proof (accepted_binding_is_exact
    secondExpected record secondActual Hsecond) as HsecondExact.
  destruct HfirstExact as [HfirstRecord _].
  destruct HsecondExact as [HsecondRecord _].
  rewrite HfirstRecord in HsecondRecord.
  injection HsecondRecord.
  trivial.
Qed.

Theorem cross_revision_admission_requires_explicit_policy :
  forall policy expected actual,
    expected <> actual ->
    ExtendedGrammarAdmission policy expected actual ->
    policy expected actual.
Proof.
  intros policy expected actual Hdifferent Hadmitted.
  destruct Hadmitted as [Hequal | Hpolicy].
  - contradiction.
  - exact Hpolicy.
Qed.

Theorem phase1_has_no_implicit_cross_revision_admission :
  forall expected actual,
    expected <> actual ->
    decideGrammarRevisionBinding
      expected (GrammarRevisionPresent actual) <>
    GrammarRevisionBound actual.
Proof.
  intros expected actual Hdifferent Haccepted.
  rewrite (incompatible_grammar_revision_rejects
    expected actual Hdifferent) in Haccepted.
  discriminate.
Qed.
