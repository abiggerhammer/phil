From Stdlib Require Import Bool.Bool Setoids.Setoid.

From Phil.Surface Require Import GrammarRevision.

(*
  Machine-facing implementation-refinement surface for PHIL-SURFACE-REV-001.

  Native decoding has three facts at the exact grammar-binding competence
  boundary:

  - one successfully parsed grammar revision record is present;
  - that revision is exactly the selected revision; and
  - source payload identity cannot participate in or change that binding.

  Missing, duplicate, malformed, and incompatible revision inputs therefore
  fail closed before any accepted binding reaches this gate.  Concrete SHA-256
  derivation, Text decoding/equality, line parsing, and diagnostic payloads stay
  native/tooling boundaries.
*)

Definition GrammarRevisionImplementationFacts
  (expected : GrammarRevision)
  (record : GrammarRevisionRecord)
  (actual : GrammarRevision)
  (firstPayload secondPayload : nat) : Prop :=
  record = GrammarRevisionPresent expected /\
  actual = expected /\
  decideSourceBundleGrammar
    expected (mkSourceBundleModel record firstPayload) =
  decideSourceBundleGrammar
    expected (mkSourceBundleModel record secondPayload).

Theorem grammar_revision_implementation_facts_exact :
  forall expected record actual firstPayload secondPayload,
    GrammarRevisionImplementationFacts
      expected record actual firstPayload secondPayload <->
    decideGrammarRevisionBinding expected record =
      GrammarRevisionBound actual.
Proof.
  intros expected record actual firstPayload secondPayload.
  split.
  - intros [Hrecord [Hactual _]].
    subst actual.
    rewrite Hrecord.
    apply exact_grammar_revision_is_admitted.
  - intros Haccepted.
    pose proof
      (accepted_binding_is_exact expected record actual Haccepted)
      as [Hrecord Hactual].
    split.
    + exact Hrecord.
    + split.
      * exact Hactual.
      * apply source_payload_cannot_rebind_grammar_revision.
Qed.

Definition decideGrammarRevisionBindingByFacts
  (competentPresent exactSelectedRevision payloadIndependent : bool) : bool :=
  andb competentPresent (andb exactSelectedRevision payloadIndependent).

Theorem decideGrammarRevisionBindingByFacts_classifies :
  forall expected record actual firstPayload secondPayload
    competentPresent exactSelectedRevision payloadIndependent,
    (competentPresent = true <->
      record = GrammarRevisionPresent expected) ->
    (exactSelectedRevision = true <-> actual = expected) ->
    (payloadIndependent = true <->
      decideSourceBundleGrammar
        expected (mkSourceBundleModel record firstPayload) =
      decideSourceBundleGrammar
        expected (mkSourceBundleModel record secondPayload)) ->
    decideGrammarRevisionBindingByFacts
      competentPresent exactSelectedRevision payloadIndependent = true <->
    decideGrammarRevisionBinding expected record =
      GrammarRevisionBound actual.
Proof.
  intros expected record actual firstPayload secondPayload
    competentPresent exactSelectedRevision payloadIndependent
    Hpresent Hexact Hpayload.
  unfold decideGrammarRevisionBindingByFacts.
  repeat rewrite andb_true_iff.
  rewrite Hpresent, Hexact, Hpayload.
  apply grammar_revision_implementation_facts_exact.
Qed.
