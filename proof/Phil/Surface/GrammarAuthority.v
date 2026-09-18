From Stdlib Require Import Bool.Bool Arith.PeanoNat.

(*
  PHIL-SURFACE-GRAMMAR-001 — Phase 1 concrete grammar authority.

  This theorem family owns the specification/derivation boundary only:

  - exactly one canonical Grammar-v1 source authority is selected;
  - every proof-facing generated grammar names that exact source revision;
  - repeating the deterministic derivation yields the same artifact identity;
  - the production lexer reserved-word authority exactly matches the grammar's
    identifier-shaped literals; and
  - the generated formal artifact compiles warning-clean.

  Parser soundness/completeness, parser-library behavior, Unicode library
  behavior, and Haskell parser-to-grammar language correspondence remain
  PHIL-SURFACE-GRAMMAR-CORR-001/tooling boundaries.
*)

Definition GrammarSourceIdentity := nat.
Definition GrammarArtifactIdentity := nat.

Record GrammarAuthorityFacts : Type := mkGrammarAuthorityFacts {
  grammarCanonicalSource : GrammarSourceIdentity;
  grammarFirstEmbeddedSource : GrammarSourceIdentity;
  grammarSecondEmbeddedSource : GrammarSourceIdentity;
  grammarFirstArtifact : GrammarArtifactIdentity;
  grammarSecondArtifact : GrammarArtifactIdentity;
  grammarReservedWordsExact : bool;
  grammarFormalArtifactCompiles : bool;
  grammarFormalArtifactWarningClean : bool
}.

Definition GrammarAuthorityValid
  (facts : GrammarAuthorityFacts) : Prop :=
  grammarCanonicalSource facts <> 0 /\
  grammarFirstEmbeddedSource facts = grammarCanonicalSource facts /\
  grammarSecondEmbeddedSource facts = grammarCanonicalSource facts /\
  grammarFirstArtifact facts <> 0 /\
  grammarSecondArtifact facts = grammarFirstArtifact facts /\
  grammarReservedWordsExact facts = true /\
  grammarFormalArtifactCompiles facts = true /\
  grammarFormalArtifactWarningClean facts = true.

Theorem accepted_grammar_has_one_nonempty_canonical_source :
  forall facts,
    GrammarAuthorityValid facts ->
    grammarCanonicalSource facts <> 0.
Proof.
  intros facts Hvalid.
  exact (proj1 Hvalid).
Qed.

Theorem first_derivation_is_bound_to_canonical_source :
  forall facts,
    GrammarAuthorityValid facts ->
    grammarFirstEmbeddedSource facts = grammarCanonicalSource facts.
Proof.
  intros facts Hvalid.
  exact (proj1 (proj2 Hvalid)).
Qed.

Theorem repeated_derivation_remains_bound_to_canonical_source :
  forall facts,
    GrammarAuthorityValid facts ->
    grammarSecondEmbeddedSource facts = grammarCanonicalSource facts.
Proof.
  intros facts Hvalid.
  exact (proj1 (proj2 (proj2 Hvalid))).
Qed.

Theorem grammar_derivation_is_deterministic :
  forall facts,
    GrammarAuthorityValid facts ->
    grammarSecondArtifact facts = grammarFirstArtifact facts.
Proof.
  intros facts Hvalid.
  destruct Hvalid as [_ [_ [_ [_ [Hsame _]]]]].
  exact Hsame.
Qed.

Theorem grammar_reserved_word_authority_is_exact :
  forall facts,
    GrammarAuthorityValid facts ->
    grammarReservedWordsExact facts = true.
Proof.
  intros facts Hvalid.
  destruct Hvalid as [_ [_ [_ [_ [_ [Hkeywords _]]]]]].
  exact Hkeywords.
Qed.

Theorem generated_formal_grammar_compiles :
  forall facts,
    GrammarAuthorityValid facts ->
    grammarFormalArtifactCompiles facts = true.
Proof.
  intros facts Hvalid.
  destruct Hvalid as [_ [_ [_ [_ [_ [_ [Hcompiles _]]]]]]].
  exact Hcompiles.
Qed.

Theorem generated_formal_grammar_is_warning_clean :
  forall facts,
    GrammarAuthorityValid facts ->
    grammarFormalArtifactWarningClean facts = true.
Proof.
  intros facts Hvalid.
  destruct Hvalid as [_ [_ [_ [_ [_ [_ [_ Hclean]]]]]]].
  exact Hclean.
Qed.

Theorem source_substitution_cannot_satisfy_grammar_authority :
  forall facts,
    grammarFirstEmbeddedSource facts <> grammarCanonicalSource facts ->
    ~ GrammarAuthorityValid facts.
Proof.
  intros facts Hmismatch Hvalid.
  apply Hmismatch.
  eapply first_derivation_is_bound_to_canonical_source.
  exact Hvalid.
Qed.

Theorem nondeterministic_derivation_cannot_satisfy_grammar_authority :
  forall facts,
    grammarSecondArtifact facts <> grammarFirstArtifact facts ->
    ~ GrammarAuthorityValid facts.
Proof.
  intros facts Hmismatch Hvalid.
  apply Hmismatch.
  eapply grammar_derivation_is_deterministic.
  exact Hvalid.
Qed.
