From Stdlib Require Import Bool.Bool.

Inductive GrammarAuthorityDecision : Type :=
| GrammarAuthorityAccepted
| GrammarAuthorityRejected.

Definition grammarAuthorityFactsb
  (canonicalSourcePresent firstSourceExact secondSourceExact
   deterministicArtifact reservedWordsExact formalArtifactCompiles
   warningClean : bool) : bool :=
  canonicalSourcePresent &&
  firstSourceExact &&
  secondSourceExact &&
  deterministicArtifact &&
  reservedWordsExact &&
  formalArtifactCompiles &&
  warningClean.

Definition decideGrammarAuthority
  (canonicalSourcePresent firstSourceExact secondSourceExact
   deterministicArtifact reservedWordsExact formalArtifactCompiles
   warningClean : bool) : GrammarAuthorityDecision :=
  if grammarAuthorityFactsb
      canonicalSourcePresent firstSourceExact secondSourceExact
      deterministicArtifact reservedWordsExact formalArtifactCompiles
      warningClean
  then GrammarAuthorityAccepted
  else GrammarAuthorityRejected.

Theorem exact_grammar_authority_accepts :
  decideGrammarAuthority true true true true true true true =
    GrammarAuthorityAccepted.
Proof. reflexivity. Qed.

Theorem missing_or_substituted_source_rejects :
  decideGrammarAuthority false true true true true true true =
      GrammarAuthorityRejected /\
  decideGrammarAuthority true false true true true true true =
      GrammarAuthorityRejected /\
  decideGrammarAuthority true true false true true true true =
      GrammarAuthorityRejected.
Proof. repeat split; reflexivity. Qed.

Theorem nondeterministic_derivation_rejects :
  decideGrammarAuthority true true true false true true true =
    GrammarAuthorityRejected.
Proof. reflexivity. Qed.

Theorem lexical_authority_mismatch_rejects :
  decideGrammarAuthority true true true true false true true =
    GrammarAuthorityRejected.
Proof. reflexivity. Qed.

Theorem formal_compile_or_warning_failure_rejects :
  decideGrammarAuthority true true true true true false true =
      GrammarAuthorityRejected /\
  decideGrammarAuthority true true true true true true false =
      GrammarAuthorityRejected.
Proof. split; reflexivity. Qed.
