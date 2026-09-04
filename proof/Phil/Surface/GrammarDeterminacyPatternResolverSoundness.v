From Stdlib Require Import Bool.Bool Lists.List Strings.String.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyCertificate
  GrammarDeterminacyNullableFirst
  GrammarDeterminacyFollowOverlap
  GrammarDeterminacySimpleResolverSoundness
  GrammarDeterminacyStructuralScannerSoundness
  GrammarDeterminacyContinuationSoundness
  GrammarDeterminacyQualifiedNameSoundness.

Import ListNotations.
Open Scope string_scope.

(*
  Semantic soundness for the structural pattern overlap.

  #677 proves that every ordinary record_pattern derivation has the exact
  maximal qualified-name + "{" prefix that commits pattern branch 2.  The
  remaining overlapping branch is a plain identifier.  Its consumed token is
  exact, so the only way the structural scanner could misclassify it as a
  record pattern would be for the accepting continuation to begin with "." or
  "{".  GrammarDeterminacyFollowOverlap certifies directly, in the same
  compilation unit as the FOLLOW fixed point, that FOLLOW(pattern) excludes
  both tokens.
*)

Theorem phase1_surface_pattern_follow_excludes_dot :
  token_mem (OverlapLiteral ".") phase1_surface_pattern_follow = false.
Proof.
  pose proof phase1_surface_pattern_follow_structural_tail_check_true
    as Hcheck.
  apply andb_true_iff in Hcheck as [Hdot _].
  apply negb_true_iff in Hdot.
  exact Hdot.
Qed.

Theorem phase1_surface_pattern_follow_excludes_open_brace :
  token_mem (OverlapLiteral "{") phase1_surface_pattern_follow = false.
Proof.
  pose proof phase1_surface_pattern_follow_structural_tail_check_true
    as Hcheck.
  apply andb_true_iff in Hcheck as [_ Hbrace].
  apply negb_true_iff in Hbrace.
  exact Hbrace.
Qed.

Lemma continuation_lookahead_mem_literal_cons :
  forall literal tail follow,
    continuation_lookahead_mem (TLiteral literal :: tail) follow =
    token_mem (OverlapLiteral literal) follow.
Proof.
  reflexivity.
Qed.

Lemma phase1_surface_pattern_follow_literal_is_not_structural_record_tail :
  forall literal tail,
    continuation_lookahead_mem
      (TLiteral literal :: tail)
      phase1_surface_pattern_follow = true ->
    String.eqb literal "{" = false /\
    String.eqb literal "." = false.
Proof.
  intros literal tail Hcontinuation.
  rewrite continuation_lookahead_mem_literal_cons in Hcontinuation.
  split.
  - destruct (String.eqb literal "{") eqn:Hbrace.
    + apply String.eqb_eq in Hbrace.
      subst literal.
      rewrite phase1_surface_pattern_follow_excludes_open_brace
        in Hcontinuation.
      discriminate.
    + reflexivity.
  - destruct (String.eqb literal ".") eqn:Hdot.
    + apply String.eqb_eq in Hdot.
      subst literal.
      rewrite phase1_surface_pattern_follow_excludes_dot
        in Hcontinuation.
      discriminate.
    + reflexivity.
Qed.

Theorem phase1_surface_identifier_pattern_derivation_commits_pattern_branch :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "identifier") input rest tree ->
    continuation_lookahead_mem rest phase1_surface_pattern_follow = true ->
    pattern_decision input = Some (ChooseAlternative 0).
Proof.
  intros path input rest tree Hderive Hcontinuation.
  destruct
    (phase1_surface_identifier_derivation_is_exact
      path input rest tree Hderive)
    as [lexeme [tail [Hinput Hrest]]].
  rewrite Hrest in Hcontinuation.
  rewrite Hinput.
  destruct tail as [| next tail].
  - apply pattern_decision_identifier_end.
  - destruct next as [literal | class_name value].
    + destruct
        (phase1_surface_pattern_follow_literal_is_not_structural_record_tail
          literal tail Hcontinuation)
        as [Hbrace Hdot].
      apply pattern_decision_identifier_other_literal_tail.
      * exact Hbrace.
      * exact Hdot.
    + apply pattern_decision_identifier_lexical_tail.
Qed.

Theorem phase1_surface_pattern_structural_overlap_semantic_sound :
  (forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "identifier") input rest tree ->
    continuation_lookahead_mem rest phase1_surface_pattern_follow = true ->
    pattern_decision input = Some (ChooseAlternative 0)) /\
  (forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "record_pattern") input rest tree ->
    pattern_decision input = Some (ChooseAlternative 2)).
Proof.
  split.
  - exact phase1_surface_identifier_pattern_derivation_commits_pattern_branch.
  - exact phase1_surface_record_pattern_derivation_commits_pattern_branch.
Qed.
