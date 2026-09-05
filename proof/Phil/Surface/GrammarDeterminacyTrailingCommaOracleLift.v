From Stdlib Require Import Bool.Bool Lists.List Strings.String.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacySimpleResolvers
  GrammarDeterminacySimpleResolverSoundness
  GrammarDeterminacyStructuralResolvers
  GrammarDeterminacyPredictiveOracle
  GrammarDeterminacyContinuationSoundness
  GrammarDeterminacyOracleAssemblyCoverage
  GrammarDeterminacyTrailingCommaConversion
  GrammarDeterminacyTrailingCommaStop.

Import ListNotations.
Open Scope string_scope.

(*
  Lift the two semantic trailing-comma commitments into the one certified
  predictive oracle used by PHIL-SURFACE-DETERM-001.

  The simple resolver checks the two reserved-keyword suffixes before the five
  trailing-comma suffixes.  First we show that a certified trailing-comma path
  necessarily ends at a sequence child, so neither reserved-keyword suffix can
  match it.  The remaining lemmas then lift raw Continue/Stop decisions through
  the simple resolver, the combined certified overlap resolver, and finally the
  full predictive oracle.
*)

Lemma trailing_comma_repeat_path_excludes_reserved_suffixes :
  forall path,
    trailing_comma_repeat_pathb path = true ->
    path_has_suffixb path provider_declaration_suffix = false /\
    path_has_suffixb path generic_requirement_suffix = false.
Proof.
  intros path Htrail.
  unfold trailing_comma_repeat_pathb in Htrail.
  unfold case_pattern_comma_repeat_suffix,
    construct_expression_comma_repeat_suffix,
    record_decl_comma_repeat_suffix,
    record_pattern_comma_repeat_suffix,
    variant_payload_comma_repeat_suffix in Htrail.
  unfold provider_declaration_suffix, generic_requirement_suffix.
  unfold path_has_suffixb in Htrail |- *.
  remember (rev path) as reversed eqn:Hreversed.
  destruct reversed as [| last reversed].
  - simpl in Htrail.
    discriminate Htrail.
  - destruct last as [name | index | index | |].
    + simpl in Htrail.
      discriminate Htrail.
    + split; reflexivity.
    + simpl in Htrail.
      discriminate Htrail.
    + simpl in Htrail.
      discriminate Htrail.
    + simpl in Htrail.
      discriminate Htrail.
Qed.

Lemma phase1_surface_simple_resolver_trailing_path :
  forall path input decision,
    trailing_comma_repeat_pathb path = true ->
    trailing_comma_repeat_decision input = Some decision ->
    phase1_surface_simple_resolver path input = Some decision.
Proof.
  intros path input decision Hpath Hdecision.
  destruct
    (trailing_comma_repeat_path_excludes_reserved_suffixes path Hpath)
    as [Hprovider Hgeneric].
  unfold phase1_surface_simple_resolver.
  rewrite Hprovider, Hgeneric, Hpath.
  exact Hdecision.
Qed.

Lemma phase1_surface_certified_overlap_resolver_trailing_path :
  forall path input decision,
    trailing_comma_repeat_pathb path = true ->
    trailing_comma_repeat_decision input = Some decision ->
    phase1_surface_certified_overlap_resolver path input = Some decision.
Proof.
  intros path input decision Hpath Hdecision.
  pose proof
    (phase1_surface_simple_resolver_trailing_path
      path input decision Hpath Hdecision)
    as Hsimple.
  unfold phase1_surface_certified_overlap_resolver.
  rewrite Hsimple.
  reflexivity.
Qed.

Theorem phase1_surface_predictive_oracle_trailing_path :
  forall path input decision,
    trailing_comma_repeat_pathb path = true ->
    trailing_comma_repeat_decision input = Some decision ->
    phase1_surface_predictive_oracle path input = Some decision.
Proof.
  intros path input decision Hpath Hdecision.
  apply phase1_surface_predictive_oracle_extends_certified_overlap_resolver.
  apply phase1_surface_certified_overlap_resolver_trailing_path;
    assumption.
Qed.

Theorem trailing_comma_repetition_body_predictive_continues :
  forall path index body input rest tree,
    trailing_comma_repeat_pathb
      (descend path (AtSequence index)) = true ->
    comma_identifier_repetition_bodyb body = true ->
    Derives phase1_surface_rules
      (descend (descend path (AtSequence index)) AtRepetitionBody)
      body input rest tree ->
    phase1_surface_predictive_oracle
      (descend path (AtSequence index)) input =
      Some ChooseRepetitionContinue.
Proof.
  intros path index body input rest tree Hpath Hshape Hderive.
  apply phase1_surface_predictive_oracle_trailing_path.
  - exact Hpath.
  - apply
      (trailing_comma_body_derivation_continues
        (descend (descend path (AtSequence index)) AtRepetitionBody)
        body input rest tree Hshape Hderive).
Qed.

Theorem trailing_comma_sequence_tail_predictive_stops :
  forall path index items input rest trees outer_follow,
    trailing_comma_repeat_pathb
      (descend path (AtSequence index)) = true ->
    trailing_comma_tail_shapeb items outer_follow = true ->
    DerivesSequence phase1_surface_rules path (S index)
      items input rest trees ->
    continuation_lookahead_mem rest outer_follow = true ->
    phase1_surface_predictive_oracle
      (descend path (AtSequence index)) input =
      Some ChooseRepetitionStop.
Proof.
  intros path index items input rest trees outer_follow
    Hpath Hshape Hderive Hcontinuation.
  apply phase1_surface_predictive_oracle_trailing_path.
  - exact Hpath.
  - apply
      (trailing_comma_tail_derivation_stops
        path (S index) items input rest trees outer_follow
        Hshape Hderive Hcontinuation).
Qed.
