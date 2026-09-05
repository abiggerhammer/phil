From Stdlib Require Import Bool.Bool Lists.List Strings.String.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyCertificate
  GrammarDeterminacyNullableFirst
  GrammarDeterminacySimpleResolvers
  GrammarDeterminacySimpleResolverSoundness
  GrammarDeterminacyPredictiveOracle
  GrammarDeterminacyContinuationSoundness
  GrammarDeterminacyOracleAssemblyCoverage
  GrammarDeterminacyTrailingCommaConversion.

Import ListNotations.
Open Scope string_scope.

(*
  Stop-side specialization for the five trailing-comma repetition overlaps.

  A one-token FOLLOW fact is not, by itself, enough to justify stopping before
  a comma: ordinary repetition may always stop nondeterministically.  The
  oracle-assembly checker retained the exact enclosing tail shape needed to
  recover the missing two-token distinction.  This file combines that shape
  with the ordinary tail derivation and its accepting continuation.
*)

Lemma continuation_single_close_shape :
  forall input,
    continuation_lookahead_mem input [OverlapLiteral "}"] = true ->
    exists tail,
      input = TLiteral "}" :: tail.
Proof.
  intros input Hcontinuation.
  destruct input as [| first_token tail].
  - simpl in Hcontinuation.
    discriminate Hcontinuation.
  - destruct first_token as [literal | class_name lexeme].
    + unfold continuation_lookahead_mem in Hcontinuation.
      simpl in Hcontinuation.
      destruct (String.eqb literal "}") eqn:Heq.
      * apply String.eqb_eq in Heq.
        subst literal.
        exists tail.
        reflexivity.
      * discriminate Hcontinuation.
    + simpl in Hcontinuation.
      discriminate Hcontinuation.
Qed.

Lemma derives_sequence_nil_input_equals_rest :
  forall rules path index input rest trees,
    DerivesSequence rules path index [] input rest trees ->
    input = rest.
Proof.
  intros rules path index input rest trees Hderive.
  inversion Hderive; subst.
  reflexivity.
Qed.

Lemma trailing_comma_tail_derivation_stop_shape :
  forall path index items input rest trees outer_follow,
    trailing_comma_tail_shapeb items outer_follow = true ->
    DerivesSequence phase1_surface_rules path index
      items input rest trees ->
    continuation_lookahead_mem rest outer_follow = true ->
    (exists tail,
      input = TLiteral "}" :: tail) \/
    (exists tail,
      input = TLiteral "," :: TLiteral "}" :: tail).
Proof.
  intros path index items input rest trees outer_follow
    Hshape Hderive Hcontinuation.
  destruct (trailing_comma_tail_shapeb_cases items outer_follow Hshape)
    as [Htwo | [Hone Hfollow]].
  - subst items.
    destruct
      (derives_sequence_cons_exposes_head
        phase1_surface_rules path index
        (EOptional (ELiteral ",")) [ELiteral "}"]
        input rest trees Hderive)
      as [middle [optional_tree [tail_trees [Hoptional Htail]]]].
    destruct
      (derives_sequence_cons_exposes_head
        phase1_surface_rules path (S index)
        (ELiteral "}") []
        middle rest tail_trees Htail)
      as [after_close [close_tree [nil_trees [Hclose Hnil]]]].
    destruct
      (literal_derivation_is_exact
        phase1_surface_rules
        (descend path (AtSequence (S index)))
        "}" middle after_close close_tree Hclose)
      as [close_tail [Hmiddle [Hafter_close Hclose_tree]]].
    destruct
      (optional_derivation_exposes_presence
        phase1_surface_rules
        (descend path (AtSequence index))
        (ELiteral ",") input middle optional_tree Hoptional)
      as [[Hnone Hoptional_tree] |
          [comma_tree [Hoptional_tree Hcomma]]].
    + left.
      exists close_tail.
      rewrite <- Hnone.
      exact Hmiddle.
    + destruct
        (literal_derivation_is_exact
          phase1_surface_rules
          (descend (descend path (AtSequence index)) AtOptionalBody)
          "," input middle comma_tree Hcomma)
        as [comma_tail [Hinput [Hmiddle_comma Hcomma_tree]]].
      right.
      exists close_tail.
      rewrite Hinput.
      rewrite <- Hmiddle_comma.
      rewrite Hmiddle.
      reflexivity.
  - subst items.
    subst outer_follow.
    destruct
      (derives_sequence_cons_exposes_head
        phase1_surface_rules path index
        (EOptional (ELiteral ",")) []
        input rest trees Hderive)
      as [middle [optional_tree [tail_trees [Hoptional Htail]]]].
    pose proof
      (derives_sequence_nil_input_equals_rest
        phase1_surface_rules path (S index)
        middle rest tail_trees Htail)
      as Hmiddle_rest.
    subst rest.
    destruct (continuation_single_close_shape middle Hcontinuation)
      as [close_tail Hmiddle].
    destruct
      (optional_derivation_exposes_presence
        phase1_surface_rules
        (descend path (AtSequence index))
        (ELiteral ",") input middle optional_tree Hoptional)
      as [[Hnone Hoptional_tree] |
          [comma_tree [Hoptional_tree Hcomma]]].
    + left.
      exists close_tail.
      rewrite <- Hnone.
      exact Hmiddle.
    + destruct
        (literal_derivation_is_exact
          phase1_surface_rules
          (descend (descend path (AtSequence index)) AtOptionalBody)
          "," input middle comma_tree Hcomma)
        as [comma_tail [Hinput [Hmiddle_comma Hcomma_tree]]].
      right.
      exists close_tail.
      rewrite Hinput.
      rewrite <- Hmiddle_comma.
      rewrite Hmiddle.
      reflexivity.
Qed.

Theorem trailing_comma_tail_derivation_stops :
  forall path index items input rest trees outer_follow,
    trailing_comma_tail_shapeb items outer_follow = true ->
    DerivesSequence phase1_surface_rules path index
      items input rest trees ->
    continuation_lookahead_mem rest outer_follow = true ->
    trailing_comma_repeat_decision input = Some ChooseRepetitionStop.
Proof.
  intros path index items input rest trees outer_follow
    Hshape Hderive Hcontinuation.
  destruct
    (trailing_comma_tail_derivation_stop_shape
      path index items input rest trees outer_follow
      Hshape Hderive Hcontinuation)
    as [[tail Hinput] | [tail Hinput]].
  - rewrite Hinput.
    apply trailing_comma_decision_close_tail_stops.
  - rewrite Hinput.
    apply trailing_comma_decision_trailing_close_tail_stops.
Qed.
