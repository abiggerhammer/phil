From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDeterminacySimpleResolverSoundness
  GrammarAstSessionRecursionPayloadSpine
  GrammarAstSourceHeaderTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the `continue identifier` payload carrier from #1079. *)

Theorem phase1_surface_normalize_continue_session_payload_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_continue_session_expression_for_totality
      input rest tree ->
    exists session,
      phase1_surface_normalize_continue_session_payload_spine tree = Some session /\
      phase1_surface_continue_session_payload_spine_tree session = tree.
Proof.
  intros path input rest tree Hderive.
  unfold phase1_surface_continue_session_expression_for_totality in Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral "continue";
        ENonterminal "identifier"
      ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 0
      (ELiteral "continue")
      [ ENonterminal "identifier" ]
      input rest trees Hitems)
    as [after_keyword [keyword_tree [tail1_trees
      [Htrees [Hkeyword Htail1]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 1
      (ENonterminal "identifier") []
      after_keyword rest tail1_trees Htail1)
    as [after_name [name_tree [nil_trees
      [Htail1_trees [Hname Hnil]]]]].
  rewrite Htrees, Htail1_trees in Htree.
  inversion Hnil; subst nil_trees.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "continue" _ _ keyword_tree Hkeyword)
    as [keyword_tail [_ [_ Hkeyword_tree]]].
  destruct
    (phase1_surface_normalize_identifier_total_from_derivation
      _ _ _ name_tree Hname)
    as [name Hname_normalize].
  pose (session :=
    {| phase1_continue_session_name := name |}).
  assert (Hnormalize :
    phase1_surface_normalize_continue_session_payload_spine tree =
      Some session).
  {
    rewrite Htree, Hkeyword_tree.
    unfold phase1_surface_normalize_continue_session_payload_spine,
      phase1_surface_expect_sequence,
      phase1_surface_exact2,
      phase1_surface_expect_literal.
    cbn.
    rewrite Hname_normalize.
    unfold session.
    reflexivity.
  }
  exists session.
  split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_continue_session_payload_spine_round_trip.
    exact Hnormalize.
Qed.
