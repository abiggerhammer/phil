From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDeterminacySimpleResolverSoundness
  GrammarAstSessionRecursionPayloadSpine
  GrammarAstSourceHeaderTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the `recursive identifier = session_expression` payload shell
   from #1079.  The body remains at the exact certified session-expression
   boundary; recursive traversal is a separate successor slice. *)

Theorem phase1_surface_normalize_recursive_session_payload_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_recursive_session_expression_for_totality
      input rest tree ->
    exists session,
      phase1_surface_normalize_recursive_session_payload_spine tree =
        Some session /\
      phase1_surface_recursive_session_payload_spine_tree session = tree.
Proof.
  intros path input rest tree Hderive.
  unfold phase1_surface_recursive_session_expression_for_totality in Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral "recursive";
        ENonterminal "identifier";
        ELiteral "=";
        ENonterminal "session_expression"
      ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 0
      (ELiteral "recursive")
      [ ENonterminal "identifier";
        ELiteral "=";
        ENonterminal "session_expression" ]
      input rest trees Hitems)
    as [after_keyword [keyword_tree [tail1_trees
      [Htrees [Hkeyword Htail1]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 1
      (ENonterminal "identifier")
      [ ELiteral "=";
        ENonterminal "session_expression" ]
      after_keyword rest tail1_trees Htail1)
    as [after_name [name_tree [tail2_trees
      [Htail1_trees [Hname Htail2]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 2
      (ELiteral "=")
      [ ENonterminal "session_expression" ]
      after_name rest tail2_trees Htail2)
    as [after_equals [equals_tree [tail3_trees
      [Htail2_trees [Hequals Htail3]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 3
      (ENonterminal "session_expression") []
      after_equals rest tail3_trees Htail3)
    as [after_body [body_tree [nil_trees
      [Htail3_trees [Hbody Hnil]]]]].
  rewrite Htrees, Htail1_trees, Htail2_trees, Htail3_trees in Htree.
  inversion Hnil; subst nil_trees.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "recursive" _ _ keyword_tree Hkeyword)
    as [keyword_tail [_ [_ Hkeyword_tree]]].
  destruct
    (phase1_surface_normalize_identifier_total_from_derivation
      _ _ _ name_tree Hname)
    as [name Hname_normalize].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "=" _ _ equals_tree Hequals)
    as [equals_tail [_ [_ Hequals_tree]]].
  pose proof
    (phase1_surface_validate_named_node_total_from_derivation
      "session_expression" _ _ _ body_tree Hbody)
    as Hbody_validate.
  pose (session :=
    {| phase1_recursive_session_name := name;
       phase1_recursive_session_body_tree := body_tree |}).
  assert (Hnormalize :
    phase1_surface_normalize_recursive_session_payload_spine tree =
      Some session).
  {
    rewrite Htree, Hkeyword_tree, Hequals_tree.
    unfold phase1_surface_normalize_recursive_session_payload_spine,
      phase1_surface_expect_sequence,
      phase1_surface_exact4,
      phase1_surface_expect_literal.
    cbn.
    rewrite Hname_normalize.
    rewrite Hbody_validate.
    unfold session.
    reflexivity.
  }
  exists session.
  split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_recursive_session_payload_spine_round_trip.
    exact Hnormalize.
Qed.
