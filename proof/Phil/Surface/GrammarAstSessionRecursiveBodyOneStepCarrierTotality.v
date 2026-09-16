From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDeterminacySimpleResolverSoundness
  GrammarAstSessionRecursiveBodyOneStepCarrierSpine
  GrammarAstSessionRecursiveOneStepCarrierTotality
  GrammarAstSessionContinueMutualRecursiveTreeAdapterTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the one-level recursive-body entry from #1117. *)

Lemma phase1_surface_recursive_session_payload_exposes_body :
  forall path input rest payload,
    Derives phase1_surface_rules path
      phase1_surface_recursive_session_expression_for_totality
      input rest
      (phase1_surface_recursive_session_payload_spine_tree payload) ->
    exists body_path body_input body_rest,
      Derives phase1_surface_rules body_path
        (ENonterminal "session_expression")
        body_input body_rest
        (phase1_recursive_session_body_tree payload).
Proof.
  intros path input rest [name body_tree] Hderive.
  unfold phase1_surface_recursive_session_expression_for_totality in Hderive.
  unfold phase1_surface_recursive_session_payload_spine_tree in Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral "recursive";
        ENonterminal "identifier";
        ELiteral "=";
        ENonterminal "session_expression"
      ]
      input rest
      (PTSequence
        [ PTLiteral "recursive";
          phase1_surface_identifier_tree name;
          PTLiteral "=";
          body_tree
        ])
      Hderive)
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
    as [after_body [actual_body_tree [nil_trees
      [Htail3_trees [Hbody Hnil]]]]].
  inversion Hnil; subst nil_trees.
  rewrite Htrees, Htail1_trees, Htail2_trees, Htail3_trees in Htree.
  inversion Htree; subst actual_body_tree.
  eexists _, _, _.
  exact Hbody.
Qed.

Theorem
  phase1_surface_normalize_recursive_body_one_step_session_spine_fuels_total_from_derivation :
  forall path input rest session,
    Derives phase1_surface_rules path
      (ENonterminal "session_expression") input rest
      (phase1_surface_recursive_one_step_session_spine_tree session) ->
    exists source_fuel closure_fuel refined,
      phase1_surface_normalize_recursive_body_one_step_session_spine_fuels
        source_fuel closure_fuel session = Some refined.
Proof.
  intros path input rest session Hderive.
  destruct session as [nonreference | reference_tree].
  - destruct nonreference as
      [direction parameter boundary guard continuation
      |choice
      |choice
      |terminal
      |recursive_payload
      |payload].
    + exists 0, 0.
      eexists.
      reflexivity.
    + exists 0, 0.
      eexists.
      reflexivity.
    + exists 0, 0.
      eexists.
      reflexivity.
    + exists 0, 0.
      eexists.
      reflexivity.
    + destruct recursive_payload as [name body_tree].
      cbn in Hderive.
      destruct
        (phase1_surface_selected_recursive_derivation
          path input rest
          (phase1_surface_recursive_session_payload_spine_tree
            {| phase1_recursive_session_name := name;
               phase1_recursive_session_body_tree := body_tree |})
          Hderive)
        as [recursive_path Hrecursive].
      destruct
        (phase1_surface_recursive_session_payload_exposes_body
          recursive_path input rest
          {| phase1_recursive_session_name := name;
             phase1_recursive_session_body_tree := body_tree |}
          Hrecursive)
        as [body_path [body_input [body_rest Hbody]]].
      destruct
        (phase1_surface_normalize_continue_mutual_recursive_session_tree_fuels_total_from_derivation
          body_path body_input body_rest body_tree Hbody)
        as [source_fuel [closure_fuel [body [Hbody_normalize Hbody_tree]]]].
      exists source_fuel, closure_fuel.
      exists
        (Phase1RecursiveBodyOneStepNonreferenceSession
          (Phase1RecursiveBodyOneStepRecursiveSession
            {| phase1_recursive_body_one_step_name := name;
               phase1_recursive_body_one_step_body := body |})).
      cbn.
      rewrite Hbody_normalize.
      reflexivity.
    + exists 0, 0.
      eexists.
      reflexivity.
  - exists 0, 0.
    eexists.
    reflexivity.
Qed.
