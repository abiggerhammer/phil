From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstTermArgumentsExpressionFallbackBaseChoiceShiftRefinedListTotality
  GrammarAstTermArgumentsExpressionFallbackBaseChoiceTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Complete the derivation-driven totality lift for refined shift expressions
  through the term_arguments spine/tree carrier.

  This is the enclosing shell for the shared-fuel list witness proved in the
  preceding support file.  It preserves exact reconstruction of every
  derivable term_arguments ParseTree.

  Structural Rocq surface-correspondence only.  This continues
  PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Lemma
  phase1_surface_normalize_term_arguments_expression_fallback_base_choice_shift_refined_spine_fuel_total_from_spine_derivation :
  forall arguments path input rest,
    Derives phase1_surface_rules path (ENonterminal "term_arguments")
      input rest
      (phase1_surface_term_arguments_expression_fallback_base_choice_spine_tree
        arguments) ->
    exists fuel refined,
      phase1_surface_normalize_term_arguments_expression_fallback_base_choice_shift_refined_spine_fuel
        fuel arguments = Some refined.
Proof.
  intros [arguments] path input rest Hderive.
  unfold
    phase1_surface_term_arguments_expression_fallback_base_choice_spine_tree
    in Hderive.
  cbn in Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "term_arguments"
      input rest
      (PTNonterminal "term_arguments"
        (PTSequence
          [ PTLiteral "(";
            phase1_surface_term_argument_expression_fallback_base_choice_entries_tree
              arguments;
            PTLiteral ")"
          ]))
      Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_term_arguments_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  inversion Htree; subst subtree.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "term_arguments"))
      [ ELiteral "(";
        EOptional
          (ESequence
            [ ENonterminal "expression";
              ERepetition
                (ESequence
                  [ ELiteral ",";
                    ENonterminal "expression"
                  ])
            ]);
        ELiteral ")"
      ]
      input rest
      (PTSequence
        [ PTLiteral "(";
          phase1_surface_term_argument_expression_fallback_base_choice_entries_tree
            arguments;
          PTLiteral ")"
        ])
      Hbody)
    as [trees [Hsequence_tree Hitems]].
  inversion Hsequence_tree; subst trees.
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hentries : Derives phase1_surface_rules _
      (EOptional
        (ESequence
          [ ENonterminal "expression";
            ERepetition
              (ESequence
                [ ELiteral ",";
                  ENonterminal "expression"
                ])
          ]))
      _ _
      (phase1_surface_term_argument_expression_fallback_base_choice_entries_tree
        arguments) |- _ =>
      destruct
        (phase1_surface_normalize_term_argument_expression_fallback_base_choice_shift_refined_values_fuel_total_from_entries_derivation
          arguments _ _ _ Hentries)
        as [fuel [refined_arguments Hrefined_arguments]];
      exists fuel,
        {| phase1_term_arguments_expression_fallback_base_choice_shift_refined_spine_arguments :=
             refined_arguments |};
      cbn;
      rewrite Hrefined_arguments;
      reflexivity
  end.
Qed.

Theorem
  phase1_surface_normalize_term_arguments_expression_fallback_base_choice_shift_refined_tree_fuel_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "term_arguments")
      input rest tree ->
    exists fuel refined,
      phase1_surface_normalize_term_arguments_expression_fallback_base_choice_shift_refined_tree_fuel
        fuel tree = Some refined /\
      phase1_surface_term_arguments_expression_fallback_base_choice_shift_refined_spine_tree
        refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_term_arguments_expression_fallback_base_choice_tree_total_from_derivation
      path input rest tree Hderive)
    as [base [Hbase Hbase_round_trip]].
  pose proof Hderive as Hcanonical.
  rewrite <- Hbase_round_trip in Hcanonical.
  destruct
    (phase1_surface_normalize_term_arguments_expression_fallback_base_choice_shift_refined_spine_fuel_total_from_spine_derivation
      base path input rest Hcanonical)
    as [fuel [refined Hrefined]].
  assert (Hnormalize :
    phase1_surface_normalize_term_arguments_expression_fallback_base_choice_shift_refined_tree_fuel
      fuel tree = Some refined).
  {
    unfold
      phase1_surface_normalize_term_arguments_expression_fallback_base_choice_shift_refined_tree_fuel.
    rewrite Hbase.
    exact Hrefined.
  }
  exists fuel, refined.
  split.
  - exact Hnormalize.
  - eapply
      phase1_surface_normalize_term_arguments_expression_fallback_base_choice_shift_refined_tree_fuel_round_trip.
    exact Hnormalize.
Qed.
