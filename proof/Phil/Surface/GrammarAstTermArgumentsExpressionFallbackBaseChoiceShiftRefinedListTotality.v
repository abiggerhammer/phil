From Stdlib Require Import Arith.PeanoNat Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstTermArgumentsExpressionFallbackBaseChoiceShiftRefinedArgumentTotality
  GrammarAstTermArgumentsExpressionFallbackBaseChoiceShiftRefinedFuelSupport.

Import ListNotations.
Open Scope string_scope.

(*
  Shared-fuel totality across the finite term_arguments value list.

  Each expression has a local finite-fuel refined witness.  This file combines
  those witnesses with Nat.max across the comma suffix repetition and the
  optional first/rest entries shell, using the monotonicity facts from the
  preceding fuel-support slice.

  Structural Rocq surface-correspondence only.  This continues
  PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Lemma
  phase1_surface_normalize_term_argument_expression_fallback_base_choice_shift_refined_values_fuel_total_from_suffix_repetition :
  forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body = ESequence [ELiteral ","; ENonterminal "expression"] ->
    forall arguments,
      trees =
        map
          phase1_surface_term_argument_expression_fallback_base_choice_suffix_tree
          arguments ->
      exists fuel refined,
        phase1_surface_normalize_term_argument_expression_fallback_base_choice_shift_refined_values_fuel
          fuel arguments = Some refined.
Proof.
  intros path body input rest trees Hderive Hbody_shape.
  subst body.
  induction Hderive as
    [path body input
    |path body input middle rest tree trees
       Hitem Hprogress Hrest IHrest];
    intros arguments Htrees.
  - destruct arguments as [|argument arguments]; cbn in Htrees.
    + exists 0, [].
      reflexivity.
    + discriminate Htrees.
  - destruct arguments as [|argument arguments]; cbn in Htrees;
      try discriminate Htrees.
    inversion Htrees; subst tree trees.
    unfold
      phase1_surface_term_argument_expression_fallback_base_choice_suffix_tree
      in Hitem.
    destruct
      (derives_sequence_expression_exposes_items
        phase1_surface_rules
        (descend path AtRepetitionBody)
        [ ELiteral ",";
          ENonterminal "expression"
        ]
        input middle
        (PTSequence
          [ PTLiteral ",";
            phase1_surface_expression_fallback_base_choice_spine_tree argument
          ])
        Hitem)
      as [item_trees [Hitem_tree Hitem_items]].
    inversion Hitem_tree; subst item_trees.
    repeat match goal with
    | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
        inversion Hseq; subst; clear Hseq
    end.
    match goal with
    | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
        inversion Hnil; subst; clear Hnil
    end.
    match goal with
    | Hargument : Derives phase1_surface_rules _
        (ENonterminal "expression")
        _ _
        (phase1_surface_expression_fallback_base_choice_spine_tree argument)
        |- _ =>
        destruct
          (phase1_surface_normalize_expression_fallback_base_choice_shift_refined_from_base_choice_spine_fuel_total_from_derivation
            argument _ _ _ Hargument)
          as [item_fuel [refined_argument Hrefined_argument]];
        destruct (IHrest arguments eq_refl)
          as [rest_fuel [refined_rest Hrefined_rest]];
        let fuel := constr:(Nat.max item_fuel rest_fuel) in
        pose proof
          (phase1_surface_normalize_expression_fallback_base_choice_shift_refined_from_base_choice_spine_fuel_monotone
            item_fuel fuel argument refined_argument
            (Nat.le_max_l item_fuel rest_fuel)
            Hrefined_argument)
          as Hrefined_argument_larger;
        pose proof
          (phase1_surface_normalize_term_argument_expression_fallback_base_choice_shift_refined_values_fuel_monotone
            rest_fuel fuel arguments refined_rest
            (Nat.le_max_r item_fuel rest_fuel)
            Hrefined_rest)
          as Hrefined_rest_larger;
        exists fuel, (refined_argument :: refined_rest);
        cbn;
        rewrite Hrefined_argument_larger, Hrefined_rest_larger;
        reflexivity
    end.
Qed.

Lemma
  phase1_surface_normalize_term_argument_expression_fallback_base_choice_shift_refined_values_fuel_total_from_entries_derivation :
  forall arguments path input rest,
    Derives phase1_surface_rules path
      (EOptional
        (ESequence
          [ ENonterminal "expression";
            ERepetition
              (ESequence
                [ ELiteral ",";
                  ENonterminal "expression"
                ])
          ]))
      input rest
      (phase1_surface_term_argument_expression_fallback_base_choice_entries_tree
        arguments) ->
    exists fuel refined,
      phase1_surface_normalize_term_argument_expression_fallback_base_choice_shift_refined_values_fuel
        fuel arguments = Some refined.
Proof.
  intros arguments path input rest Hderive.
  destruct arguments as [|first rest_arguments].
  - exists 0, [].
    reflexivity.
  - cbn in Hderive |- *.
    inversion Hderive; subst.
    match goal with
    | Hbody : Derives phase1_surface_rules _
        (ESequence
          [ ENonterminal "expression";
            ERepetition
              (ESequence
                [ ELiteral ",";
                  ENonterminal "expression"
                ])
          ])
        _ _
        (PTSequence
          [ phase1_surface_expression_fallback_base_choice_spine_tree first;
            PTRepetition
              (map
                phase1_surface_term_argument_expression_fallback_base_choice_suffix_tree
                rest_arguments)
          ]) |- _ =>
        destruct
          (derives_sequence_expression_exposes_items
            phase1_surface_rules _
            [ ENonterminal "expression";
              ERepetition
                (ESequence
                  [ ELiteral ",";
                    ENonterminal "expression"
                  ])
            ]
            _ _
            (PTSequence
              [ phase1_surface_expression_fallback_base_choice_spine_tree first;
                PTRepetition
                  (map
                    phase1_surface_term_argument_expression_fallback_base_choice_suffix_tree
                    rest_arguments)
              ])
            Hbody)
          as [trees [Htree Hitems]];
        inversion Htree; subst trees;
        repeat match goal with
        | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
            inversion Hseq; subst; clear Hseq
        end;
        match goal with
        | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
            inversion Hnil; subst; clear Hnil
        end;
        match goal with
        | Hfirst : Derives phase1_surface_rules _
            (ENonterminal "expression")
            _ _
            (phase1_surface_expression_fallback_base_choice_spine_tree first),
          Hrepeat : Derives phase1_surface_rules _
            (ERepetition
              (ESequence
                [ ELiteral ",";
                  ENonterminal "expression"
                ]))
            _ _
            (PTRepetition
              (map
                phase1_surface_term_argument_expression_fallback_base_choice_suffix_tree
                rest_arguments)) |- _ =>
            destruct
              (phase1_surface_normalize_expression_fallback_base_choice_shift_refined_from_base_choice_spine_fuel_total_from_derivation
                first _ _ _ Hfirst)
              as [first_fuel [refined_first Hrefined_first]];
            destruct
              (phase1_surface_repetition_derivation_exposes
                _
                (ESequence
                  [ ELiteral ",";
                    ENonterminal "expression"
                  ])
                _ _
                (PTRepetition
                  (map
                    phase1_surface_term_argument_expression_fallback_base_choice_suffix_tree
                    rest_arguments))
                Hrepeat)
              as [rest_trees [Hrest_tree Hrest_body]];
            inversion Hrest_tree; subst rest_trees;
            destruct
              (phase1_surface_normalize_term_argument_expression_fallback_base_choice_shift_refined_values_fuel_total_from_suffix_repetition
                _
                (ESequence
                  [ ELiteral ",";
                    ENonterminal "expression"
                  ])
                _ _
                (map
                  phase1_surface_term_argument_expression_fallback_base_choice_suffix_tree
                  rest_arguments)
                Hrest_body eq_refl
                rest_arguments eq_refl)
              as [rest_fuel [refined_rest Hrefined_rest]];
            let fuel := constr:(Nat.max first_fuel rest_fuel) in
            pose proof
              (phase1_surface_normalize_expression_fallback_base_choice_shift_refined_from_base_choice_spine_fuel_monotone
                first_fuel fuel first refined_first
                (Nat.le_max_l first_fuel rest_fuel)
                Hrefined_first)
              as Hrefined_first_larger;
            pose proof
              (phase1_surface_normalize_term_argument_expression_fallback_base_choice_shift_refined_values_fuel_monotone
                rest_fuel fuel rest_arguments refined_rest
                (Nat.le_max_r first_fuel rest_fuel)
                Hrefined_rest)
              as Hrefined_rest_larger;
            exists fuel, (refined_first :: refined_rest);
            cbn;
            rewrite Hrefined_first_larger, Hrefined_rest_larger;
            reflexivity
        end
    end.
Qed.
