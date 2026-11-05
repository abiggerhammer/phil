From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceTotality
  GrammarAstRecordGenericRequirementExpressionFallbackBaseChoiceShiftRefinedTotality
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Derivation-driven fuel totality for the data_decl lift of the shift-refined
  generic_requirements carrier.

  The base declaration totality proof first exposes the canonical
  fallback/base-choice data spine. Replaying the data derivation isolates its
  optional generic_requirements field, where the completed shift-refined
  generic_requirements totality proof supplies a finite fuel witness.

  Structural Rocq surface correspondence only. This does not change Grammar-v1,
  Haskell/runtime behavior, evaluation semantics, or make broader parser
  soundness/completeness claims. It continues PHIL-SURFACE-GRAMMAR-CORR-001
  after #1497.
*)

Theorem
  phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "data_decl")
      input rest tree ->
    exists fuel refined,
      phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel
        fuel tree = Some refined /\
      phase1_surface_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_tree
        refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_tree_total_from_derivation
      path input rest tree Hderive)
    as [base [Hbase Hbase_round_trip]].
  destruct base as
    [name generic_params mode requirements first_variant rest_variants].
  cbn in Hbase, Hbase_round_trip.
  rewrite <- Hbase_round_trip in Hderive.
  unfold
    phase1_surface_data_generic_requirement_expression_fallback_base_choice_spine_tree
    in Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "data_decl"
      input rest
      (PTNonterminal "data_decl"
        (PTSequence
          [ PTLiteral "data";
            phase1_surface_identifier_tree name;
            phase1_surface_optional_generic_params_kind_type_tree generic_params;
            phase1_surface_optional_mode_tree mode;
            phase1_surface_optional_generic_requirements_expression_fallback_base_choice_tree
              requirements;
            PTLiteral "=";
            phase1_surface_record_field_type_variant_spine_tree first_variant;
            PTRepetition
              (map phase1_surface_record_field_type_data_suffix_tree
                rest_variants);
            PTLiteral ";"
          ]))
      Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_data_decl_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  inversion Htree; subst subtree.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "data_decl"))
      [ ELiteral "data";
        ENonterminal "identifier";
        EOptional (ENonterminal "generic_params");
        EOptional
          (ESequence [ELiteral "mode"; ENonterminal "structural_mode"]);
        EOptional (ENonterminal "generic_requirements");
        ELiteral "=";
        ENonterminal "variant_decl";
        ERepetition phase1_surface_data_variant_suffix_expression_for_totality;
        ELiteral ";"
      ]
      input rest
      (PTSequence
        [ PTLiteral "data";
          phase1_surface_identifier_tree name;
          phase1_surface_optional_generic_params_kind_type_tree generic_params;
          phase1_surface_optional_mode_tree mode;
          phase1_surface_optional_generic_requirements_expression_fallback_base_choice_tree
            requirements;
          PTLiteral "=";
          phase1_surface_record_field_type_variant_spine_tree first_variant;
          PTRepetition
            (map phase1_surface_record_field_type_data_suffix_tree
              rest_variants);
          PTLiteral ";"
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
  | Hrequirements : Derives phase1_surface_rules _
      (EOptional (ENonterminal "generic_requirements"))
      _ _
      (phase1_surface_optional_generic_requirements_expression_fallback_base_choice_tree
        requirements)
      |- _ =>
      destruct
        (phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_fuel_total_from_spine_derivation
          requirements _ _ _ Hrequirements)
        as [fuel [refined_requirements Hrefined_requirements]];
      let refined := constr:(
        {| phase1_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_name :=
             name;
           phase1_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_generic_params :=
             generic_params;
           phase1_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_mode :=
             mode;
           phase1_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_requirements :=
             refined_requirements;
           phase1_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_first_variant :=
             first_variant;
           phase1_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_rest_variants :=
             rest_variants |}) in
      assert (Hnormalize :
        phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel
          fuel tree = Some refined);
      [ unfold
          phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel;
        rewrite Hbase;
        unfold
          phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel;
        cbn;
        rewrite Hrefined_requirements;
        reflexivity
      | exists fuel, refined;
        split;
        [ exact Hnormalize
        | eapply
            phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel_round_trip;
          exact Hnormalize ] ]
  end.
Qed.
