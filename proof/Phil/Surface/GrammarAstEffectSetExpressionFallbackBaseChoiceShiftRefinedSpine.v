From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstEffectSetExpressionFallbackBaseChoiceSpine
  GrammarAstEffectExpressionExpressionFallbackBaseChoiceShiftRefinedSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Lift the completed refined shift-expression effect_expression carrier through
  effect-set literals and the enclosing effect_set_expression choice.

  Literal member order and punctuation remain exact. One explicit fuel value is
  threaded across the finite literal member list; the static-reference branch
  is unchanged.

  Structural Rocq surface correspondence only. This continues
  PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Fixpoint
  phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_values_fuel
  (fuel : nat)
  (effects : list Phase1SurfaceEffectExpressionExpressionFallbackBaseChoiceSpine)
  : option
      (list
        Phase1SurfaceEffectExpressionExpressionFallbackBaseChoiceShiftRefinedSpine) :=
  match effects with
  | [] => Some []
  | effect :: rest =>
      match
        phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_spine_fuel
          fuel effect,
        phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_values_fuel
          fuel rest
      with
      | Some refined, Some refined_rest =>
          Some (refined :: refined_rest)
      | _, _ => None
      end
  end.

Theorem
  phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_values_fuel_round_trip :
  forall fuel effects refined,
    phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_values_fuel
      fuel effects = Some refined ->
    map
      phase1_surface_effect_expression_expression_fallback_base_choice_shift_refined_spine_tree
      refined =
    map
      phase1_surface_effect_expression_expression_fallback_base_choice_spine_tree
      effects.
Proof.
  intros fuel effects.
  induction effects as [|effect rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_spine_fuel
        fuel effect)
      as [actual |] eqn:Heffect; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_values_fuel
        fuel rest)
      as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    f_equal.
    + eapply
        phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_spine_fuel_round_trip.
      exact Heffect.
    + eapply IH.
      exact Hrest.
Qed.

Definition
  phase1_surface_effect_expression_expression_fallback_base_choice_shift_refined_suffix_tree
  (effect :
    Phase1SurfaceEffectExpressionExpressionFallbackBaseChoiceShiftRefinedSpine)
  : ParseTree :=
  PTSequence
    [ PTLiteral ",";
      phase1_surface_effect_expression_expression_fallback_base_choice_shift_refined_spine_tree
        effect
    ].

Definition
  phase1_surface_effect_expression_expression_fallback_base_choice_shift_refined_entries_tree
  (effects :
    list
      Phase1SurfaceEffectExpressionExpressionFallbackBaseChoiceShiftRefinedSpine)
  : ParseTree :=
  match effects with
  | [] => PTOptionalNone
  | first :: rest =>
      PTOptionalSome
        (PTSequence
          [ phase1_surface_effect_expression_expression_fallback_base_choice_shift_refined_spine_tree
              first;
            PTRepetition
              (map
                phase1_surface_effect_expression_expression_fallback_base_choice_shift_refined_suffix_tree
                rest)
          ])
  end.

Theorem
  phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_values_entries_fuel_round_trip :
  forall fuel effects refined,
    phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_values_fuel
      fuel effects = Some refined ->
    phase1_surface_effect_expression_expression_fallback_base_choice_shift_refined_entries_tree
      refined =
    phase1_surface_effect_expression_expression_fallback_base_choice_entries_tree
      effects.
Proof.
  intros fuel effects.
  induction effects as [|effect rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_spine_fuel
        fuel effect)
      as [actual |] eqn:Heffect; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_values_fuel
        fuel rest)
      as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_spine_fuel_round_trip
        fuel effect actual Heffect).
    pose proof
      (phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_values_fuel_round_trip
        fuel rest actual_rest Hrest) as Hrest_round_trip.
    unfold
      phase1_surface_effect_expression_expression_fallback_base_choice_shift_refined_suffix_tree.
    unfold
      phase1_surface_effect_expression_expression_fallback_base_choice_suffix_tree.
    cbn in Hrest_round_trip |- *.
    rewrite Hrest_round_trip.
    reflexivity.
Qed.

Record
  Phase1SurfaceEffectSetExpressionFallbackBaseChoiceShiftRefinedLiteralSpine
  : Type := {
  phase1_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_effects :
    list
      Phase1SurfaceEffectExpressionExpressionFallbackBaseChoiceShiftRefinedSpine
}.

Definition
  phase1_surface_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_tree
  (literal :
    Phase1SurfaceEffectSetExpressionFallbackBaseChoiceShiftRefinedLiteralSpine)
  : ParseTree :=
  PTNonterminal "effect_set_literal"
    (PTSequence
      [ PTLiteral "{";
        phase1_surface_effect_expression_expression_fallback_base_choice_shift_refined_entries_tree
          (phase1_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_effects
            literal);
        PTLiteral "}"
      ]).

Definition
  phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_fuel
  (fuel : nat)
  (literal : Phase1SurfaceEffectSetExpressionFallbackBaseChoiceLiteralSpine)
  : option
      Phase1SurfaceEffectSetExpressionFallbackBaseChoiceShiftRefinedLiteralSpine :=
  match
    phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_values_fuel
      fuel
      (phase1_effect_set_expression_fallback_base_choice_literal_spine_effects
        literal)
  with
  | Some effects =>
      Some
        {| phase1_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_effects :=
             effects |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_fuel_round_trip :
  forall fuel literal refined,
    phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_fuel
      fuel literal = Some refined ->
    phase1_surface_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_tree
      refined =
    phase1_surface_effect_set_expression_fallback_base_choice_literal_spine_tree
      literal.
Proof.
  intros fuel [effects] refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_values_fuel
      fuel effects)
    as [actual |] eqn:Heffects; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_values_entries_fuel_round_trip
      fuel effects actual Heffects).
  reflexivity.
Qed.

Inductive
  Phase1SurfaceEffectSetExpressionFallbackBaseChoiceShiftRefinedSpine
  : Type :=
| Phase1EffectSetExpressionFallbackBaseChoiceShiftRefinedLiteral
    (literal :
      Phase1SurfaceEffectSetExpressionFallbackBaseChoiceShiftRefinedLiteralSpine)
| Phase1EffectSetExpressionFallbackBaseChoiceShiftRefinedReference
    (reference : Phase1SurfaceStaticReferenceSpine).

Definition
  phase1_surface_effect_set_expression_fallback_base_choice_shift_refined_spine_tree
  (effects : Phase1SurfaceEffectSetExpressionFallbackBaseChoiceShiftRefinedSpine)
  : ParseTree :=
  match effects with
  | Phase1EffectSetExpressionFallbackBaseChoiceShiftRefinedLiteral literal =>
      PTNonterminal "effect_set_expression"
        (PTAlternative 0
          (phase1_surface_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_tree
            literal))
  | Phase1EffectSetExpressionFallbackBaseChoiceShiftRefinedReference reference =>
      PTNonterminal "effect_set_expression"
        (PTAlternative 1
          (phase1_surface_static_reference_spine_tree reference))
  end.

Definition
  phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_spine_fuel
  (fuel : nat)
  (effects : Phase1SurfaceEffectSetExpressionFallbackBaseChoiceSpine)
  : option Phase1SurfaceEffectSetExpressionFallbackBaseChoiceShiftRefinedSpine :=
  match effects with
  | Phase1EffectSetExpressionFallbackBaseChoiceLiteral literal =>
      match
        phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_fuel
          fuel literal
      with
      | Some refined =>
          Some
            (Phase1EffectSetExpressionFallbackBaseChoiceShiftRefinedLiteral
              refined)
      | None => None
      end
  | Phase1EffectSetExpressionFallbackBaseChoiceReference reference =>
      Some
        (Phase1EffectSetExpressionFallbackBaseChoiceShiftRefinedReference
          reference)
  end.

Theorem
  phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_spine_fuel_round_trip :
  forall fuel effects refined,
    phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_spine_fuel
      fuel effects = Some refined ->
    phase1_surface_effect_set_expression_fallback_base_choice_shift_refined_spine_tree
      refined =
    phase1_surface_effect_set_expression_fallback_base_choice_spine_tree effects.
Proof.
  intros fuel effects refined Hnormalize.
  destruct effects as [literal | reference].
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_fuel
        fuel literal)
      as [actual |] eqn:Hliteral; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_fuel_round_trip
        fuel literal actual Hliteral).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Definition
  phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_tree_fuel
  (fuel : nat)
  (tree : ParseTree)
  : option Phase1SurfaceEffectSetExpressionFallbackBaseChoiceShiftRefinedSpine :=
  match
    phase1_surface_normalize_effect_set_expression_fallback_base_choice_tree tree
  with
  | Some effects =>
      phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_spine_fuel
        fuel effects
  | None => None
  end.

Theorem
  phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_tree_fuel_round_trip :
  forall fuel tree refined,
    phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_effect_set_expression_fallback_base_choice_shift_refined_spine_tree
      refined = tree.
Proof.
  intros fuel tree refined Hnormalize.
  unfold
    phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_tree_fuel
    in Hnormalize.
  destruct
    (phase1_surface_normalize_effect_set_expression_fallback_base_choice_tree tree)
    as [effects |] eqn:Heffects; try discriminate Hnormalize.
  transitivity
    (phase1_surface_effect_set_expression_fallback_base_choice_spine_tree
      effects).
  - eapply
      phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_spine_fuel_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_effect_set_expression_fallback_base_choice_tree_round_trip.
    exact Heffects.
Qed.
