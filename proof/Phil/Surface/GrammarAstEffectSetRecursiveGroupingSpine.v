From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstStaticReferenceSpine
  GrammarAstEffectSetSpine
  GrammarAstEffectExpressionExpressionFallbackBaseChoiceShiftRefinedSpine
  GrammarAstEffectSetExpressionFallbackBaseChoiceShiftRefinedSpine
  GrammarAstEffectExpressionRecursiveGroupingSpine.

Import ListNotations.
Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001.

  Every effect-set literal member is an actual recursive grouping effect
  carrier. The shallow shell retains braces, comma order, empty literals, and
  the enclosing literal/reference choice. The reference branch stores the
  existing static-reference carrier directly, with no duplicate raw payload.

  Raw conversion normalizes every effect tree. The legacy adapter traverses
  every existing full effect carrier and directly copies the reference branch.
  Neither entry point requires caller-supplied fuel. Boundaries inherited from
  the effect carrier remain; no enclosing requirement or Haskell binding is
  established by this module.
*)

Fixpoint phase1_surface_normalize_effect_set_recursive_grouping_values
  (effects : list ParseTree)
  : option (list Phase1SurfaceEffectExpressionRecursiveGroupingSpine) :=
  match effects with
  | [] => Some []
  | effect :: rest =>
      match
        phase1_surface_normalize_effect_expression_recursive_grouping_tree effect,
        phase1_surface_normalize_effect_set_recursive_grouping_values rest
      with
      | Some refined, Some refined_rest => Some (refined :: refined_rest)
      | _, _ => None
      end
  end.

Theorem phase1_surface_normalize_effect_set_recursive_grouping_values_round_trip :
  forall effects refined,
    phase1_surface_normalize_effect_set_recursive_grouping_values effects =
      Some refined ->
    map phase1_surface_effect_expression_recursive_grouping_spine_tree refined =
      effects.
Proof.
  induction effects as [|effect rest IH]; intros refined Hnormalize.
  - inversion Hnormalize; reflexivity.
  - cbn [phase1_surface_normalize_effect_set_recursive_grouping_values]
      in Hnormalize.
    destruct
      (phase1_surface_normalize_effect_expression_recursive_grouping_tree effect)
      as [actual |] eqn:Heffect; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_effect_set_recursive_grouping_values rest)
      as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn [map].
    rewrite
      (phase1_surface_normalize_effect_expression_recursive_grouping_tree_round_trip
        effect actual Heffect),
      (IH actual_rest eq_refl).
    reflexivity.
Qed.

Fixpoint phase1_surface_refine_effect_set_recursive_grouping_values
  (effects :
    list Phase1SurfaceEffectExpressionExpressionFallbackBaseChoiceShiftRefinedSpine)
  : option (list Phase1SurfaceEffectExpressionRecursiveGroupingSpine) :=
  match effects with
  | [] => Some []
  | effect :: rest =>
      match
        phase1_surface_refine_effect_expression_recursive_grouping effect,
        phase1_surface_refine_effect_set_recursive_grouping_values rest
      with
      | Some refined, Some refined_rest => Some (refined :: refined_rest)
      | _, _ => None
      end
  end.

Theorem phase1_surface_refine_effect_set_recursive_grouping_values_round_trip :
  forall effects refined,
    phase1_surface_refine_effect_set_recursive_grouping_values effects =
      Some refined ->
    map phase1_surface_effect_expression_recursive_grouping_spine_tree refined =
      map
        phase1_surface_effect_expression_expression_fallback_base_choice_shift_refined_spine_tree
        effects.
Proof.
  induction effects as [|effect rest IH]; intros refined Hnormalize.
  - inversion Hnormalize; reflexivity.
  - cbn [phase1_surface_refine_effect_set_recursive_grouping_values]
      in Hnormalize.
    destruct (phase1_surface_refine_effect_expression_recursive_grouping effect)
      as [actual |] eqn:Heffect; try discriminate Hnormalize.
    destruct (phase1_surface_refine_effect_set_recursive_grouping_values rest)
      as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn [map].
    rewrite
      (phase1_surface_refine_effect_expression_recursive_grouping_round_trip
        effect actual Heffect),
      (IH actual_rest eq_refl).
    reflexivity.
Qed.

Record Phase1SurfaceEffectSetLiteralRecursiveGroupingSpine : Type := {
  phase1_effect_set_literal_recursive_grouping_spine_effects :
    list Phase1SurfaceEffectExpressionRecursiveGroupingSpine
}.

Definition phase1_surface_effect_set_literal_recursive_grouping_spine_base
  (literal : Phase1SurfaceEffectSetLiteralRecursiveGroupingSpine)
  : Phase1SurfaceEffectSetLiteralSpine :=
  {| phase1_effect_set_literal_spine_effects :=
       map phase1_surface_effect_expression_recursive_grouping_spine_tree
         (phase1_effect_set_literal_recursive_grouping_spine_effects literal) |}.

Definition phase1_surface_effect_set_literal_recursive_grouping_spine_tree
  (literal : Phase1SurfaceEffectSetLiteralRecursiveGroupingSpine) : ParseTree :=
  phase1_surface_effect_set_literal_spine_tree
    (phase1_surface_effect_set_literal_recursive_grouping_spine_base literal).

Definition phase1_surface_normalize_effect_set_literal_recursive_grouping_spine
  (previous : Phase1SurfaceEffectSetLiteralSpine)
  : option Phase1SurfaceEffectSetLiteralRecursiveGroupingSpine :=
  match phase1_surface_normalize_effect_set_recursive_grouping_values
    (phase1_effect_set_literal_spine_effects previous) with
  | Some refined =>
      Some {| phase1_effect_set_literal_recursive_grouping_spine_effects :=
                refined |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_effect_set_literal_recursive_grouping_spine_round_trip :
  forall previous refined,
    phase1_surface_normalize_effect_set_literal_recursive_grouping_spine previous =
      Some refined ->
    phase1_surface_effect_set_literal_recursive_grouping_spine_base refined =
      previous.
Proof.
  intros [effects] refined Hnormalize.
  unfold phase1_surface_normalize_effect_set_literal_recursive_grouping_spine
    in Hnormalize.
  cbn [phase1_effect_set_literal_spine_effects] in Hnormalize.
  destruct (phase1_surface_normalize_effect_set_recursive_grouping_values effects)
    as [actual |] eqn:Heffects; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  unfold phase1_surface_effect_set_literal_recursive_grouping_spine_base.
  cbn [phase1_effect_set_literal_recursive_grouping_spine_effects].
  rewrite
    (phase1_surface_normalize_effect_set_recursive_grouping_values_round_trip
      effects actual Heffects).
  reflexivity.
Qed.

Theorem
  phase1_surface_normalize_effect_set_literal_recursive_grouping_spine_tree_round_trip :
  forall previous refined,
    phase1_surface_normalize_effect_set_literal_recursive_grouping_spine previous =
      Some refined ->
    phase1_surface_effect_set_literal_recursive_grouping_spine_tree refined =
      phase1_surface_effect_set_literal_spine_tree previous.
Proof.
  intros previous refined Hnormalize.
  unfold phase1_surface_effect_set_literal_recursive_grouping_spine_tree.
  rewrite
    (phase1_surface_normalize_effect_set_literal_recursive_grouping_spine_round_trip
      previous refined Hnormalize).
  reflexivity.
Qed.

Definition phase1_surface_normalize_effect_set_literal_recursive_grouping_tree
  (tree : ParseTree) : option Phase1SurfaceEffectSetLiteralRecursiveGroupingSpine :=
  match phase1_surface_normalize_effect_set_literal_spine tree with
  | Some previous =>
      phase1_surface_normalize_effect_set_literal_recursive_grouping_spine previous
  | None => None
  end.

Theorem
  phase1_surface_normalize_effect_set_literal_recursive_grouping_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_effect_set_literal_recursive_grouping_tree tree =
      Some refined ->
    phase1_surface_effect_set_literal_recursive_grouping_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_effect_set_literal_recursive_grouping_tree
    in Hnormalize.
  destruct (phase1_surface_normalize_effect_set_literal_spine tree)
    as [previous |] eqn:Hprevious; try discriminate Hnormalize.
  transitivity (phase1_surface_effect_set_literal_spine_tree previous).
  - eapply
      phase1_surface_normalize_effect_set_literal_recursive_grouping_spine_tree_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_effect_set_literal_spine_round_trip.
    exact Hprevious.
Qed.

Lemma phase1_surface_effect_set_recursive_grouping_legacy_entries_tree :
  forall effects,
    phase1_surface_effect_set_entries_tree
      (map
        phase1_surface_effect_expression_expression_fallback_base_choice_shift_refined_spine_tree
        effects) =
    phase1_surface_effect_expression_expression_fallback_base_choice_shift_refined_entries_tree
      effects.
Proof.
  intros [|first rest].
  - reflexivity.
  - cbn [map phase1_surface_effect_set_entries_tree
      phase1_surface_effect_expression_tree
      phase1_surface_effect_expression_expression_fallback_base_choice_shift_refined_entries_tree].
    unfold phase1_surface_effect_set_suffix_tree,
      phase1_surface_effect_expression_tree,
      phase1_surface_effect_expression_expression_fallback_base_choice_shift_refined_suffix_tree.
    rewrite map_map.
    reflexivity.
Qed.

Lemma phase1_surface_effect_set_recursive_grouping_legacy_literal_tree :
  forall previous,
    phase1_surface_effect_set_literal_spine_tree
      {| phase1_effect_set_literal_spine_effects :=
           map
             phase1_surface_effect_expression_expression_fallback_base_choice_shift_refined_spine_tree
             (phase1_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_effects
               previous) |} =
    phase1_surface_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_tree
      previous.
Proof.
  intros [effects].
  unfold phase1_surface_effect_set_literal_spine_tree,
    phase1_surface_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_tree.
  cbn [phase1_effect_set_literal_spine_effects
    phase1_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_effects].
  rewrite phase1_surface_effect_set_recursive_grouping_legacy_entries_tree.
  reflexivity.
Qed.

Definition phase1_surface_refine_effect_set_literal_recursive_grouping
  (previous :
    Phase1SurfaceEffectSetExpressionFallbackBaseChoiceShiftRefinedLiteralSpine)
  : option Phase1SurfaceEffectSetLiteralRecursiveGroupingSpine :=
  match phase1_surface_refine_effect_set_recursive_grouping_values
    (phase1_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_effects
      previous) with
  | Some refined =>
      Some {| phase1_effect_set_literal_recursive_grouping_spine_effects :=
                refined |}
  | None => None
  end.

Theorem phase1_surface_refine_effect_set_literal_recursive_grouping_round_trip :
  forall previous refined,
    phase1_surface_refine_effect_set_literal_recursive_grouping previous =
      Some refined ->
    phase1_surface_effect_set_literal_recursive_grouping_spine_tree refined =
      phase1_surface_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_tree
        previous.
Proof.
  intros [effects] refined Hnormalize.
  unfold phase1_surface_refine_effect_set_literal_recursive_grouping in Hnormalize.
  cbn [phase1_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_effects]
    in Hnormalize.
  destruct (phase1_surface_refine_effect_set_recursive_grouping_values effects)
    as [actual |] eqn:Heffects; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  unfold phase1_surface_effect_set_literal_recursive_grouping_spine_tree,
    phase1_surface_effect_set_literal_recursive_grouping_spine_base.
  cbn [phase1_effect_set_literal_recursive_grouping_spine_effects].
  rewrite
    (phase1_surface_refine_effect_set_recursive_grouping_values_round_trip
      effects actual Heffects).
  exact
    (phase1_surface_effect_set_recursive_grouping_legacy_literal_tree
      {| phase1_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_effects :=
           effects |}).
Qed.

Inductive Phase1SurfaceEffectSetRecursiveGroupingSpine : Type :=
| Phase1EffectSetGroupingLiteral
    (literal : Phase1SurfaceEffectSetLiteralRecursiveGroupingSpine)
| Phase1EffectSetGroupingReference
    (reference : Phase1SurfaceStaticReferenceSpine).

Definition phase1_surface_effect_set_recursive_grouping_spine_base
  (effects : Phase1SurfaceEffectSetRecursiveGroupingSpine)
  : Phase1SurfaceEffectSetSpine :=
  match effects with
  | Phase1EffectSetGroupingLiteral literal =>
      Phase1EffectSetLiteral
        (phase1_surface_effect_set_literal_recursive_grouping_spine_base literal)
  | Phase1EffectSetGroupingReference reference =>
      Phase1EffectSetReference reference
  end.

Definition phase1_surface_effect_set_recursive_grouping_spine_tree
  (effects : Phase1SurfaceEffectSetRecursiveGroupingSpine) : ParseTree :=
  phase1_surface_effect_set_spine_tree
    (phase1_surface_effect_set_recursive_grouping_spine_base effects).

Definition phase1_surface_normalize_effect_set_recursive_grouping_spine
  (previous : Phase1SurfaceEffectSetSpine)
  : option Phase1SurfaceEffectSetRecursiveGroupingSpine :=
  match previous with
  | Phase1EffectSetLiteral literal =>
      match
        phase1_surface_normalize_effect_set_literal_recursive_grouping_spine literal
      with
      | Some refined => Some (Phase1EffectSetGroupingLiteral refined)
      | None => None
      end
  | Phase1EffectSetReference reference =>
      Some (Phase1EffectSetGroupingReference reference)
  end.

Theorem phase1_surface_normalize_effect_set_recursive_grouping_spine_round_trip :
  forall previous refined,
    phase1_surface_normalize_effect_set_recursive_grouping_spine previous =
      Some refined ->
    phase1_surface_effect_set_recursive_grouping_spine_base refined = previous.
Proof.
  intros [literal |reference] refined Hnormalize.
  - cbn [phase1_surface_normalize_effect_set_recursive_grouping_spine]
      in Hnormalize.
    destruct
      (phase1_surface_normalize_effect_set_literal_recursive_grouping_spine literal)
      as [actual |] eqn:Hliteral; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn [phase1_surface_effect_set_recursive_grouping_spine_base].
    rewrite
      (phase1_surface_normalize_effect_set_literal_recursive_grouping_spine_round_trip
        literal actual Hliteral).
    reflexivity.
  - inversion Hnormalize; reflexivity.
Qed.

Theorem
  phase1_surface_normalize_effect_set_recursive_grouping_spine_tree_round_trip :
  forall previous refined,
    phase1_surface_normalize_effect_set_recursive_grouping_spine previous =
      Some refined ->
    phase1_surface_effect_set_recursive_grouping_spine_tree refined =
      phase1_surface_effect_set_spine_tree previous.
Proof.
  intros previous refined Hnormalize.
  unfold phase1_surface_effect_set_recursive_grouping_spine_tree.
  rewrite
    (phase1_surface_normalize_effect_set_recursive_grouping_spine_round_trip
      previous refined Hnormalize).
  reflexivity.
Qed.

Theorem
  phase1_surface_normalize_effect_set_recursive_grouping_spine_reference_preserved :
  forall reference,
    phase1_surface_normalize_effect_set_recursive_grouping_spine
      (Phase1EffectSetReference reference) =
    Some (Phase1EffectSetGroupingReference reference).
Proof.
  reflexivity.
Qed.

Definition phase1_surface_normalize_effect_set_recursive_grouping_tree
  (tree : ParseTree) : option Phase1SurfaceEffectSetRecursiveGroupingSpine :=
  match phase1_surface_normalize_effect_set_spine tree with
  | Some previous =>
      phase1_surface_normalize_effect_set_recursive_grouping_spine previous
  | None => None
  end.

Theorem phase1_surface_normalize_effect_set_recursive_grouping_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_effect_set_recursive_grouping_tree tree =
      Some refined ->
    phase1_surface_effect_set_recursive_grouping_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_effect_set_recursive_grouping_tree in Hnormalize.
  destruct (phase1_surface_normalize_effect_set_spine tree)
    as [previous |] eqn:Hprevious; try discriminate Hnormalize.
  transitivity (phase1_surface_effect_set_spine_tree previous).
  - eapply
      phase1_surface_normalize_effect_set_recursive_grouping_spine_tree_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_effect_set_spine_round_trip.
    exact Hprevious.
Qed.

Definition phase1_surface_refine_effect_set_recursive_grouping
  (previous : Phase1SurfaceEffectSetExpressionFallbackBaseChoiceShiftRefinedSpine)
  : option Phase1SurfaceEffectSetRecursiveGroupingSpine :=
  match previous with
  | Phase1EffectSetExpressionFallbackBaseChoiceShiftRefinedLiteral literal =>
      match phase1_surface_refine_effect_set_literal_recursive_grouping literal with
      | Some refined => Some (Phase1EffectSetGroupingLiteral refined)
      | None => None
      end
  | Phase1EffectSetExpressionFallbackBaseChoiceShiftRefinedReference reference =>
      Some (Phase1EffectSetGroupingReference reference)
  end.

Theorem phase1_surface_refine_effect_set_recursive_grouping_round_trip :
  forall previous refined,
    phase1_surface_refine_effect_set_recursive_grouping previous = Some refined ->
    phase1_surface_effect_set_recursive_grouping_spine_tree refined =
      phase1_surface_effect_set_expression_fallback_base_choice_shift_refined_spine_tree
        previous.
Proof.
  intros [literal |reference] refined Hnormalize.
  - cbn [phase1_surface_refine_effect_set_recursive_grouping] in Hnormalize.
    destruct (phase1_surface_refine_effect_set_literal_recursive_grouping literal)
      as [actual |] eqn:Hliteral; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    change
      (PTNonterminal "effect_set_expression"
        (PTAlternative 0
          (phase1_surface_effect_set_literal_recursive_grouping_spine_tree actual)) =
       PTNonterminal "effect_set_expression"
        (PTAlternative 0
          (phase1_surface_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_tree
            literal))).
    rewrite
      (phase1_surface_refine_effect_set_literal_recursive_grouping_round_trip
        literal actual Hliteral).
    reflexivity.
  - inversion Hnormalize; reflexivity.
Qed.

Theorem phase1_surface_refine_effect_set_recursive_grouping_reference_preserved :
  forall reference,
    phase1_surface_refine_effect_set_recursive_grouping
      (Phase1EffectSetExpressionFallbackBaseChoiceShiftRefinedReference reference) =
    Some (Phase1EffectSetGroupingReference reference).
Proof.
  reflexivity.
Qed.
