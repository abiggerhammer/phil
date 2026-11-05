From Stdlib Require Import Arith.PeanoNat Lists.List.

From Phil.Surface Require Import
  GrammarAstAdditiveExpressionRefinedSpine
  GrammarAstAdditiveExpressionSpineTotality
  GrammarAstAdditiveSuffixRefinedSpineTotality
  GrammarAstMultiplicativeExpressionRefinedSpineFuelSupport
  GrammarAstUnaryExpressionRecursiveRefinedSpineFuelMonotonicity.

Import ListNotations.

(*
  Shared-fuel support for the completed additive-expression refinement.

  First, lift the existing recursive-unary and multiplicative-suffix
  monotonicity results through the completed multiplicative-expression
  normalizer. Then lift that result through one additive suffix and a suffix
  list. Finally, combine the finite derivation-driven suffix fuel witnesses with
  Nat.max so an enclosing additive expression can use one shared fuel value.

  Structural correspondence support only. This does not add evaluation
  semantics, change Grammar-v1, alter Haskell, or make broader production-parser
  soundness/completeness claims. It continues PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Lemma
  phase1_surface_normalize_multiplicative_expression_first_refined_spine_fuel_monotone :
  forall fuel larger expression refined,
    fuel <= larger ->
    phase1_surface_normalize_multiplicative_expression_first_refined_spine_fuel
      fuel expression = Some refined ->
    phase1_surface_normalize_multiplicative_expression_first_refined_spine_fuel
      larger expression = Some refined.
Proof.
  intros fuel larger expression refined Hle Hnormalize.
  unfold
    phase1_surface_normalize_multiplicative_expression_first_refined_spine_fuel
    in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_unary_expression_recursive_refined_tree_fuel
      fuel
      (phase1_multiplicative_expression_spine_first expression))
    as [first |] eqn:Hfirst; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  rewrite
    (phase1_surface_normalize_unary_expression_recursive_refined_tree_fuel_monotone
      fuel larger
      (phase1_multiplicative_expression_spine_first expression)
      first Hle Hfirst).
  reflexivity.
Qed.

Lemma
  phase1_surface_normalize_multiplicative_expression_first_refined_tree_fuel_monotone :
  forall fuel larger tree refined,
    fuel <= larger ->
    phase1_surface_normalize_multiplicative_expression_first_refined_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_normalize_multiplicative_expression_first_refined_tree_fuel
      larger tree = Some refined.
Proof.
  intros fuel larger tree refined Hle Hnormalize.
  unfold
    phase1_surface_normalize_multiplicative_expression_first_refined_tree_fuel
    in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_multiplicative_expression_spine tree)
    as [expression |] eqn:Hexpression; try discriminate Hnormalize.
  eapply
    phase1_surface_normalize_multiplicative_expression_first_refined_spine_fuel_monotone.
  - exact Hle.
  - exact Hnormalize.
Qed.

Lemma
  phase1_surface_normalize_multiplicative_expression_refined_spine_fuel_monotone :
  forall fuel larger expression refined,
    fuel <= larger ->
    phase1_surface_normalize_multiplicative_expression_refined_spine_fuel
      fuel expression = Some refined ->
    phase1_surface_normalize_multiplicative_expression_refined_spine_fuel
      larger expression = Some refined.
Proof.
  intros fuel larger expression refined Hle Hnormalize.
  unfold phase1_surface_normalize_multiplicative_expression_refined_spine_fuel
    in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_multiplicative_suffix_refined_spines_fuel
      fuel
      (phase1_multiplicative_expression_first_refined_spine_rest expression))
    as [rest |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  pose proof
    (phase1_surface_normalize_multiplicative_suffix_refined_spines_fuel_monotone
      fuel larger
      (phase1_multiplicative_expression_first_refined_spine_rest expression)
      rest Hle Hrest)
    as Hrest_larger.
  rewrite Hrest_larger.
  reflexivity.
Qed.

Lemma
  phase1_surface_normalize_multiplicative_expression_refined_tree_fuel_monotone :
  forall fuel larger tree refined,
    fuel <= larger ->
    phase1_surface_normalize_multiplicative_expression_refined_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_normalize_multiplicative_expression_refined_tree_fuel
      larger tree = Some refined.
Proof.
  intros fuel larger tree refined Hle Hnormalize.
  unfold phase1_surface_normalize_multiplicative_expression_refined_tree_fuel
    in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_multiplicative_expression_first_refined_tree_fuel
      fuel tree)
    as [expression |] eqn:Hexpression; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_multiplicative_expression_refined_spine_fuel
      fuel expression)
    as [result |] eqn:Hresult; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  pose proof
    (phase1_surface_normalize_multiplicative_expression_first_refined_tree_fuel_monotone
      fuel larger tree expression Hle Hexpression)
    as Hexpression_larger.
  rewrite Hexpression_larger.
  eapply
    phase1_surface_normalize_multiplicative_expression_refined_spine_fuel_monotone.
  - exact Hle.
  - exact Hresult.
Qed.

Lemma
  phase1_surface_normalize_additive_suffix_refined_spine_fuel_monotone :
  forall fuel larger suffix refined,
    fuel <= larger ->
    phase1_surface_normalize_additive_suffix_refined_spine_fuel
      fuel suffix = Some refined ->
    phase1_surface_normalize_additive_suffix_refined_spine_fuel
      larger suffix = Some refined.
Proof.
  intros fuel larger suffix refined Hle Hnormalize.
  unfold phase1_surface_normalize_additive_suffix_refined_spine_fuel
    in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_multiplicative_expression_refined_tree_fuel
      fuel
      (phase1_additive_suffix_spine_right suffix))
    as [right |] eqn:Hright; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  rewrite
    (phase1_surface_normalize_multiplicative_expression_refined_tree_fuel_monotone
      fuel larger
      (phase1_additive_suffix_spine_right suffix)
      right Hle Hright).
  reflexivity.
Qed.

Lemma
  phase1_surface_normalize_additive_suffix_refined_spines_fuel_monotone :
  forall fuel larger suffixes refined,
    fuel <= larger ->
    phase1_surface_normalize_additive_suffix_refined_spines_fuel
      fuel suffixes = Some refined ->
    phase1_surface_normalize_additive_suffix_refined_spines_fuel
      larger suffixes = Some refined.
Proof.
  intros fuel larger suffixes.
  induction suffixes as [|suffix rest IH];
    intros refined Hle Hnormalize.
  - cbn in Hnormalize |- *.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize |- *.
    destruct
      (phase1_surface_normalize_additive_suffix_refined_spine_fuel fuel suffix)
      as [refined_suffix |] eqn:Hsuffix; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_additive_suffix_refined_spines_fuel fuel rest)
      as [refined_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    pose proof
      (phase1_surface_normalize_additive_suffix_refined_spine_fuel_monotone
        fuel larger suffix refined_suffix Hle Hsuffix)
      as Hsuffix_larger.
    pose proof
      (IH refined_rest Hle Hrest)
      as Hrest_larger.
    rewrite Hsuffix_larger, Hrest_larger.
    reflexivity.
Qed.

Lemma
  phase1_surface_normalize_additive_suffix_refined_spines_fuel_total_from_repetition :
  forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body = phase1_surface_additive_suffix_expression_for_totality ->
    exists fuel suffixes refined,
      phase1_surface_normalize_additive_suffix_spines trees =
        Some suffixes /\
      phase1_surface_normalize_additive_suffix_refined_spines_fuel
        fuel suffixes = Some refined.
Proof.
  intros path body input rest trees Hderive.
  induction Hderive as
    [path body input
    |path body input middle rest tree trees
       Hitem Hprogress Hrest IHrest];
    intros Hbody_shape.
  - exists 0, [], [].
    split; reflexivity.
  - subst body.
    destruct
      (phase1_surface_normalize_additive_suffix_refined_spine_fuel_total_from_derivation
        _ _ _ tree Hitem)
      as [item_fuel [suffix [refined_suffix
        [Hsuffix [Hrefined_suffix Hsuffix_tree]]]]].
    destruct (IHrest eq_refl)
      as [rest_fuel [suffixes [refined_rest
        [Hsuffixes Hrefined_rest]]]].
    let fuel := constr:(Nat.max item_fuel rest_fuel) in
    pose proof
      (phase1_surface_normalize_additive_suffix_refined_spine_fuel_monotone
        item_fuel fuel suffix refined_suffix
        (Nat.le_max_l item_fuel rest_fuel)
        Hrefined_suffix)
      as Hrefined_suffix_larger.
    pose proof
      (phase1_surface_normalize_additive_suffix_refined_spines_fuel_monotone
        rest_fuel fuel suffixes refined_rest
        (Nat.le_max_r item_fuel rest_fuel)
        Hrefined_rest)
      as Hrefined_rest_larger.
    exists fuel, (suffix :: suffixes), (refined_suffix :: refined_rest).
    split.
    + cbn.
      rewrite Hsuffix, Hsuffixes.
      reflexivity.
    + cbn.
      rewrite Hrefined_suffix_larger, Hrefined_rest_larger.
      reflexivity.
Qed.
