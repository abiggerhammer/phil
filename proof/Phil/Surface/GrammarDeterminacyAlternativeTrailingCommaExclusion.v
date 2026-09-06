From Stdlib Require Import Bool.Bool Lists.List Strings.String.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDeterminacySimpleResolvers
  GrammarDeterminacyPredictiveOracle
  GrammarDeterminacyDerivationPathSoundness
  GrammarDeterminacyPathSuffixReflection.

Import ListNotations.
Open Scope string_scope.

(*
  Exclude the five trailing-comma repetition resolver sites from alternative
  nodes.  This is the remaining path-shape seam before the final alternative
  resolver dispatch can treat every certified-resolver Some result as an
  alternative-root decision.

  #779 reflects boolean suffix tests into concrete list decompositions.  Once
  a valid phase-1 path is decomposed at any of the five generated suffixes, the
  generated grammar computes the expression at that suffix to a repetition
  node, never an alternative.
*)

Lemma case_pattern_comma_repeat_suffix_not_alternative :
  forall prefix items,
    phase1_surface_expression_path_context
      (List.app prefix case_pattern_comma_repeat_suffix)
      (EAlternative items) ->
    False.
Proof.
  intros prefix items Hpath.
  unfold phase1_surface_expression_path_context,
    phase1_surface_expression_at_path in Hpath.
  rewrite expression_at_path_app in Hpath.
  destruct
    (expression_at_path
      phase1_surface_rules phase1_surface_root_expression prefix)
    as [middle |] eqn:Hmiddle.
  - destruct middle as
      [literal | class_name | name | sequence | alternatives | body | body];
      try (vm_compute in Hpath; discriminate Hpath).
    destruct (String.eqb "case_pattern" name) eqn:Hname;
      try discriminate Hpath.
    apply String.eqb_eq in Hname.
    subst name.
    vm_compute in Hpath.
    discriminate Hpath.
  - discriminate Hpath.
Qed.

Lemma construct_expression_comma_repeat_suffix_not_alternative :
  forall prefix items,
    phase1_surface_expression_path_context
      (List.app prefix construct_expression_comma_repeat_suffix)
      (EAlternative items) ->
    False.
Proof.
  intros prefix items Hpath.
  unfold phase1_surface_expression_path_context,
    phase1_surface_expression_at_path in Hpath.
  rewrite expression_at_path_app in Hpath.
  destruct
    (expression_at_path
      phase1_surface_rules phase1_surface_root_expression prefix)
    as [middle |] eqn:Hmiddle.
  - destruct middle as
      [literal | class_name | name | sequence | alternatives | body | body];
      try (vm_compute in Hpath; discriminate Hpath).
    destruct (String.eqb "construct_expression" name) eqn:Hname;
      try discriminate Hpath.
    apply String.eqb_eq in Hname.
    subst name.
    vm_compute in Hpath.
    discriminate Hpath.
  - discriminate Hpath.
Qed.

Lemma record_decl_comma_repeat_suffix_not_alternative :
  forall prefix items,
    phase1_surface_expression_path_context
      (List.app prefix record_decl_comma_repeat_suffix)
      (EAlternative items) ->
    False.
Proof.
  intros prefix items Hpath.
  unfold phase1_surface_expression_path_context,
    phase1_surface_expression_at_path in Hpath.
  rewrite expression_at_path_app in Hpath.
  destruct
    (expression_at_path
      phase1_surface_rules phase1_surface_root_expression prefix)
    as [middle |] eqn:Hmiddle.
  - destruct middle as
      [literal | class_name | name | sequence | alternatives | body | body];
      try (vm_compute in Hpath; discriminate Hpath).
    destruct (String.eqb "record_decl" name) eqn:Hname;
      try discriminate Hpath.
    apply String.eqb_eq in Hname.
    subst name.
    vm_compute in Hpath.
    discriminate Hpath.
  - discriminate Hpath.
Qed.

Lemma record_pattern_comma_repeat_suffix_not_alternative :
  forall prefix items,
    phase1_surface_expression_path_context
      (List.app prefix record_pattern_comma_repeat_suffix)
      (EAlternative items) ->
    False.
Proof.
  intros prefix items Hpath.
  unfold phase1_surface_expression_path_context,
    phase1_surface_expression_at_path in Hpath.
  rewrite expression_at_path_app in Hpath.
  destruct
    (expression_at_path
      phase1_surface_rules phase1_surface_root_expression prefix)
    as [middle |] eqn:Hmiddle.
  - destruct middle as
      [literal | class_name | name | sequence | alternatives | body | body];
      try (vm_compute in Hpath; discriminate Hpath).
    destruct (String.eqb "record_pattern" name) eqn:Hname;
      try discriminate Hpath.
    apply String.eqb_eq in Hname.
    subst name.
    vm_compute in Hpath.
    discriminate Hpath.
  - discriminate Hpath.
Qed.

Lemma variant_payload_comma_repeat_suffix_not_alternative :
  forall prefix items,
    phase1_surface_expression_path_context
      (List.app prefix variant_payload_comma_repeat_suffix)
      (EAlternative items) ->
    False.
Proof.
  intros prefix items Hpath.
  unfold phase1_surface_expression_path_context,
    phase1_surface_expression_at_path in Hpath.
  rewrite expression_at_path_app in Hpath.
  destruct
    (expression_at_path
      phase1_surface_rules phase1_surface_root_expression prefix)
    as [middle |] eqn:Hmiddle.
  - destruct middle as
      [literal | class_name | name | sequence | alternatives | body | body];
      try (vm_compute in Hpath; discriminate Hpath).
    destruct (String.eqb "variant_payload" name) eqn:Hname;
      try discriminate Hpath.
    apply String.eqb_eq in Hname.
    subst name.
    vm_compute in Hpath.
    discriminate Hpath.
  - discriminate Hpath.
Qed.

Theorem phase1_surface_alternative_excludes_trailing_comma_path :
  forall path items,
    phase1_surface_expression_path_context path (EAlternative items) ->
    trailing_comma_repeat_pathb path = false.
Proof.
  intros path items Hpath.
  destruct (trailing_comma_repeat_pathb path) eqn:Htrail.
  - exfalso.
    unfold trailing_comma_repeat_pathb in Htrail.
    apply orb_true_iff in Htrail.
    destruct Htrail as [Hcase | Hrest].
    + apply path_has_suffixb_true_shape in Hcase.
      destruct Hcase as [prefix Hshape].
      subst path.
      eapply case_pattern_comma_repeat_suffix_not_alternative.
      exact Hpath.
    + apply orb_true_iff in Hrest.
      destruct Hrest as [Hconstruct | Hrest].
      * apply path_has_suffixb_true_shape in Hconstruct.
        destruct Hconstruct as [prefix Hshape].
        subst path.
        eapply construct_expression_comma_repeat_suffix_not_alternative.
        exact Hpath.
      * apply orb_true_iff in Hrest.
        destruct Hrest as [Hrecord_decl | Hrest].
        -- apply path_has_suffixb_true_shape in Hrecord_decl.
           destruct Hrecord_decl as [prefix Hshape].
           subst path.
           eapply record_decl_comma_repeat_suffix_not_alternative.
           exact Hpath.
        -- apply orb_true_iff in Hrest.
           destruct Hrest as [Hrecord_pattern | Hvariant].
           ++ apply path_has_suffixb_true_shape in Hrecord_pattern.
              destruct Hrecord_pattern as [prefix Hshape].
              subst path.
              eapply record_pattern_comma_repeat_suffix_not_alternative.
              exact Hpath.
           ++ apply path_has_suffixb_true_shape in Hvariant.
              destruct Hvariant as [prefix Hshape].
              subst path.
              eapply variant_payload_comma_repeat_suffix_not_alternative.
              exact Hpath.
  - reflexivity.
Qed.
