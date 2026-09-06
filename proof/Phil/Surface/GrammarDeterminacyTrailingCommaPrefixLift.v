From Stdlib Require Import Lists.List Lia.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarDeterminacySimpleResolvers
  GrammarDeterminacyPathPrefixInvariance
  GrammarDeterminacyPathSuffixReflection
  GrammarDeterminacyActualCanonicalPath.

Import ListNotations.

(*
  One-way caller-prefix transport for the five trailing-comma resolver paths.

  Arbitrary prefix invariance is intentionally too strong: a caller prefix can
  create a suffix match when the rule-local path is shorter than the suffix.
  The final ordinary-derivation -> predictive-oracle induction only needs the
  sound direction below.  Once a canonical rule-local path already matches a
  suffix, that suffix is no longer than the canonical path, so #772's
  length-bounded prefix invariance applies directly.
*)

Lemma path_has_suffixb_prefix_preserves_true :
  forall prefix path suffix,
    path_has_suffixb path suffix = true ->
    path_has_suffixb (prefix ++ path) suffix = true.
Proof.
  intros prefix path suffix Hsuffix.
  destruct
    (path_has_suffixb_true_shape path suffix Hsuffix)
    as [shape_prefix Hshape].
  assert (Hlength : List.length suffix <= List.length path).
  {
    rewrite Hshape, List.app_length.
    lia.
  }
  rewrite
    path_has_suffixb_prefix_irrelevant_when_long_enough
    by exact Hlength.
  exact Hsuffix.
Qed.

Theorem trailing_comma_repeat_pathb_prefix_preserves_true :
  forall prefix path,
    trailing_comma_repeat_pathb path = true ->
    trailing_comma_repeat_pathb (prefix ++ path) = true.
Proof.
  intros prefix path Htrail.
  unfold trailing_comma_repeat_pathb in Htrail |- *.
  apply orb_true_iff in Htrail as [Hcase | Htrail].
  - apply orb_true_iff.
    left.
    eapply path_has_suffixb_prefix_preserves_true.
    exact Hcase.
  - apply orb_true_iff in Htrail as [Hconstruct | Htrail].
    + apply orb_true_iff.
      right.
      apply orb_true_iff.
      left.
      eapply path_has_suffixb_prefix_preserves_true.
      exact Hconstruct.
    + apply orb_true_iff in Htrail as [Hrecord_decl | Htrail].
      * apply orb_true_iff.
        right.
        apply orb_true_iff.
        right.
        apply orb_true_iff.
        left.
        eapply path_has_suffixb_prefix_preserves_true.
        exact Hrecord_decl.
      * apply orb_true_iff in Htrail as [Hrecord_pattern | Hvariant].
        -- apply orb_true_iff.
           right.
           apply orb_true_iff.
           right.
           apply orb_true_iff.
           right.
           apply orb_true_iff.
           left.
           eapply path_has_suffixb_prefix_preserves_true.
           exact Hrecord_pattern.
        -- apply orb_true_iff.
           right.
           apply orb_true_iff.
           right.
           apply orb_true_iff.
           right.
           apply orb_true_iff.
           right.
           eapply path_has_suffixb_prefix_preserves_true.
           exact Hvariant.
Qed.

Theorem phase1_surface_actual_canonical_trailing_comma_lift :
  forall actual caller_prefix canonical,
    phase1_surface_actual_canonical_path
      actual caller_prefix canonical ->
    trailing_comma_repeat_pathb canonical = true ->
    trailing_comma_repeat_pathb actual = true.
Proof.
  intros actual caller_prefix canonical Hpath Htrail.
  unfold phase1_surface_actual_canonical_path in Hpath.
  subst actual.
  eapply trailing_comma_repeat_pathb_prefix_preserves_true.
  exact Htrail.
Qed.
