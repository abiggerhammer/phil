From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarDeterminacySimpleResolvers
  GrammarDeterminacyActualCanonicalPath.

Import ListNotations.
Open Scope string_scope.

(*
  Rooted caller-prefix invariance for the five trailing-comma resolver paths.

  #794 proved the one-way fact that an already-recognized canonical suffix
  remains recognized after restoring the caller prefix.  The final mutual
  induction also needs the converse for the fallback branch.  That converse is
  false for arbitrary short paths, but canonical rule-local paths are rooted at
  a nonterminal reset and contain only structural steps after that root.

  Every trailing-comma suffix has exactly the same shape: one nonterminal root
  followed only by structural steps.  Therefore a suffix cannot begin in the
  caller prefix and cross a rule-local reset boundary: the canonical root would
  have to match a structural step.  This file packages that exact invariant.
*)

Definition phase1_surface_rule_local_structural_step
  (step : SyntaxPathStep) : Prop :=
  match step with
  | AtNonterminal _ => False
  | _ => True
  end.

Definition phase1_surface_rule_local_path
  (path : SyntaxPath) : Prop :=
  exists name tail,
    path = AtNonterminal name :: tail /\
    Forall phase1_surface_rule_local_structural_step tail.

Lemma phase1_surface_rule_local_structural_steps_rev :
  forall steps,
    Forall phase1_surface_rule_local_structural_step steps ->
    Forall phase1_surface_rule_local_structural_step (rev steps).
Proof.
  intros steps Hsteps.
  induction Hsteps as [| step rest Hstep Hrest IH].
  - simpl.
    constructor.
  - simpl.
    apply Forall_app.
    split.
    + exact IH.
    + constructor.
      * exact Hstep.
      * constructor.
Qed.

Lemma reversed_path_prefixb_rule_local_boundary_irrelevant :
  forall expected_steps expected_root local_steps local_root extra,
    Forall phase1_surface_rule_local_structural_step expected_steps ->
    Forall phase1_surface_rule_local_structural_step local_steps ->
    reversed_path_prefixb
      (expected_steps ++ [AtNonterminal expected_root])
      (local_steps ++ [AtNonterminal local_root] ++ extra) =
    reversed_path_prefixb
      (expected_steps ++ [AtNonterminal expected_root])
      (local_steps ++ [AtNonterminal local_root]).
Proof.
  induction expected_steps as [| expected expected_rest IH];
    intros expected_root local_steps local_root extra
      Hexpected Hlocal.
  - destruct local_steps as [| local local_rest].
    + simpl.
      reflexivity.
    + inversion Hlocal as [| ? ? Hlocal_head Hlocal_rest]; subst.
      simpl.
      destruct local;
        simpl in Hlocal_head |- *;
        try contradiction;
        reflexivity.
  - inversion Hexpected as [| ? ? Hexpected_head Hexpected_rest]; subst.
    destruct local_steps as [| local local_rest].
    + simpl.
      destruct expected;
        simpl in Hexpected_head |- *;
        try contradiction;
        reflexivity.
    + inversion Hlocal as [| ? ? Hlocal_head Hlocal_rest]; subst.
      simpl.
      f_equal.
      apply IH;
        assumption.
Qed.

Lemma path_has_rule_local_suffixb_prefix_irrelevant :
  forall (prefix : SyntaxPath)
         (local_root : string)
         (local_tail : list SyntaxPathStep)
         (suffix_root : string)
         (suffix_tail : list SyntaxPathStep),
    Forall phase1_surface_rule_local_structural_step local_tail ->
    Forall phase1_surface_rule_local_structural_step suffix_tail ->
    path_has_suffixb
      (List.app prefix (AtNonterminal local_root :: local_tail))
      (AtNonterminal suffix_root :: suffix_tail) =
    path_has_suffixb
      (AtNonterminal local_root :: local_tail)
      (AtNonterminal suffix_root :: suffix_tail).
Proof.
  intros prefix local_root local_tail suffix_root suffix_tail
    Hlocal Hsuffix.
  unfold path_has_suffixb.
  rewrite List.rev_app_distr.
  simpl.
  rewrite <- List.app_assoc.
  apply reversed_path_prefixb_rule_local_boundary_irrelevant.
  - apply phase1_surface_rule_local_structural_steps_rev.
    exact Hsuffix.
  - apply phase1_surface_rule_local_structural_steps_rev.
    exact Hlocal.
Qed.

Lemma phase1_surface_rule_local_path_reset :
  forall name,
    phase1_surface_rule_local_path [AtNonterminal name].
Proof.
  intros name.
  exists name, [].
  split.
  - reflexivity.
  - constructor.
Qed.

Lemma phase1_surface_rule_local_path_descend :
  forall path step,
    phase1_surface_rule_local_path path ->
    phase1_surface_rule_local_structural_step step ->
    phase1_surface_rule_local_path (descend path step).
Proof.
  intros path step Hpath Hstep.
  destruct Hpath as [name [tail [Hpath Htail]]].
  subst path.
  exists name, (tail ++ [step]).
  split.
  - unfold descend.
    simpl.
    reflexivity.
  - apply Forall_app.
    split.
    + exact Htail.
    + constructor.
      * exact Hstep.
      * constructor.
Qed.

Theorem trailing_comma_repeat_pathb_rule_local_prefix_irrelevant :
  forall (prefix : SyntaxPath)
         (local_root : string)
         (local_tail : list SyntaxPathStep),
    Forall phase1_surface_rule_local_structural_step local_tail ->
    trailing_comma_repeat_pathb
      (List.app prefix (AtNonterminal local_root :: local_tail)) =
    trailing_comma_repeat_pathb
      (AtNonterminal local_root :: local_tail).
Proof.
  intros prefix local_root local_tail Hlocal.
  unfold trailing_comma_repeat_pathb.
  unfold case_pattern_comma_repeat_suffix,
    construct_expression_comma_repeat_suffix,
    record_decl_comma_repeat_suffix,
    record_pattern_comma_repeat_suffix,
    variant_payload_comma_repeat_suffix.
  repeat rewrite path_has_rule_local_suffixb_prefix_irrelevant
    by (try exact Hlocal;
        unfold phase1_surface_rule_local_structural_step;
        repeat constructor).
  reflexivity.
Qed.

Theorem phase1_surface_actual_canonical_trailing_comma_equation :
  forall actual caller_prefix canonical,
    phase1_surface_actual_canonical_path
      actual caller_prefix canonical ->
    phase1_surface_rule_local_path canonical ->
    trailing_comma_repeat_pathb actual =
    trailing_comma_repeat_pathb canonical.
Proof.
  intros actual caller_prefix canonical Hpath Hlocal.
  unfold phase1_surface_actual_canonical_path in Hpath.
  subst actual.
  destruct Hlocal as [name [tail [Hcanonical Htail]]].
  subst canonical.
  apply trailing_comma_repeat_pathb_rule_local_prefix_irrelevant.
  exact Htail.
Qed.
