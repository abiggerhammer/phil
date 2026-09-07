From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  Grammar
  GrammarDeterminacySimpleResolvers
  GrammarDeterminacyOracleAssemblyCoverage
  GrammarDeterminacyOracleAssemblyReflection
  GrammarDeterminacyActualCanonicalPath
  GrammarDeterminacyRootedTrailingCommaInvariance.

Import ListNotations.

(*
  Sequence-head trailing-comma context for the final
  ordinary-derivation -> predictive-oracle mutual induction.

  A trailing-comma repetition is decided at the repetition expression path,
  but its eventual Stop commitment is justified by the enclosing sequence
  tail.  Package the actual/canonical path transport and assembly reflection
  here so the mutual induction only has to reason about the ordinary
  repetition/tail derivations themselves.
*)

Theorem phase1_surface_sequence_child_actual_canonical_invariants :
  forall actual caller_prefix canonical index,
    phase1_surface_actual_canonical_path
      actual caller_prefix canonical ->
    phase1_surface_rule_local_path canonical ->
    phase1_surface_actual_canonical_path
      (descend actual (AtSequence index))
      caller_prefix
      (descend canonical (AtSequence index)) /\
    phase1_surface_rule_local_path
      (descend canonical (AtSequence index)).
Proof.
  intros actual caller_prefix canonical index Hpath Hlocal.
  split.
  - apply phase1_surface_actual_canonical_path_descend.
    exact Hpath.
  - apply phase1_surface_rule_local_path_descend.
    + exact Hlocal.
    + simpl.
      exact I.
Qed.

Theorem phase1_surface_sequence_child_trailing_comma_equation :
  forall actual caller_prefix canonical index,
    phase1_surface_actual_canonical_path
      actual caller_prefix canonical ->
    phase1_surface_rule_local_path canonical ->
    trailing_comma_repeat_pathb
      (descend actual (AtSequence index)) =
    trailing_comma_repeat_pathb
      (descend canonical (AtSequence index)).
Proof.
  intros actual caller_prefix canonical index Hpath Hlocal.
  destruct
    (phase1_surface_sequence_child_actual_canonical_invariants
      actual caller_prefix canonical index Hpath Hlocal)
    as [Hchild_path Hchild_local].
  apply phase1_surface_actual_canonical_trailing_comma_equation
    with (caller_prefix := caller_prefix).
  - exact Hchild_path.
  - exact Hchild_local.
Qed.

Corollary phase1_surface_sequence_child_trailing_true_transport :
  forall actual caller_prefix canonical index,
    phase1_surface_actual_canonical_path
      actual caller_prefix canonical ->
    phase1_surface_rule_local_path canonical ->
    trailing_comma_repeat_pathb
      (descend canonical (AtSequence index)) = true ->
    trailing_comma_repeat_pathb
      (descend actual (AtSequence index)) = true.
Proof.
  intros actual caller_prefix canonical index Hpath Hlocal Htrailing.
  pose proof
    (phase1_surface_sequence_child_trailing_comma_equation
      actual caller_prefix canonical index Hpath Hlocal)
    as Heq.
  rewrite Htrailing in Heq.
  exact Heq.
Qed.

Corollary phase1_surface_sequence_child_trailing_false_transport :
  forall actual caller_prefix canonical index,
    phase1_surface_actual_canonical_path
      actual caller_prefix canonical ->
    phase1_surface_rule_local_path canonical ->
    trailing_comma_repeat_pathb
      (descend canonical (AtSequence index)) = false ->
    trailing_comma_repeat_pathb
      (descend actual (AtSequence index)) = false.
Proof.
  intros actual caller_prefix canonical index Hpath Hlocal Htrailing.
  pose proof
    (phase1_surface_sequence_child_trailing_comma_equation
      actual caller_prefix canonical index Hpath Hlocal)
    as Heq.
  rewrite Htrailing in Heq.
  exact Heq.
Qed.

Theorem phase1_surface_sequence_head_trailing_assembly_context :
  forall actual caller_prefix canonical index body rest outer_follow,
    phase1_surface_actual_canonical_path
      actual caller_prefix canonical ->
    phase1_surface_rule_local_path canonical ->
    trailing_comma_repeat_pathb
      (descend canonical (AtSequence index)) = true ->
    sequence_head_assembly_guardb
      canonical index (ERepetition body) rest outer_follow = true ->
    trailing_comma_repeat_pathb
      (descend actual (AtSequence index)) = true /\
    comma_identifier_repetition_bodyb body = true /\
    trailing_comma_tail_shapeb rest outer_follow = true.
Proof.
  intros actual caller_prefix canonical index body rest outer_follow
    Hpath Hlocal Htrailing Hguard.
  pose proof
    (phase1_surface_sequence_child_trailing_true_transport
      actual caller_prefix canonical index Hpath Hlocal Htrailing)
    as Hactual_trailing.
  destruct
    (sequence_head_assembly_guard_trailing
      canonical index body rest outer_follow Htrailing Hguard)
    as [Hbody Htail].
  split.
  - exact Hactual_trailing.
  - split.
    + exact Hbody.
    + exact Htail.
Qed.
