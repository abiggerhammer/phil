From Stdlib Require Import Bool.Bool Lists.List.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyNullableFirst
  GrammarDeterminacyPredictiveOracle
  GrammarDeterminacyWitnessSoundness
  GrammarDeterminacyContinuationSoundness
  GrammarDeterminacyFollowCoverage
  GrammarDeterminacyDerivationPathSoundness
  GrammarDeterminacyOracleAssemblyCoverage
  GrammarDeterminacyOracleAssemblyReflection.

Import ListNotations.

(*
  Final ordinary-derivation -> predictive-oracle bridge for
  PHIL-SURFACE-DETERM-001.

  This first layer packages the structural choice-safety facts and exact root
  invariants consumed by the mutual derivation induction.  Keeping these
  boolean-reflection steps outside that induction prevents conversion-heavy
  proof terms from accumulating in its constructor cases.
*)

Lemma predictive_bridge_choice_safe_sequence_cons :
  forall fuel item rest,
    choice_bodies_nonnullable_fuel
      (S fuel) (ESequence (item :: rest)) = true ->
    choice_bodies_nonnullable_fuel fuel item = true /\
    choice_bodies_nonnullable_fuel
      (S fuel) (ESequence rest) = true.
Proof.
  intros fuel item rest Hsafe.
  rewrite continuation_choice_bodies_nonnullable_sequence_step in Hsafe.
  simpl in Hsafe.
  apply andb_true_iff in Hsafe as [Hhead Hrest].
  split.
  - exact Hhead.
  - rewrite continuation_choice_bodies_nonnullable_sequence_step.
    exact Hrest.
Qed.

Lemma predictive_bridge_choice_safe_alternative_member :
  forall fuel items index item,
    choice_bodies_nonnullable_fuel
      (S fuel) (EAlternative items) = true ->
    nth_error items index = Some item ->
    nullable_expression phase1_surface_nullable_facts item = false /\
    choice_bodies_nonnullable_fuel fuel item = true.
Proof.
  intros fuel items index item Hsafe Hnth.
  rewrite choice_bodies_nonnullable_alternative_step in Hsafe.
  rewrite forallb_forall in Hsafe.
  pose proof (Hsafe item (nth_error_In items index item Hnth)) as Hitem.
  apply andb_true_iff in Hitem as [Hnonnullable Hchild].
  apply negb_true_iff in Hnonnullable.
  split; assumption.
Qed.

Lemma predictive_bridge_choice_safe_optional_body :
  forall fuel body,
    choice_bodies_nonnullable_fuel
      (S fuel) (EOptional body) = true ->
    nullable_expression phase1_surface_nullable_facts body = false /\
    choice_bodies_nonnullable_fuel fuel body = true.
Proof.
  intros fuel body Hsafe.
  rewrite choice_safe_first_optional_safety_equation in Hsafe.
  apply andb_true_iff in Hsafe as [Hnonnullable Hbody].
  apply negb_true_iff in Hnonnullable.
  split; assumption.
Qed.

Lemma predictive_bridge_choice_safe_repetition_body :
  forall fuel body,
    choice_bodies_nonnullable_fuel
      (S fuel) (ERepetition body) = true ->
    nullable_expression phase1_surface_nullable_facts body = false /\
    choice_bodies_nonnullable_fuel fuel body = true.
Proof.
  intros fuel body Hsafe.
  rewrite choice_safe_first_repetition_safety_equation in Hsafe.
  apply andb_true_iff in Hsafe as [Hnonnullable Hbody].
  apply negb_true_iff in Hnonnullable.
  split; assumption.
Qed.

Lemma phase1_surface_predictive_bridge_root_choice_safe :
  choice_bodies_nonnullable_fuel
    expression_fuel (ENonterminal phase1_surface_start) = true.
Proof.
  reflexivity.
Qed.

Lemma phase1_surface_predictive_bridge_root_assembly_covered :
  oracle_assembly_coverage_fuel
    oracle_assembly_fuel
    []
    phase1_surface_start_follow
    (ENonterminal phase1_surface_start) = true.
Proof.
  reflexivity.
Qed.

Theorem phase1_surface_predictive_bridge_root_invariants :
  forall tokens tree,
    Phase1CompleteDerivation tokens tree ->
    phase1_surface_expression_path_context
      [] (ENonterminal phase1_surface_start) /\
    choice_bodies_nonnullable_fuel
      expression_fuel (ENonterminal phase1_surface_start) = true /\
    follow_coverage_fuel
      expression_fuel
      phase1_surface_start_follow
      (ENonterminal phase1_surface_start) = true /\
    oracle_assembly_coverage_fuel
      oracle_assembly_fuel
      []
      phase1_surface_start_follow
      (ENonterminal phase1_surface_start) = true /\
    continuation_lookahead_mem [] phase1_surface_start_follow = true.
Proof.
  intros tokens tree Hderive.
  repeat split.
  - exact (phase1_surface_complete_derivation_root_path_context
      tokens tree Hderive).
  - exact phase1_surface_predictive_bridge_root_choice_safe.
  - exact phase1_surface_root_follow_covered.
  - exact phase1_surface_predictive_bridge_root_assembly_covered.
  - exact phase1_surface_start_follow_accepts_eof.
Qed.
