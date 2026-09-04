From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Strings.String Lia.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationLookahead
  GrammarDeterminacyCertificate
  GrammarDeterminacyNullableFirst
  GrammarDeterminacyFollowOverlap
  GrammarDeterminacySimpleResolvers
  GrammarDeterminacyPredictiveOracle
  GrammarDeterminacyWitnessSoundness.

Import ListNotations.
Open Scope string_scope.

(*
  Accepting continuation/FOLLOW bridge for PHIL-SURFACE-DETERM-001.

  #592 connects semantic nullable/FIRST witnesses from ordinary derivations to
  the exact computed Grammar-v1 tables.  This file adds the dual continuation
  facts needed at zero-consuming choices.  It mirrors the local FOLLOW
  propagation from GrammarDeterminacyFollowOverlap.v without importing parser
  branch order or resolver policy.

  The two central lemmas say:

    - a derived sequence begins either with a token from FIRST(sequence), or,
      when it consumes nothing, with an accepting token from the sequence's
      outer continuation; and
    - a derived repetition begins either with a token from FIRST(body), or,
      when it stops, with an accepting token from the repetition's outer
      continuation.

  These are the semantic facts the final ordinary-derivation -> predictive-
  oracle theorem needs for optional/repetition skip/stop choices.
*)

Definition continuation_lookahead_mem
  (input : list ConcreteToken)
  (follow : list OverlapToken) : bool :=
  match input with
  | [] => token_mem OverlapEof follow
  | first_token :: _ =>
      token_mem
        (GrammarDeterminacyPredictiveOracle.concrete_token_shape first_token)
        follow
  end.

Lemma continuation_concrete_token_shapes_agree :
  forall token,
    GrammarDeterminacyPredictiveOracle.concrete_token_shape token =
    GrammarDerivationLookahead.concrete_token_shape token.
Proof.
  intros token.
  destruct token; reflexivity.
Qed.

Lemma continuation_lookahead_mem_union_right :
  forall input left right,
    continuation_lookahead_mem input right = true ->
    continuation_lookahead_mem input (token_union left right) = true.
Proof.
  intros input left right Hmem.
  destruct input as [| first_token rest];
    unfold continuation_lookahead_mem in *.
  - apply token_mem_union_right. exact Hmem.
  - apply token_mem_union_right. exact Hmem.
Qed.

Lemma continuation_lookahead_mem_union_left :
  forall input left right,
    continuation_lookahead_mem input left = true ->
    continuation_lookahead_mem input (token_union left right) = true.
Proof.
  intros input left right Hmem.
  destruct input as [| first_token rest];
    unfold continuation_lookahead_mem in *.
  - apply token_mem_union_left. exact Hmem.
  - apply token_mem_union_left. exact Hmem.
Qed.

Definition phase1_surface_sequence_local_follow
  (items : list EbnfExpression)
  (outer_follow : list OverlapToken) : list OverlapToken :=
  let suffix := ESequence items in
  let suffix_first :=
    first_expression
      phase1_surface_nullable_facts
      phase1_surface_first_facts
      suffix in
  if nullable_expression phase1_surface_nullable_facts suffix
  then token_union suffix_first outer_follow
  else suffix_first.

Definition phase1_surface_repetition_local_follow
  (body : EbnfExpression)
  (outer_follow : list OverlapToken) : list OverlapToken :=
  token_union
    (first_expression
      phase1_surface_nullable_facts
      phase1_surface_first_facts
      body)
    outer_follow.

Lemma continuation_choice_bodies_nonnullable_sequence_step :
  forall fuel items,
    choice_bodies_nonnullable_fuel (S fuel) (ESequence items) =
    forallb (choice_bodies_nonnullable_fuel fuel) items.
Proof.
  reflexivity.
Qed.

Lemma choice_bodies_nonnullable_fuel_step_monotone :
  forall fuel expression,
    choice_bodies_nonnullable_fuel fuel expression = true ->
    choice_bodies_nonnullable_fuel (S fuel) expression = true.
Proof.
  intros fuel.
  induction fuel as [| fuel IH]; intros expression Hsafe.
  - change false = true in Hsafe.
    discriminate.
  - destruct expression as
      [literal | class_name | name | items | items | body | body].
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + rewrite continuation_choice_bodies_nonnullable_sequence_step in Hsafe.
      rewrite continuation_choice_bodies_nonnullable_sequence_step.
      eapply
        (forallb_impl_true_depth
          EbnfExpression
          (choice_bodies_nonnullable_fuel fuel)
          (choice_bodies_nonnullable_fuel (S fuel))
          items).
      * intros item Hitem.
        apply IH. exact Hitem.
      * exact Hsafe.
    + rewrite choice_bodies_nonnullable_alternative_step in Hsafe.
      rewrite choice_bodies_nonnullable_alternative_step.
      eapply
        (forallb_impl_true_depth
          EbnfExpression
          (fun item =>
            andb
              (negb
                (nullable_expression
                  phase1_surface_nullable_facts item))
              (choice_bodies_nonnullable_fuel fuel item))
          (fun item =>
            andb
              (negb
                (nullable_expression
                  phase1_surface_nullable_facts item))
              (choice_bodies_nonnullable_fuel (S fuel) item))
          items).
      * intros item Hitem.
        apply andb_true_iff in Hitem as [Hnullable Hchild].
        apply andb_true_iff. split.
        -- exact Hnullable.
        -- apply IH. exact Hchild.
      * exact Hsafe.
    + rewrite choice_bodies_nonnullable_optional_step in Hsafe.
      rewrite choice_bodies_nonnullable_optional_step.
      apply andb_true_iff in Hsafe as [Hnullable Hbody].
      apply andb_true_iff. split.
      * exact Hnullable.
      * apply IH. exact Hbody.
    + rewrite choice_bodies_nonnullable_repetition_step in Hsafe.
      rewrite choice_bodies_nonnullable_repetition_step.
      apply andb_true_iff in Hsafe as [Hnullable Hbody].
      apply andb_true_iff. split.
      * exact Hnullable.
      * apply IH. exact Hbody.
Qed.

Lemma choice_bodies_nonnullable_fuel_monotone :
  forall low high expression,
    low <= high ->
    choice_bodies_nonnullable_fuel low expression = true ->
    choice_bodies_nonnullable_fuel high expression = true.
Proof.
  intros low high expression Hle Hsafe.
  induction Hle.
  - exact Hsafe.
  - apply choice_bodies_nonnullable_fuel_step_monotone.
    exact IHHle.
Qed.

Lemma sequence_choice_safe_at_expression_fuel :
  forall fuel items,
    S fuel <= expression_fuel ->
    forallb (choice_bodies_nonnullable_fuel fuel) items = true ->
    choice_bodies_nonnullable_fuel
      expression_fuel (ESequence items) = true.
Proof.
  intros fuel items Hfuel Hsafe.
  eapply choice_bodies_nonnullable_fuel_monotone.
  - exact Hfuel.
  - rewrite continuation_choice_bodies_nonnullable_sequence_step.
    exact Hsafe.
Qed.

Lemma first_witness_is_computed_continuation_first :
  forall first_token tail expression,
    FirstWitness
      phase1_surface_rules
      (GrammarDerivationLookahead.concrete_token_shape first_token)
      expression ->
    choice_bodies_nonnullable_fuel
      expression_fuel expression = true ->
    continuation_lookahead_mem
      (first_token :: tail)
      (first_expression
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        expression) = true.
Proof.
  intros first_token tail expression Hfirst Hsafe.
  unfold continuation_lookahead_mem.
  rewrite continuation_concrete_token_shapes_agree.
  eapply phase1_surface_first_witness_matches_computed_facts.
  - exact Hfirst.
  - exact Hsafe.
Qed.

Theorem phase1_surface_sequence_accepting_continuation_sound :
  forall path index items input rest trees fuel outer_follow,
    DerivesSequence
      phase1_surface_rules path index items input rest trees ->
    S fuel <= expression_fuel ->
    forallb (choice_bodies_nonnullable_fuel fuel) items = true ->
    continuation_lookahead_mem rest outer_follow = true ->
    continuation_lookahead_mem
      input
      (phase1_surface_sequence_local_follow items outer_follow) = true.
Proof.
  intros path index items input rest trees fuel outer_follow
    Hderive Hfuel Hsafe Hcontinuation.
  assert (Hsequence_safe :
    choice_bodies_nonnullable_fuel
      expression_fuel (ESequence items) = true).
  {
    eapply sequence_choice_safe_at_expression_fuel.
    - exact Hfuel.
    - exact Hsafe.
  }
  destruct
    (List.list_eq_dec concrete_token_eq_dec input rest)
    as [Hequal | Hprogress].
  - subst rest.
    pose proof
      ((proj1 (proj2
        (no_consume_derivation_has_nullable_witness
          phase1_surface_rules)))
        path index items input input trees Hderive eq_refl)
      as Hnullable_items.
    assert (Hnullable_sequence :
      NullableWitness
        phase1_surface_rules (ESequence items)).
    {
      apply nullable_sequence_witness.
      exact Hnullable_items.
    }
    pose proof
      (phase1_surface_nullable_witness_matches_computed_facts
        (ESequence items) Hnullable_sequence Hsequence_safe)
      as Hnullable.
    unfold phase1_surface_sequence_local_follow.
    rewrite Hnullable.
    apply continuation_lookahead_mem_union_right.
    exact Hcontinuation.
  - destruct input as [| first_token tail].
    + exfalso.
      apply Hprogress.
      destruct
        (derives_sequence_consumes_prefix
          phase1_surface_rules path index items [] rest trees Hderive)
        as [consumed Hprefix].
      destruct consumed as [| head consumed].
      * simpl in Hprefix. exact Hprefix.
      * discriminate Hprefix.
    + pose proof
        ((proj1 (proj2
          (consuming_derivation_has_first_witness
            phase1_surface_rules)))
          path index items (first_token :: tail) rest trees Hderive)
        as Hfirst_property.
      unfold DerivesSequenceFirstProperty in Hfirst_property.
      pose proof (Hfirst_property Hprogress) as Hfirst_items.
      assert (Hfirst_sequence :
        FirstWitness
          phase1_surface_rules
          (GrammarDerivationLookahead.concrete_token_shape first_token)
          (ESequence items)).
      {
        apply first_sequence_witness.
        exact Hfirst_items.
      }
      pose proof
        (first_witness_is_computed_continuation_first
          first_token tail (ESequence items)
          Hfirst_sequence Hsequence_safe)
        as Hfirst_mem.
      unfold phase1_surface_sequence_local_follow.
      destruct
        (nullable_expression
          phase1_surface_nullable_facts (ESequence items))
        eqn:Hnullable.
      * apply continuation_lookahead_mem_union_left.
        exact Hfirst_mem.
      * exact Hfirst_mem.
Qed.

Theorem phase1_surface_repetition_accepting_continuation_sound :
  forall path body input rest trees fuel outer_follow,
    DerivesRepetition
      phase1_surface_rules path body input rest trees ->
    fuel <= expression_fuel ->
    choice_bodies_nonnullable_fuel fuel body = true ->
    continuation_lookahead_mem rest outer_follow = true ->
    continuation_lookahead_mem
      input
      (phase1_surface_repetition_local_follow body outer_follow) = true.
Proof.
  intros path body input rest trees fuel outer_follow
    Hderive Hfuel Hsafe Hcontinuation.
  destruct
    (List.list_eq_dec concrete_token_eq_dec input rest)
    as [Hequal | Hprogress].
  - subst rest.
    unfold phase1_surface_repetition_local_follow.
    apply continuation_lookahead_mem_union_right.
    exact Hcontinuation.
  - destruct input as [| first_token tail].
    + exfalso.
      apply Hprogress.
      destruct
        (derives_repetition_consumes_prefix
          phase1_surface_rules path body [] rest trees Hderive)
        as [consumed Hprefix].
      destruct consumed as [| head consumed].
      * simpl in Hprefix. exact Hprefix.
      * discriminate Hprefix.
    + pose proof
        ((proj2 (proj2
          (consuming_derivation_has_first_witness
            phase1_surface_rules)))
          path body (first_token :: tail) rest trees Hderive)
        as Hfirst_property.
      unfold DerivesRepetitionFirstProperty in Hfirst_property.
      pose proof (Hfirst_property Hprogress) as Hfirst_body.
      assert (Hbody_safe :
        choice_bodies_nonnullable_fuel
          expression_fuel body = true).
      {
        eapply choice_bodies_nonnullable_fuel_monotone.
        - exact Hfuel.
        - exact Hsafe.
      }
      pose proof
        (first_witness_is_computed_continuation_first
          first_token tail body Hfirst_body Hbody_safe)
        as Hfirst_mem.
      unfold phase1_surface_repetition_local_follow.
      apply continuation_lookahead_mem_union_left.
      exact Hfirst_mem.
Qed.

Lemma token_intersection_empty_excludes_shared_member :
  forall token left right,
    token_intersection left right = [] ->
    token_mem token right = true ->
    token_mem token left = false.
Proof.
  intros token left.
  induction left as [| head rest IH]; intros right Hintersection Hright.
  - reflexivity.
  - simpl in Hintersection.
    destruct (token_mem head right) eqn:Hhead.
    + discriminate Hintersection.
    + simpl.
      destruct (overlap_token_eqb token head) eqn:Heq.
      * apply overlap_token_eqb_eq in Heq.
        subst head.
        rewrite Hright in Hhead.
        discriminate.
      * eapply IH.
        -- exact Hintersection.
        -- exact Hright.
Qed.

Lemma expression_starts_inputb_nil_equation :
  forall expression,
    expression_starts_inputb expression [] =
    nullable_expression phase1_surface_nullable_facts expression.
Proof.
  reflexivity.
Qed.

Lemma expression_starts_inputb_cons_equation :
  forall expression first_token rest,
    expression_starts_inputb expression (first_token :: rest) =
    token_mem
      (GrammarDeterminacyPredictiveOracle.concrete_token_shape first_token)
      (first_expression
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        expression).
Proof.
  reflexivity.
Qed.

Lemma accepting_continuation_excludes_body_start_without_overlap :
  forall body input outer_follow,
    nullable_expression phase1_surface_nullable_facts body = false ->
    token_intersection
      (first_expression
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        body)
      outer_follow = [] ->
    continuation_lookahead_mem input outer_follow = true ->
    expression_starts_inputb body input = false.
Proof.
  intros body input outer_follow Hnullable Hdisjoint Hcontinuation.
  destruct input as [| first_token rest].
  - rewrite expression_starts_inputb_nil_equation.
    exact Hnullable.
  - rewrite expression_starts_inputb_cons_equation.
    eapply token_intersection_empty_excludes_shared_member.
    + exact Hdisjoint.
    + unfold continuation_lookahead_mem in Hcontinuation.
      exact Hcontinuation.
Qed.

Definition optional_follow_overlap_siteb (site : OverlapSite) : bool :=
  overlap_kind_eqb (overlap_kind site) OptionalFollowOverlap.

Definition repeat_follow_overlap_siteb (site : OverlapSite) : bool :=
  overlap_kind_eqb (overlap_kind site) RepeatFollowOverlap.

Theorem phase1_surface_has_no_optional_follow_overlap_sites :
  List.length
    (filter optional_follow_overlap_siteb
      phase1_surface_determinacy_certificate) = 0.
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem phase1_surface_repeat_follow_overlap_sites_are_exactly_five :
  List.length
    (filter repeat_follow_overlap_siteb
      phase1_surface_determinacy_certificate) = 5.
Proof.
  vm_compute.
  reflexivity.
Qed.

Definition repeat_follow_site_is_trailing_comma_resolvedb
  (site : OverlapSite) : bool :=
  if repeat_follow_overlap_siteb site
  then trailing_comma_resolver_siteb site
  else true.

Theorem phase1_surface_every_repeat_follow_overlap_is_trailing_comma_resolved :
  forallb
    repeat_follow_site_is_trailing_comma_resolvedb
    phase1_surface_determinacy_certificate = true.
Proof.
  vm_compute.
  reflexivity.
Qed.
