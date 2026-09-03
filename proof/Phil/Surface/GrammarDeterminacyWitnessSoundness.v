From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Strings.String Lia.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationLookahead
  GrammarDerivationOracle
  GrammarDeterminacyCertificate
  GrammarDeterminacyNullableFirst
  GrammarDeterminacyFollowOverlap
  GrammarDeterminacySimpleResolvers
  GrammarDeterminacyStructuralResolvers
  GrammarDeterminacyPredictiveOracle.

Import ListNotations.
Open Scope string_scope.

Opaque phase1_surface_rules
  phase1_surface_nullable_facts
  phase1_surface_first_facts.

(*
  Fixed-point soundness bridge for PHIL-SURFACE-DETERM-001.

  #586 exposes implementation-independent structural nullable/FIRST witnesses
  from ordinary EBNF derivations.  #569 computes the exact Grammar-v1
  nullable/FIRST fixed points, while #582 checks that every exact choice body
  is non-nullable and that expression traversal has sufficient fuel.

  This file proves that, under that exact #582 fuel/safety certificate, the
  #586 witnesses are sound for the #569 computed facts.  It deliberately does
  not yet justify optional/repetition stop decisions; those require accepting
  continuation/FOLLOW reasoning and remain the next bridge.
*)

Lemma lookupRule_forallb :
  forall (predicate : GrammarRule -> bool) rules name body,
    forallb predicate rules = true ->
    lookupRule name rules = Some body ->
    predicate (name, body) = true.
Proof.
  intros predicate rules.
  induction rules as [| [candidate expression] rest IH];
    intros name body Hall Hlookup; simpl in *.
  - discriminate.
  - apply andb_true_iff in Hall as [Hhead Htail].
    destruct (String.eqb name candidate) eqn:Hname.
    + apply String.eqb_eq in Hname. subst candidate.
      inversion Hlookup. subst body.
      exact Hhead.
    + eapply IH; eauto.
Qed.

Lemma phase1_surface_rule_choice_safe :
  forall name body,
    lookupRule name phase1_surface_rules = Some body ->
    choice_bodies_nonnullable_rule (name, body) = true.
Proof.
  intros name body Hlookup.
  eapply lookupRule_forallb.
  - exact phase1_surface_all_choice_bodies_are_nonnullable.
  - exact Hlookup.
Qed.

Lemma choice_bodies_nonnullable_rule_pair :
  forall name body,
    choice_bodies_nonnullable_rule (name, body) =
    choice_bodies_nonnullable_fuel expression_fuel body.
Proof.
  reflexivity.
Qed.

Lemma phase1_surface_rule_body_choice_safe :
  forall name body,
    lookupRule name phase1_surface_rules = Some body ->
    choice_bodies_nonnullable_fuel expression_fuel body = true.
Proof.
  intros name body Hlookup.
  assert (Hsafe : choice_bodies_nonnullable_rule (name, body) = true).
  {
    eapply lookupRule_forallb.
    - exact phase1_surface_all_choice_bodies_are_nonnullable.
    - exact Hlookup.
  }
  rewrite choice_bodies_nonnullable_rule_pair in Hsafe.
  exact Hsafe.
Qed.

Lemma lookup_bool_nullable_pass :
  forall rules facts name body,
    lookupRule name rules = Some body ->
    lookup_bool name (nullable_pass rules facts) =
      nullable_expression facts body.
Proof.
  intros rules facts.
  induction rules as [| [candidate expression] rest IH];
    intros name body Hlookup; simpl in *.
  - discriminate.
  - destruct (String.eqb name candidate) eqn:Hname.
    + inversion Hlookup. subst body. reflexivity.
    + eapply IH. exact Hlookup.
Qed.

Lemma phase1_surface_nullable_lookup_rule :
  forall name body,
    lookupRule name phase1_surface_rules = Some body ->
    lookup_bool name phase1_surface_nullable_facts =
      nullable_expression phase1_surface_nullable_facts body.
Proof.
  intros name body Hlookup.
  pose proof
    (lookup_bool_nullable_pass
      phase1_surface_rules phase1_surface_nullable_facts
      name body Hlookup) as Hfact.
  rewrite phase1_surface_nullable_facts_are_stable in Hfact.
  exact Hfact.
Qed.

Lemma lookup_tokens_first_pass :
  forall rules nullable_facts first_facts name body,
    lookupRule name rules = Some body ->
    lookup_tokens name (first_pass rules nullable_facts first_facts) =
      first_expression nullable_facts first_facts body.
Proof.
  intros rules nullable_facts first_facts.
  induction rules as [| [candidate expression] rest IH];
    intros name body Hlookup; simpl in *.
  - discriminate.
  - destruct (String.eqb name candidate) eqn:Hname.
    + inversion Hlookup. subst body. reflexivity.
    + eapply IH. exact Hlookup.
Qed.

Lemma phase1_surface_first_lookup_rule :
  forall name body,
    lookupRule name phase1_surface_rules = Some body ->
    lookup_tokens name phase1_surface_first_facts =
      first_expression
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        body.
Proof.
  intros name body Hlookup.
  pose proof
    (lookup_tokens_first_pass
      phase1_surface_rules
      phase1_surface_nullable_facts
      phase1_surface_first_facts
      name body Hlookup) as Hfact.
  rewrite phase1_surface_first_facts_are_stable in Hfact.
  exact Hfact.
Qed.

Lemma nullable_sequence_cons_defined :
  forall fuel item rest item_value rest_value,
    nullable_expression_fuel
      fuel phase1_surface_nullable_facts item = Some item_value ->
    nullable_expression_fuel
      (S fuel) phase1_surface_nullable_facts (ESequence rest) = Some rest_value ->
    exists value,
      nullable_expression_fuel
        (S fuel) phase1_surface_nullable_facts
        (ESequence (item :: rest)) = Some value.
Proof.
  intros fuel item rest item_value rest_value Hitem Hrest.
  simpl in Hrest.
  simpl.
  rewrite Hitem, Hrest.
  eexists. reflexivity.
Qed.

Lemma nullable_alternative_cons_defined :
  forall fuel item rest item_value rest_value,
    nullable_expression_fuel
      fuel phase1_surface_nullable_facts item = Some item_value ->
    nullable_expression_fuel
      (S fuel) phase1_surface_nullable_facts
      (EAlternative rest) = Some rest_value ->
    exists value,
      nullable_expression_fuel
        (S fuel) phase1_surface_nullable_facts
        (EAlternative (item :: rest)) = Some value.
Proof.
  intros fuel item rest item_value rest_value Hitem Hrest.
  simpl in Hrest.
  simpl.
  rewrite Hitem, Hrest.
  eexists. reflexivity.
Qed.

Lemma choice_safe_nullable_sequence_defined :
  forall fuel items,
    (forall expression,
      choice_bodies_nonnullable_fuel fuel expression = true ->
      exists value,
        nullable_expression_fuel
          fuel phase1_surface_nullable_facts expression = Some value) ->
    forallb (choice_bodies_nonnullable_fuel fuel) items = true ->
    exists value,
      nullable_expression_fuel
        (S fuel) phase1_surface_nullable_facts (ESequence items) = Some value.
Proof.
  intros fuel items IH.
  induction items as [| item rest IHrest]; intros Hsafe; simpl in Hsafe.
  - simpl. eexists. reflexivity.
  - apply andb_true_iff in Hsafe as [Hitem_safe Hrest_safe].
    destruct (IH item Hitem_safe) as [item_value Hitem_value].
    destruct (IHrest Hrest_safe) as [rest_value Hrest_value].
    eapply nullable_sequence_cons_defined; eauto.
Qed.

Lemma choice_safe_nullable_alternative_defined :
  forall fuel items,
    (forall expression,
      choice_bodies_nonnullable_fuel fuel expression = true ->
      exists value,
        nullable_expression_fuel
          fuel phase1_surface_nullable_facts expression = Some value) ->
    forallb
      (fun item =>
        andb
          (negb (nullable_expression phase1_surface_nullable_facts item))
          (choice_bodies_nonnullable_fuel fuel item))
      items = true ->
    exists value,
      nullable_expression_fuel
        (S fuel) phase1_surface_nullable_facts (EAlternative items) = Some value.
Proof.
  intros fuel items IH.
  induction items as [| item rest IHrest]; intros Hsafe; simpl in Hsafe.
  - simpl. eexists. reflexivity.
  - apply andb_true_iff in Hsafe as [Hhead_safe Hrest_safe].
    apply andb_true_iff in Hhead_safe as [_ Hitem_safe].
    destruct (IH item Hitem_safe) as [item_value Hitem_value].
    destruct (IHrest Hrest_safe) as [rest_value Hrest_value].
    eapply nullable_alternative_cons_defined; eauto.
Qed.

Lemma choice_safe_nullable_defined :
  forall fuel expression,
    choice_bodies_nonnullable_fuel fuel expression = true ->
    exists value,
      nullable_expression_fuel
        fuel phase1_surface_nullable_facts expression = Some value.
Proof.
  induction fuel as [| fuel IH]; intros expression Hsafe.
  - simpl in Hsafe. discriminate.
  - destruct expression as
      [literal | class_name | name | items | items | body | body].
    + simpl. eexists. reflexivity.
    + simpl. eexists. reflexivity.
    + simpl. eexists. reflexivity.
    + simpl in Hsafe.
      eapply choice_safe_nullable_sequence_defined; eauto.
    + simpl in Hsafe.
      eapply choice_safe_nullable_alternative_defined; eauto.
    + simpl. eexists. reflexivity.
    + simpl. eexists. reflexivity.
Qed.

Lemma first_sequence_cons_defined :
  forall fuel item rest item_first item_nullable rest_first,
    first_expression_fuel
      fuel phase1_surface_nullable_facts phase1_surface_first_facts item =
      Some item_first ->
    nullable_expression_fuel
      fuel phase1_surface_nullable_facts item = Some item_nullable ->
    first_expression_fuel
      (S fuel) phase1_surface_nullable_facts phase1_surface_first_facts
      (ESequence rest) = Some rest_first ->
    exists tokens,
      first_expression_fuel
        (S fuel) phase1_surface_nullable_facts phase1_surface_first_facts
        (ESequence (item :: rest)) = Some tokens.
Proof.
  intros fuel item rest item_first item_nullable rest_first
    Hitem_first Hitem_nullable Hrest_first.
  simpl in Hrest_first.
  simpl.
  rewrite Hitem_first, Hitem_nullable.
  destruct item_nullable.
  - rewrite Hrest_first. eexists. reflexivity.
  - eexists. reflexivity.
Qed.

Lemma first_alternative_cons_defined :
  forall fuel item rest item_first rest_first,
    first_expression_fuel
      fuel phase1_surface_nullable_facts phase1_surface_first_facts item =
      Some item_first ->
    first_expression_fuel
      (S fuel) phase1_surface_nullable_facts phase1_surface_first_facts
      (EAlternative rest) = Some rest_first ->
    exists tokens,
      first_expression_fuel
        (S fuel) phase1_surface_nullable_facts phase1_surface_first_facts
        (EAlternative (item :: rest)) = Some tokens.
Proof.
  intros fuel item rest item_first rest_first Hitem_first Hrest_first.
  simpl in Hrest_first.
  simpl.
  rewrite Hitem_first, Hrest_first.
  eexists. reflexivity.
Qed.

Lemma choice_safe_first_sequence_defined :
  forall fuel items,
    (forall expression,
      choice_bodies_nonnullable_fuel fuel expression = true ->
      exists tokens,
        first_expression_fuel
          fuel
          phase1_surface_nullable_facts
          phase1_surface_first_facts
          expression = Some tokens) ->
    forallb (choice_bodies_nonnullable_fuel fuel) items = true ->
    exists tokens,
      first_expression_fuel
        (S fuel)
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        (ESequence items) = Some tokens.
Proof.
  intros fuel items IH.
  induction items as [| item rest IHrest]; intros Hsafe; simpl in Hsafe.
  - simpl. eexists. reflexivity.
  - apply andb_true_iff in Hsafe as [Hitem_safe Hrest_safe].
    destruct (IH item Hitem_safe) as [item_first Hitem_first].
    destruct (choice_safe_nullable_defined fuel item Hitem_safe)
      as [item_nullable Hitem_nullable].
    destruct (IHrest Hrest_safe) as [rest_first Hrest_first].
    eapply first_sequence_cons_defined; eauto.
Qed.

Lemma choice_safe_first_alternative_defined :
  forall fuel items,
    (forall expression,
      choice_bodies_nonnullable_fuel fuel expression = true ->
      exists tokens,
        first_expression_fuel
          fuel
          phase1_surface_nullable_facts
          phase1_surface_first_facts
          expression = Some tokens) ->
    forallb
      (fun item =>
        andb
          (negb (nullable_expression phase1_surface_nullable_facts item))
          (choice_bodies_nonnullable_fuel fuel item))
      items = true ->
    exists tokens,
      first_expression_fuel
        (S fuel)
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        (EAlternative items) = Some tokens.
Proof.
  intros fuel items IH.
  induction items as [| item rest IHrest]; intros Hsafe; simpl in Hsafe.
  - simpl. eexists. reflexivity.
  - apply andb_true_iff in Hsafe as [Hhead_safe Hrest_safe].
    apply andb_true_iff in Hhead_safe as [_ Hitem_safe].
    destruct (IH item Hitem_safe) as [item_first Hitem_first].
    destruct (IHrest Hrest_safe) as [rest_first Hrest_first].
    eapply first_alternative_cons_defined; eauto.
Qed.

Lemma choice_safe_first_defined :
  forall fuel expression,
    choice_bodies_nonnullable_fuel fuel expression = true ->
    exists tokens,
      first_expression_fuel
        fuel
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        expression = Some tokens.
Proof.
  induction fuel as [| fuel IH]; intros expression Hsafe.
  - simpl in Hsafe. discriminate.
  - destruct expression as
      [literal | class_name | name | items | items | body | body].
    + simpl. eexists. reflexivity.
    + simpl. eexists. reflexivity.
    + simpl. eexists. reflexivity.
    + simpl in Hsafe.
      eapply choice_safe_first_sequence_defined; eauto.
    + simpl in Hsafe.
      eapply choice_safe_first_alternative_defined; eauto.
    + simpl in Hsafe.
      apply andb_true_iff in Hsafe as [_ Hbody_safe].
      exact (IH body Hbody_safe).
    + simpl in Hsafe.
      apply andb_true_iff in Hsafe as [_ Hbody_safe].
      exact (IH body Hbody_safe).
Qed.

Definition NullableWitnessFuelProperty (expression : EbnfExpression) : Prop :=
  forall fuel,
    fuel <= expression_fuel ->
    choice_bodies_nonnullable_fuel fuel expression = true ->
    nullable_expression_fuel
      fuel phase1_surface_nullable_facts expression = Some true.

Definition NullableSequenceFuelProperty
  (items : list EbnfExpression) : Prop :=
  forall fuel,
    S fuel <= expression_fuel ->
    forallb (choice_bodies_nonnullable_fuel fuel) items = true ->
    nullable_expression_fuel
      (S fuel) phase1_surface_nullable_facts (ESequence items) = Some true.

Definition NullableAlternativeFuelProperty
  (items : list EbnfExpression) : Prop :=
  forall fuel,
    S fuel <= expression_fuel ->
    forallb
      (fun item =>
        andb
          (negb (nullable_expression phase1_surface_nullable_facts item))
          (choice_bodies_nonnullable_fuel fuel item))
      items = true ->
    nullable_expression_fuel
      (S fuel) phase1_surface_nullable_facts (EAlternative items) = Some true.

Theorem phase1_surface_nullable_witness_fuel_sound :
  (forall expression,
    NullableWitness phase1_surface_rules expression ->
    NullableWitnessFuelProperty expression) /\
  (forall items,
    NullableSequenceWitness phase1_surface_rules items ->
    NullableSequenceFuelProperty items) /\
  (forall items,
    NullableAlternativeWitness phase1_surface_rules items ->
    NullableAlternativeFuelProperty items).
Proof.
  apply NullableWitness_mutind.
  - intros name body Hlookup Hbody IHbody.
    unfold NullableWitnessFuelProperty in *.
    intros fuel Hfuel Hsafe.
    destruct fuel as [| fuel].
    + simpl in Hsafe. discriminate.
    + assert (Hbody_safe :
        choice_bodies_nonnullable_fuel expression_fuel body = true).
      { eapply phase1_surface_rule_body_choice_safe. exact Hlookup. }
      specialize (IHbody expression_fuel (Nat.le_refl _) Hbody_safe).
      pose proof (phase1_surface_nullable_lookup_rule name body Hlookup)
        as Hlookup_fact.
      unfold nullable_expression in Hlookup_fact.
      rewrite IHbody in Hlookup_fact.
      simpl in Hlookup_fact.
      simpl. rewrite Hlookup_fact. reflexivity.
  - intros items Hitems IHitems.
    unfold NullableWitnessFuelProperty, NullableSequenceFuelProperty in *.
    intros fuel Hfuel Hsafe.
    destruct fuel as [| fuel].
    + simpl in Hsafe. discriminate.
    + simpl in Hsafe.
      exact (IHitems fuel Hfuel Hsafe).
  - intros items Hitems IHitems.
    unfold NullableWitnessFuelProperty, NullableAlternativeFuelProperty in *.
    intros fuel Hfuel Hsafe.
    destruct fuel as [| fuel].
    + simpl in Hsafe. discriminate.
    + simpl in Hsafe.
      exact (IHitems fuel Hfuel Hsafe).
  - intros body.
    unfold NullableWitnessFuelProperty.
    intros fuel Hfuel Hsafe.
    destruct fuel; simpl in *; try discriminate; reflexivity.
  - intros body.
    unfold NullableWitnessFuelProperty.
    intros fuel Hfuel Hsafe.
    destruct fuel; simpl in *; try discriminate; reflexivity.
  - unfold NullableSequenceFuelProperty.
    intros fuel Hfuel Hsafe.
    reflexivity.
  - intros item rest Hitem IHitem Hrest IHrest.
    unfold NullableSequenceFuelProperty in *.
    intros fuel Hfuel Hsafe.
    simpl in Hsafe.
    apply andb_true_iff in Hsafe as [Hitem_safe Hrest_safe].
    assert (Hfuel_item : fuel <= expression_fuel) by lia.
    specialize (IHitem fuel Hfuel_item Hitem_safe).
    specialize (IHrest fuel Hfuel Hrest_safe).
    simpl in IHrest.
    simpl.
    rewrite IHitem, IHrest.
    reflexivity.
  - intros item rest Hitem IHitem.
    unfold NullableAlternativeFuelProperty in *.
    intros fuel Hfuel Hsafe.
    simpl in Hsafe.
    apply andb_true_iff in Hsafe as [Hhead_safe Hrest_safe].
    apply andb_true_iff in Hhead_safe as [_ Hitem_safe].
    assert (Hfuel_item : fuel <= expression_fuel) by lia.
    specialize (IHitem fuel Hfuel_item Hitem_safe).
    assert (Hrest_expr_safe :
      choice_bodies_nonnullable_fuel
        (S fuel) (EAlternative rest) = true).
    { simpl. exact Hrest_safe. }
    destruct (choice_safe_nullable_defined
      (S fuel) (EAlternative rest) Hrest_expr_safe)
      as [rest_value Hrest_value].
    simpl in Hrest_value.
    simpl.
    rewrite IHitem, Hrest_value.
    reflexivity.
  - intros item rest Hrest IHrest.
    unfold NullableAlternativeFuelProperty in *.
    intros fuel Hfuel Hsafe.
    simpl in Hsafe.
    apply andb_true_iff in Hsafe as [Hhead_safe Hrest_safe].
    apply andb_true_iff in Hhead_safe as [_ Hitem_safe].
    destruct (choice_safe_nullable_defined fuel item Hitem_safe)
      as [item_value Hitem_value].
    specialize (IHrest fuel Hfuel Hrest_safe).
    simpl in IHrest.
    simpl.
    rewrite Hitem_value, IHrest.
    destruct item_value; reflexivity.
Qed.

Corollary phase1_surface_nullable_witness_matches_computed_facts :
  forall expression,
    NullableWitness phase1_surface_rules expression ->
    choice_bodies_nonnullable_fuel expression_fuel expression = true ->
    nullable_expression phase1_surface_nullable_facts expression = true.
Proof.
  intros expression Hnullable Hsafe.
  pose proof
    (proj1 phase1_surface_nullable_witness_fuel_sound
      expression Hnullable expression_fuel (Nat.le_refl _) Hsafe)
    as Heval.
  unfold nullable_expression.
  rewrite Heval.
  reflexivity.
Qed.

Lemma overlap_token_eqb_eq :
  forall first second,
    overlap_token_eqb first second = true -> first = second.
Proof.
  intros first second.
  destruct first, second; simpl; try discriminate; try (intro; reflexivity).
  - intro Heq. apply String.eqb_eq in Heq. subst. reflexivity.
  - intro Heq. apply String.eqb_eq in Heq. subst. reflexivity.
Qed.

Lemma overlap_token_eqb_refl :
  forall token,
    overlap_token_eqb token token = true.
Proof.
  intros token. destruct token; simpl; try rewrite String.eqb_refl; reflexivity.
Qed.

Lemma token_mem_insert_preserve :
  forall target inserted tokens,
    token_mem target tokens = true ->
    token_mem target (token_insert inserted tokens) = true.
Proof.
  intros target inserted tokens Htarget.
  unfold token_insert.
  destruct (token_mem inserted tokens) eqn:Hinserted.
  - exact Htarget.
  - simpl.
    destruct (overlap_token_eqb target inserted); auto.
Qed.

Lemma token_mem_insert_self :
  forall token tokens,
    token_mem token (token_insert token tokens) = true.
Proof.
  intros token tokens.
  unfold token_insert.
  destruct (token_mem token tokens) eqn:Hmem.
  - exact Hmem.
  - simpl. rewrite overlap_token_eqb_refl. reflexivity.
Qed.

Lemma token_mem_union_right :
  forall target left right,
    token_mem target right = true ->
    token_mem target (token_union left right) = true.
Proof.
  intros target left.
  induction left as [| head rest IH]; intros right Hmem; simpl.
  - exact Hmem.
  - apply IH.
    apply token_mem_insert_preserve.
    exact Hmem.
Qed.

Lemma token_mem_union_left :
  forall target left right,
    token_mem target left = true ->
    token_mem target (token_union left right) = true.
Proof.
  intros target left.
  induction left as [| head rest IH]; intros right Hmem.
  - discriminate.
  - simpl in Hmem.
    destruct (overlap_token_eqb target head) eqn:Heq.
    + apply overlap_token_eqb_eq in Heq. subst head.
      simpl.
      apply token_mem_union_right.
      apply token_mem_insert_self.
    + simpl.
      apply IH.
      exact Hmem.
Qed.

Definition FirstWitnessFuelProperty
  (token : OverlapToken) (expression : EbnfExpression) : Prop :=
  forall fuel,
    fuel <= expression_fuel ->
    choice_bodies_nonnullable_fuel fuel expression = true ->
    exists tokens,
      first_expression_fuel
        fuel
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        expression = Some tokens /\
      token_mem token tokens = true.

Definition FirstSequenceFuelProperty
  (token : OverlapToken) (items : list EbnfExpression) : Prop :=
  forall fuel,
    S fuel <= expression_fuel ->
    forallb (choice_bodies_nonnullable_fuel fuel) items = true ->
    exists tokens,
      first_expression_fuel
        (S fuel)
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        (ESequence items) = Some tokens /\
      token_mem token tokens = true.

Definition FirstAlternativeFuelProperty
  (token : OverlapToken) (items : list EbnfExpression) : Prop :=
  forall fuel,
    S fuel <= expression_fuel ->
    forallb
      (fun item =>
        andb
          (negb (nullable_expression phase1_surface_nullable_facts item))
          (choice_bodies_nonnullable_fuel fuel item))
      items = true ->
    exists tokens,
      first_expression_fuel
        (S fuel)
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        (EAlternative items) = Some tokens /\
      token_mem token tokens = true.

Theorem phase1_surface_first_witness_fuel_sound :
  (forall token expression,
    FirstWitness phase1_surface_rules token expression ->
    FirstWitnessFuelProperty token expression) /\
  (forall token items,
    FirstSequenceWitness phase1_surface_rules token items ->
    FirstSequenceFuelProperty token items) /\
  (forall token items,
    FirstAlternativeWitness phase1_surface_rules token items ->
    FirstAlternativeFuelProperty token items).
Proof.
  apply FirstWitness_mutind.
  - intros token literal Htoken.
    unfold FirstWitnessFuelProperty.
    intros fuel Hfuel Hsafe.
    destruct fuel as [| fuel].
    + simpl in Hsafe. discriminate.
    + subst token. eexists. split; simpl.
      * reflexivity.
      * rewrite String.eqb_refl. reflexivity.
  - intros token class_name Htoken.
    unfold FirstWitnessFuelProperty.
    intros fuel Hfuel Hsafe.
    destruct fuel as [| fuel].
    + simpl in Hsafe. discriminate.
    + subst token. eexists. split; simpl.
      * reflexivity.
      * rewrite String.eqb_refl. reflexivity.
  - intros token name body Hlookup Hbody IHbody.
    unfold FirstWitnessFuelProperty in *.
    intros fuel Hfuel Hsafe.
    destruct fuel as [| fuel].
    + simpl in Hsafe. discriminate.
    + assert (Hbody_safe :
        choice_bodies_nonnullable_fuel expression_fuel body = true).
      { eapply phase1_surface_rule_body_choice_safe. exact Hlookup. }
      destruct (IHbody expression_fuel (Nat.le_refl _) Hbody_safe)
        as [tokens [Hbody_first Hbody_mem]].
      pose proof (phase1_surface_first_lookup_rule name body Hlookup)
        as Hlookup_fact.
      unfold first_expression in Hlookup_fact.
      rewrite Hbody_first in Hlookup_fact.
      simpl in Hlookup_fact.
      exists tokens. split.
      * simpl. rewrite Hlookup_fact. reflexivity.
      * exact Hbody_mem.
  - intros token items Hitems IHitems.
    unfold FirstWitnessFuelProperty, FirstSequenceFuelProperty in *.
    intros fuel Hfuel Hsafe.
    destruct fuel as [| fuel].
    + simpl in Hsafe. discriminate.
    + simpl in Hsafe.
      exact (IHitems fuel Hfuel Hsafe).
  - intros token items Hitems IHitems.
    unfold FirstWitnessFuelProperty, FirstAlternativeFuelProperty in *.
    intros fuel Hfuel Hsafe.
    destruct fuel as [| fuel].
    + simpl in Hsafe. discriminate.
    + simpl in Hsafe.
      exact (IHitems fuel Hfuel Hsafe).
  - intros token body Hbody IHbody.
    unfold FirstWitnessFuelProperty in *.
    intros fuel Hfuel Hsafe.
    destruct fuel as [| fuel].
    + simpl in Hsafe. discriminate.
    + simpl in Hsafe.
      apply andb_true_iff in Hsafe as [_ Hbody_safe].
      assert (Hfuel_body : fuel <= expression_fuel) by lia.
      exact (IHbody fuel Hfuel_body Hbody_safe).
  - intros token body Hbody IHbody.
    unfold FirstWitnessFuelProperty in *.
    intros fuel Hfuel Hsafe.
    destruct fuel as [| fuel].
    + simpl in Hsafe. discriminate.
    + simpl in Hsafe.
      apply andb_true_iff in Hsafe as [_ Hbody_safe].
      assert (Hfuel_body : fuel <= expression_fuel) by lia.
      exact (IHbody fuel Hfuel_body Hbody_safe).
  - intros token item rest Hitem IHitem.
    unfold FirstSequenceFuelProperty in *.
    intros fuel Hfuel Hsafe.
    simpl in Hsafe.
    apply andb_true_iff in Hsafe as [Hitem_safe Hrest_safe].
    assert (Hfuel_item : fuel <= expression_fuel) by lia.
    destruct (IHitem fuel Hfuel_item Hitem_safe)
      as [item_first [Hitem_first Hitem_mem]].
    destruct (choice_safe_nullable_defined fuel item Hitem_safe)
      as [item_nullable Hitem_nullable].
    assert (Hrest_expr_safe :
      choice_bodies_nonnullable_fuel (S fuel) (ESequence rest) = true).
    { simpl. exact Hrest_safe. }
    destruct (choice_safe_first_defined
      (S fuel) (ESequence rest) Hrest_expr_safe)
      as [rest_first Hrest_first].
    simpl in Hrest_first.
    simpl.
    rewrite Hitem_first, Hitem_nullable.
    destruct item_nullable.
    + rewrite Hrest_first.
      exists (token_union item_first rest_first). split.
      * reflexivity.
      * apply token_mem_union_left. exact Hitem_mem.
    + exists item_first. split; [reflexivity | exact Hitem_mem].
  - intros token item rest Hnullable Hrest IHrest.
    unfold FirstSequenceFuelProperty in *.
    intros fuel Hfuel Hsafe.
    simpl in Hsafe.
    apply andb_true_iff in Hsafe as [Hitem_safe Hrest_safe].
    assert (Hfuel_item : fuel <= expression_fuel) by lia.
    pose proof
      (proj1 phase1_surface_nullable_witness_fuel_sound
        item Hnullable fuel Hfuel_item Hitem_safe)
      as Hitem_nullable.
    destruct (choice_safe_first_defined fuel item Hitem_safe)
      as [item_first Hitem_first].
    destruct (IHrest fuel Hfuel Hrest_safe)
      as [rest_first [Hrest_first Hrest_mem]].
    simpl in Hrest_first.
    simpl.
    rewrite Hitem_first, Hitem_nullable, Hrest_first.
    exists (token_union item_first rest_first). split.
    + reflexivity.
    + apply token_mem_union_right. exact Hrest_mem.
  - intros token item rest Hitem IHitem.
    unfold FirstAlternativeFuelProperty in *.
    intros fuel Hfuel Hsafe.
    simpl in Hsafe.
    apply andb_true_iff in Hsafe as [Hhead_safe Hrest_safe].
    apply andb_true_iff in Hhead_safe as [_ Hitem_safe].
    assert (Hfuel_item : fuel <= expression_fuel) by lia.
    destruct (IHitem fuel Hfuel_item Hitem_safe)
      as [item_first [Hitem_first Hitem_mem]].
    assert (Hrest_expr_safe :
      choice_bodies_nonnullable_fuel (S fuel) (EAlternative rest) = true).
    { simpl. exact Hrest_safe. }
    destruct (choice_safe_first_defined
      (S fuel) (EAlternative rest) Hrest_expr_safe)
      as [rest_first Hrest_first].
    simpl in Hrest_first.
    simpl.
    rewrite Hitem_first, Hrest_first.
    exists (token_union item_first rest_first). split.
    + reflexivity.
    + apply token_mem_union_left. exact Hitem_mem.
  - intros token item rest Hrest IHrest.
    unfold FirstAlternativeFuelProperty in *.
    intros fuel Hfuel Hsafe.
    simpl in Hsafe.
    apply andb_true_iff in Hsafe as [Hhead_safe Hrest_safe].
    apply andb_true_iff in Hhead_safe as [_ Hitem_safe].
    destruct (choice_safe_first_defined fuel item Hitem_safe)
      as [item_first Hitem_first].
    destruct (IHrest fuel Hfuel Hrest_safe)
      as [rest_first [Hrest_first Hrest_mem]].
    simpl in Hrest_first.
    simpl.
    rewrite Hitem_first, Hrest_first.
    exists (token_union item_first rest_first). split.
    + reflexivity.
    + apply token_mem_union_right. exact Hrest_mem.
Qed.

Corollary phase1_surface_first_witness_matches_computed_facts :
  forall token expression,
    FirstWitness phase1_surface_rules token expression ->
    choice_bodies_nonnullable_fuel expression_fuel expression = true ->
    token_mem token
      (first_expression
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        expression) = true.
Proof.
  intros token expression Hfirst Hsafe.
  destruct
    (proj1 phase1_surface_first_witness_fuel_sound
      token expression Hfirst expression_fuel (Nat.le_refl _) Hsafe)
    as [tokens [Heval Hmem]].
  unfold first_expression.
  rewrite Heval.
  exact Hmem.
Qed.

Transparent phase1_surface_rules
  phase1_surface_nullable_facts
  phase1_surface_first_facts.
