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

Lemma forallb_andb_right :
  forall (A : Type) (left right : A -> bool) items,
    forallb (fun item => andb (left item) (right item)) items = true ->
    forallb right items = true.
Proof.
  intros A left right items.
  induction items as [| item rest IH]; intros Hall; simpl in *.
  - reflexivity.
  - apply andb_true_iff in Hall as [Hhead Htail].
    apply andb_true_iff in Hhead as [_ Hright].
    apply andb_true_iff. split.
    + exact Hright.
    + apply IH. exact Htail.
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

Lemma choice_safe_nullable_alternative_choices_defined :
  forall fuel items,
    (forall expression,
      choice_bodies_nonnullable_fuel fuel expression = true ->
      exists value,
        nullable_expression_fuel
          fuel phase1_surface_nullable_facts expression = Some value) ->
    forallb (choice_bodies_nonnullable_fuel fuel) items = true ->
    exists value,
      nullable_expression_fuel
        (S fuel) phase1_surface_nullable_facts (EAlternative items) = Some value.
Proof.
  intros fuel items IH.
  induction items as [| item rest IHrest]; intros Hsafe; simpl in Hsafe.
  - simpl. eexists. reflexivity.
  - apply andb_true_iff in Hsafe as [Hitem_safe Hrest_safe].
    destruct (IH item Hitem_safe) as [item_value Hitem_value].
    destruct (IHrest Hrest_safe) as [rest_value Hrest_value].
    eapply nullable_alternative_cons_defined; eauto.
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
  intros fuel items IH Hsafe.
  eapply choice_safe_nullable_alternative_choices_defined.
  - exact IH.
  - eapply
      (forallb_andb_right
        EbnfExpression
        (fun item => negb (nullable_expression phase1_surface_nullable_facts item))
        (choice_bodies_nonnullable_fuel fuel)
        items).
    exact Hsafe.
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

Lemma choice_safe_first_alternative_choices_defined :
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
        (EAlternative items) = Some tokens.
Proof.
  intros fuel items IH.
  induction items as [| item rest IHrest]; intros Hsafe; simpl in Hsafe.
  - simpl. eexists. reflexivity.
  - apply andb_true_iff in Hsafe as [Hitem_safe Hrest_safe].
    destruct (IH item Hitem_safe) as [item_first Hitem_first].
    destruct (IHrest Hrest_safe) as [rest_first Hrest_first].
    eapply first_alternative_cons_defined; eauto.
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
  intros fuel items IH Hsafe.
  eapply choice_safe_first_alternative_choices_defined.
  - exact IH.
  - eapply
      (forallb_andb_right
        EbnfExpression
        (fun item => negb (nullable_expression phase1_surface_nullable_facts item))
        (choice_bodies_nonnullable_fuel fuel)
        items).
    exact Hsafe.
Qed.

Lemma choice_safe_first_optional_safety_equation :
  forall fuel body,
    choice_bodies_nonnullable_fuel (S fuel) (EOptional body) =
    andb
      (negb (nullable_expression phase1_surface_nullable_facts body))
      (choice_bodies_nonnullable_fuel fuel body).
Proof.
  reflexivity.
Qed.

Lemma choice_safe_first_repetition_safety_equation :
  forall fuel body,
    choice_bodies_nonnullable_fuel (S fuel) (ERepetition body) =
    andb
      (negb (nullable_expression phase1_surface_nullable_facts body))
      (choice_bodies_nonnullable_fuel fuel body).
Proof.
  reflexivity.
Qed.

Lemma first_expression_optional_fuel_equation :
  forall fuel body,
    first_expression_fuel
      (S fuel)
      phase1_surface_nullable_facts
      phase1_surface_first_facts
      (EOptional body) =
    first_expression_fuel
      fuel
      phase1_surface_nullable_facts
      phase1_surface_first_facts
      body.
Proof.
  reflexivity.
Qed.

Lemma first_expression_repetition_fuel_equation :
  forall fuel body,
    first_expression_fuel
      (S fuel)
      phase1_surface_nullable_facts
      phase1_surface_first_facts
      (ERepetition body) =
    first_expression_fuel
      fuel
      phase1_surface_nullable_facts
      phase1_surface_first_facts
      body.
Proof.
  reflexivity.
Qed.

Lemma choice_safe_first_optional_defined :
  forall fuel body,
    (forall expression,
      choice_bodies_nonnullable_fuel fuel expression = true ->
      exists tokens,
        first_expression_fuel
          fuel
          phase1_surface_nullable_facts
          phase1_surface_first_facts
          expression = Some tokens) ->
    choice_bodies_nonnullable_fuel (S fuel) (EOptional body) = true ->
    exists tokens,
      first_expression_fuel
        (S fuel)
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        (EOptional body) = Some tokens.
Proof.
  intros fuel body IH Hsafe.
  rewrite choice_safe_first_optional_safety_equation in Hsafe.
  apply andb_true_iff in Hsafe as [_ Hbody_safe].
  destruct (IH body Hbody_safe) as [tokens Htokens].
  exists tokens.
  rewrite first_expression_optional_fuel_equation.
  exact Htokens.
Qed.

Lemma choice_safe_first_repetition_defined :
  forall fuel body,
    (forall expression,
      choice_bodies_nonnullable_fuel fuel expression = true ->
      exists tokens,
        first_expression_fuel
          fuel
          phase1_surface_nullable_facts
          phase1_surface_first_facts
          expression = Some tokens) ->
    choice_bodies_nonnullable_fuel (S fuel) (ERepetition body) = true ->
    exists tokens,
      first_expression_fuel
        (S fuel)
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        (ERepetition body) = Some tokens.
Proof.
  intros fuel body IH Hsafe.
  rewrite choice_safe_first_repetition_safety_equation in Hsafe.
  apply andb_true_iff in Hsafe as [_ Hbody_safe].
  destruct (IH body Hbody_safe) as [tokens Htokens].
  exists tokens.
  rewrite first_expression_repetition_fuel_equation.
  exact Htokens.
Qed.

Lemma choice_safe_first_defined_step :
  forall fuel,
    (forall expression,
      choice_bodies_nonnullable_fuel fuel expression = true ->
      exists tokens,
        first_expression_fuel
          fuel
          phase1_surface_nullable_facts
          phase1_surface_first_facts
          expression = Some tokens) ->
    forall expression,
      choice_bodies_nonnullable_fuel (S fuel) expression = true ->
      exists tokens,
        first_expression_fuel
          (S fuel)
          phase1_surface_nullable_facts
          phase1_surface_first_facts
          expression = Some tokens.
Proof.
  intros fuel IH expression Hsafe.
  destruct expression as
    [literal | class_name | name | items | items | body | body].
  - abstract (simpl; eexists; reflexivity).
  - abstract (simpl; eexists; reflexivity).
  - abstract (simpl; eexists; reflexivity).
  - abstract (
      simpl in Hsafe;
      exact (choice_safe_first_sequence_defined fuel items IH Hsafe)).
  - abstract (
      simpl in Hsafe;
      exact (choice_safe_first_alternative_defined fuel items IH Hsafe)).
  - exact (choice_safe_first_optional_defined fuel body IH Hsafe).
  - exact (choice_safe_first_repetition_defined fuel body IH Hsafe).
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
  induction fuel as [| fuel IH].
  - intros expression Hsafe.
    simpl in Hsafe. discriminate.
  - intros expression Hsafe.
    exact (choice_safe_first_defined_step fuel IH expression Hsafe).
Qed.

Fixpoint nullable_depth_safe_fuel
  (fuel : nat)
  (expression : EbnfExpression) : bool :=
  match fuel with
  | O => false
  | S remaining =>
      match expression with
      | ELiteral _ => true
      | ELexicalClass _ => true
      | ENonterminal _ => true
      | ESequence items =>
          forallb (nullable_depth_safe_fuel remaining) items
      | EAlternative items =>
          forallb (nullable_depth_safe_fuel remaining) items
      | EOptional _ => true
      | ERepetition _ => true
      end
  end.

Lemma forallb_impl_true_depth :
  forall (A : Type) (source target : A -> bool) items,
    (forall item, source item = true -> target item = true) ->
    forallb source items = true ->
    forallb target items = true.
Proof.
  intros A source target items Himpl.
  induction items as [| item rest IH]; simpl; intros Hall.
  - reflexivity.
  - apply andb_true_iff in Hall as [Hitem Hrest].
    apply andb_true_iff. split.
    + apply Himpl. exact Hitem.
    + apply IH. exact Hrest.
Qed.

Lemma choice_safe_implies_nullable_depth_safe :
  forall fuel expression,
    choice_bodies_nonnullable_fuel fuel expression = true ->
    nullable_depth_safe_fuel fuel expression = true.
Proof.
  induction fuel as [| fuel IH]; intros expression Hsafe.
  - simpl in Hsafe. discriminate.
  - destruct expression as
      [literal | class_name | name | items | items | body | body];
      simpl in Hsafe |- *.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + eapply
        (forallb_impl_true_depth
          EbnfExpression
          (choice_bodies_nonnullable_fuel fuel)
          (nullable_depth_safe_fuel fuel)).
      * intros item Hitem. apply IH. exact Hitem.
      * exact Hsafe.
    + pose proof
        (forallb_andb_right
          EbnfExpression
          (fun item =>
            negb
              (nullable_expression
                phase1_surface_nullable_facts item))
          (choice_bodies_nonnullable_fuel fuel)
          items Hsafe)
        as Hbodies.
      eapply
        (forallb_impl_true_depth
          EbnfExpression
          (choice_bodies_nonnullable_fuel fuel)
          (nullable_depth_safe_fuel fuel)).
      * intros item Hitem. apply IH. exact Hitem.
      * exact Hbodies.
    + reflexivity.
    + reflexivity.
Qed.

Definition nullable_depth_safe_rule (rule : GrammarRule) : bool :=
  match rule with
  | (_, expression) =>
      nullable_depth_safe_fuel expression_fuel expression
  end.

Theorem phase1_surface_all_rule_bodies_nullable_depth_safe :
  forallb nullable_depth_safe_rule phase1_surface_rules = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_rule_body_nullable_depth_safe :
  forall name body,
    lookupRule name phase1_surface_rules = Some body ->
    nullable_depth_safe_fuel expression_fuel body = true.
Proof.
  intros name body Hlookup.
  apply choice_safe_implies_nullable_depth_safe.
  apply phase1_surface_rule_body_choice_safe with name.
  exact Hlookup.
Qed.

Lemma nullable_depth_safe_sequence_defined :
  forall fuel items,
    (forall expression,
      nullable_depth_safe_fuel fuel expression = true ->
      exists value,
        nullable_expression_fuel
          fuel phase1_surface_nullable_facts expression = Some value) ->
    forallb (nullable_depth_safe_fuel fuel) items = true ->
    exists value,
      nullable_expression_fuel
        (S fuel) phase1_surface_nullable_facts
        (ESequence items) = Some value.
Proof.
  intros fuel items Hdefined.
  induction items as [| item rest IHrest]; intros Hsafe.
  - simpl. eexists. reflexivity.
  - simpl in Hsafe.
    apply andb_true_iff in Hsafe as [Hitem_safe Hrest_safe].
    destruct (Hdefined item Hitem_safe) as [item_value Hitem].
    destruct (IHrest Hrest_safe) as [rest_value Hrest].
    eapply nullable_sequence_cons_defined; eauto.
Qed.

Lemma nullable_depth_safe_alternative_defined :
  forall fuel items,
    (forall expression,
      nullable_depth_safe_fuel fuel expression = true ->
      exists value,
        nullable_expression_fuel
          fuel phase1_surface_nullable_facts expression = Some value) ->
    forallb (nullable_depth_safe_fuel fuel) items = true ->
    exists value,
      nullable_expression_fuel
        (S fuel) phase1_surface_nullable_facts
        (EAlternative items) = Some value.
Proof.
  intros fuel items Hdefined.
  induction items as [| item rest IHrest]; intros Hsafe.
  - simpl. eexists. reflexivity.
  - simpl in Hsafe.
    apply andb_true_iff in Hsafe as [Hitem_safe Hrest_safe].
    destruct (Hdefined item Hitem_safe) as [item_value Hitem].
    destruct (IHrest Hrest_safe) as [rest_value Hrest].
    eapply nullable_alternative_cons_defined; eauto.
Qed.

Lemma nullable_depth_safe_defined :
  forall fuel expression,
    nullable_depth_safe_fuel fuel expression = true ->
    exists value,
      nullable_expression_fuel
        fuel phase1_surface_nullable_facts expression = Some value.
Proof.
  induction fuel as [| fuel IH]; intros expression Hsafe.
  - simpl in Hsafe. discriminate.
  - destruct expression as
      [literal | class_name | name | items | items | body | body];
      simpl in Hsafe |- *.
    + eexists. reflexivity.
    + eexists. reflexivity.
    + eexists. reflexivity.
    + eapply nullable_depth_safe_sequence_defined.
      * intros child Hchild. apply IH. exact Hchild.
      * exact Hsafe.
    + eapply nullable_depth_safe_alternative_defined.
      * intros child Hchild. apply IH. exact Hchild.
      * exact Hsafe.
    + eexists. reflexivity.
    + eexists. reflexivity.
Qed.

Inductive ComputedNullableSem : EbnfExpression -> Prop :=
| computed_nullable_nonterminal_sem :
    forall name,
      lookup_bool name phase1_surface_nullable_facts = true ->
      ComputedNullableSem (ENonterminal name)
| computed_nullable_sequence_sem :
    forall items,
      ComputedNullableSequenceSem items ->
      ComputedNullableSem (ESequence items)
| computed_nullable_alternative_sem :
    forall items,
      ComputedNullableAlternativeSem items ->
      ComputedNullableSem (EAlternative items)
| computed_nullable_optional_sem :
    forall body,
      ComputedNullableSem (EOptional body)
| computed_nullable_repetition_sem :
    forall body,
      ComputedNullableSem (ERepetition body)

with ComputedNullableSequenceSem : list EbnfExpression -> Prop :=
| computed_nullable_sequence_nil_sem :
    ComputedNullableSequenceSem []
| computed_nullable_sequence_cons_sem :
    forall item rest,
      ComputedNullableSem item ->
      ComputedNullableSequenceSem rest ->
      ComputedNullableSequenceSem (item :: rest)

with ComputedNullableAlternativeSem : list EbnfExpression -> Prop :=
| computed_nullable_alternative_here_sem :
    forall item rest,
      ComputedNullableSem item ->
      ComputedNullableAlternativeSem (item :: rest)
| computed_nullable_alternative_later_sem :
    forall item rest,
      ComputedNullableAlternativeSem rest ->
      ComputedNullableAlternativeSem (item :: rest).

Lemma computed_nullable_sequence_sem_sound :
  forall fuel items,
    (forall expression,
      ComputedNullableSem expression ->
      nullable_depth_safe_fuel fuel expression = true ->
      nullable_expression_fuel
        fuel phase1_surface_nullable_facts expression = Some true) ->
    ComputedNullableSequenceSem items ->
    forallb (nullable_depth_safe_fuel fuel) items = true ->
    nullable_expression_fuel
      (S fuel) phase1_surface_nullable_facts
      (ESequence items) = Some true.
Proof.
  intros fuel items Hsound Hsem.
  induction Hsem as
    [| item rest Hitem Hrest IHrest]; intros Hsafe.
  - reflexivity.
  - simpl in Hsafe.
    apply andb_true_iff in Hsafe as [Hitem_safe Hrest_safe].
    pose proof (Hsound item Hitem Hitem_safe) as Hitem_true.
    assert (Hrest_expr_safe :
      nullable_depth_safe_fuel
        (S fuel) (ESequence rest) = true).
    { simpl. exact Hrest_safe. }
    pose proof (IHrest Hrest_safe) as Hrest_true.
    pose proof Hrest_true as Hrest_local.
    simpl in Hrest_local.
    simpl.
    rewrite Hitem_true, Hrest_local.
    reflexivity.
Qed.

Lemma computed_nullable_alternative_sem_sound :
  forall fuel items,
    (forall expression,
      ComputedNullableSem expression ->
      nullable_depth_safe_fuel fuel expression = true ->
      nullable_expression_fuel
        fuel phase1_surface_nullable_facts expression = Some true) ->
    ComputedNullableAlternativeSem items ->
    forallb (nullable_depth_safe_fuel fuel) items = true ->
    nullable_expression_fuel
      (S fuel) phase1_surface_nullable_facts
      (EAlternative items) = Some true.
Proof.
  intros fuel items Hsound Hsem.
  induction Hsem as
    [item rest Hitem | item rest Hrest IHrest]; intros Hsafe.
  - simpl in Hsafe.
    apply andb_true_iff in Hsafe as [Hitem_safe Hrest_safe].
    pose proof (Hsound item Hitem Hitem_safe) as Hitem_true.
    assert (Hrest_expr_safe :
      nullable_depth_safe_fuel
        (S fuel) (EAlternative rest) = true).
    { simpl. exact Hrest_safe. }
    destruct
      (nullable_depth_safe_defined
        (S fuel) (EAlternative rest) Hrest_expr_safe)
      as [rest_value Hrest_defined].
    pose proof Hrest_defined as Hrest_local.
    simpl in Hrest_local.
    simpl.
    rewrite Hitem_true, Hrest_local.
    reflexivity.
  - simpl in Hsafe.
    apply andb_true_iff in Hsafe as [Hitem_safe Hrest_safe].
    destruct
      (nullable_depth_safe_defined fuel item Hitem_safe)
      as [item_value Hitem_defined].
    pose proof (IHrest Hrest_safe) as Hrest_true.
    pose proof Hrest_true as Hrest_local.
    simpl in Hrest_local.
    simpl.
    rewrite Hitem_defined, Hrest_local.
    destruct item_value; reflexivity.
Qed.

Lemma computed_nullable_sem_sound_step :
  forall fuel,
    (forall expression,
      ComputedNullableSem expression ->
      nullable_depth_safe_fuel fuel expression = true ->
      nullable_expression_fuel
        fuel phase1_surface_nullable_facts expression = Some true) ->
    forall expression,
      ComputedNullableSem expression ->
      nullable_depth_safe_fuel (S fuel) expression = true ->
      nullable_expression_fuel
        (S fuel) phase1_surface_nullable_facts expression = Some true.
Proof.
  intros fuel IH expression Hsem Hsafe.
  destruct Hsem as
    [name Hlookup
    | items Hitems
    | items Hitems
    | body
    | body].
  - simpl. rewrite Hlookup. reflexivity.
  - simpl in Hsafe.
    exact
      (computed_nullable_sequence_sem_sound
        fuel items IH Hitems Hsafe).
  - simpl in Hsafe.
    exact
      (computed_nullable_alternative_sem_sound
        fuel items IH Hitems Hsafe).
  - reflexivity.
  - reflexivity.
Qed.

Theorem computed_nullable_sem_sound :
  forall fuel expression,
    ComputedNullableSem expression ->
    nullable_depth_safe_fuel fuel expression = true ->
    nullable_expression_fuel
      fuel phase1_surface_nullable_facts expression = Some true.
Proof.
  induction fuel as [| fuel IH].
  - intros expression Hsem Hsafe.
    simpl in Hsafe. discriminate.
  - intros expression Hsem Hsafe.
    exact
      (computed_nullable_sem_sound_step
        fuel IH expression Hsem Hsafe).
Qed.

Lemma computed_nullable_sem_sound_at_expression_fuel :
  forall body,
    ComputedNullableSem body ->
    nullable_depth_safe_fuel expression_fuel body = true ->
    nullable_expression_fuel
      expression_fuel phase1_surface_nullable_facts body = Some true.
Proof.
  intros body Hsem Hsafe.
  exact
    (computed_nullable_sem_sound
      expression_fuel body Hsem Hsafe).
Qed.

Lemma nullable_expression_true_from_expression_fuel :
  forall body,
    nullable_expression_fuel
      expression_fuel phase1_surface_nullable_facts body = Some true ->
    nullable_expression phase1_surface_nullable_facts body = true.
Proof.
  intros body Heval.
  unfold nullable_expression.
  rewrite Heval.
  reflexivity.
Qed.

Lemma phase1_surface_nullable_lookup_true :
  forall name body,
    lookupRule name phase1_surface_rules = Some body ->
    nullable_expression phase1_surface_nullable_facts body = true ->
    lookup_bool name phase1_surface_nullable_facts = true.
Proof.
  intros name body Hlookup Hbody.
  rewrite
    (phase1_surface_nullable_lookup_rule name body Hlookup).
  exact Hbody.
Qed.

Lemma nullable_witness_nonterminal_sem_case :
  forall name body,
    lookupRule name phase1_surface_rules = Some body ->
    ComputedNullableSem body ->
    ComputedNullableSem (ENonterminal name).
Proof.
  intros name body Hlookup Hbody_sem.
  assert (Hbody_safe :
    nullable_depth_safe_fuel expression_fuel body = true).
  {
    apply phase1_surface_rule_body_nullable_depth_safe with name.
    exact Hlookup.
  }
  assert (Hlookup_true :
    lookup_bool name phase1_surface_nullable_facts = true).
  {
    apply phase1_surface_nullable_lookup_true with body.
    - exact Hlookup.
    - apply nullable_expression_true_from_expression_fuel.
      apply computed_nullable_sem_sound_at_expression_fuel.
      + exact Hbody_sem.
      + exact Hbody_safe.
  }
  exact (computed_nullable_nonterminal_sem name Hlookup_true).
Qed.

Theorem nullable_witness_implies_computed_sem :
  (forall expression,
    NullableWitness phase1_surface_rules expression ->
    ComputedNullableSem expression) /\
  (forall items,
    NullableSequenceWitness phase1_surface_rules items ->
    ComputedNullableSequenceSem items) /\
  (forall items,
    NullableAlternativeWitness phase1_surface_rules items ->
    ComputedNullableAlternativeSem items).
Proof.
  apply NullableWitness_mutind.
  - intros name body Hlookup Hbody IHbody.
    exact
      (nullable_witness_nonterminal_sem_case
        name body Hlookup IHbody).
  - intros items Hitems IHitems.
    now constructor.
  - intros items Hitems IHitems.
    now constructor.
  - intros body.
    constructor.
  - intros body.
    constructor.
  - constructor.
  - intros item rest Hitem IHitem Hrest IHrest.
    now constructor.
  - intros item rest Hitem IHitem.
    now constructor.
  - intros item rest Hrest IHrest.
    now constructor.
Qed.

Corollary nullable_witness_depth_sound :
  forall expression
    (witness : NullableWitness phase1_surface_rules expression)
    fuel,
    nullable_depth_safe_fuel fuel expression = true ->
    nullable_expression_fuel
      fuel phase1_surface_nullable_facts expression = Some true.
Proof.
  intros expression witness fuel Hsafe.
  pose proof
    ((proj1 nullable_witness_implies_computed_sem)
      expression witness)
    as Hsem.
  exact (computed_nullable_sem_sound fuel expression Hsem Hsafe).
Qed.

Theorem phase1_surface_nullable_witness_matches_computed_facts :
  forall expression,
    NullableWitness phase1_surface_rules expression ->
    choice_bodies_nonnullable_fuel
      expression_fuel expression = true ->
    nullable_expression
      phase1_surface_nullable_facts expression = true.
Proof.
  intros expression Hwitness Hchoice_safe.
  pose proof
    (choice_safe_implies_nullable_depth_safe
      expression_fuel expression Hchoice_safe)
    as Hdepth_safe.
  pose proof
    (nullable_witness_depth_sound
      expression Hwitness expression_fuel Hdepth_safe)
    as Hnullable.
  unfold nullable_expression.
  rewrite Hnullable.
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

Inductive ComputedFirstSem (token : OverlapToken)
  : EbnfExpression -> Prop :=
| computed_first_literal_sem :
    forall literal,
      token = OverlapLiteral literal ->
      ComputedFirstSem token (ELiteral literal)
| computed_first_lexical_sem :
    forall class_name,
      token = OverlapLexicalClass class_name ->
      ComputedFirstSem token (ELexicalClass class_name)
| computed_first_nonterminal_sem :
    forall name,
      token_mem token
        (lookup_tokens name phase1_surface_first_facts) = true ->
      ComputedFirstSem token (ENonterminal name)
| computed_first_sequence_sem :
    forall items,
      ComputedFirstSequenceSem token items ->
      ComputedFirstSem token (ESequence items)
| computed_first_alternative_sem :
    forall items,
      ComputedFirstAlternativeSem token items ->
      ComputedFirstSem token (EAlternative items)
| computed_first_optional_sem :
    forall body,
      ComputedFirstSem token body ->
      ComputedFirstSem token (EOptional body)
| computed_first_repetition_sem :
    forall body,
      ComputedFirstSem token body ->
      ComputedFirstSem token (ERepetition body)

with ComputedFirstSequenceSem (token : OverlapToken)
  : list EbnfExpression -> Prop :=
| computed_first_sequence_here_sem :
    forall item rest,
      ComputedFirstSem token item ->
      ComputedFirstSequenceSem token (item :: rest)
| computed_first_sequence_later_sem :
    forall item rest,
      ComputedNullableSem item ->
      ComputedFirstSequenceSem token rest ->
      ComputedFirstSequenceSem token (item :: rest)

with ComputedFirstAlternativeSem (token : OverlapToken)
  : list EbnfExpression -> Prop :=
| computed_first_alternative_here_sem :
    forall item rest,
      ComputedFirstSem token item ->
      ComputedFirstAlternativeSem token (item :: rest)
| computed_first_alternative_later_sem :
    forall item rest,
      ComputedFirstAlternativeSem token rest ->
      ComputedFirstAlternativeSem token (item :: rest).

Lemma computed_first_sequence_sem_sound :
  forall token fuel items,
    (forall expression,
      ComputedFirstSem token expression ->
      choice_bodies_nonnullable_fuel fuel expression = true ->
      exists tokens,
        first_expression_fuel
          fuel
          phase1_surface_nullable_facts
          phase1_surface_first_facts
          expression = Some tokens /\
        token_mem token tokens = true) ->
    ComputedFirstSequenceSem token items ->
    forallb (choice_bodies_nonnullable_fuel fuel) items = true ->
    exists tokens,
      first_expression_fuel
        (S fuel)
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        (ESequence items) = Some tokens /\
      token_mem token tokens = true.
Proof.
  intros token fuel items Hsound Hsem.
  induction Hsem as
    [item rest Hitem
    | item rest Hnullable Hrest IHrest]; intros Hsafe.
  - simpl in Hsafe.
    apply andb_true_iff in Hsafe as [Hitem_safe Hrest_safe].
    destruct (Hsound item Hitem Hitem_safe)
      as [item_first [Hitem_first Hitem_mem]].
    destruct (choice_safe_nullable_defined fuel item Hitem_safe)
      as [item_nullable Hitem_nullable].
    assert (Hrest_expr_safe :
      choice_bodies_nonnullable_fuel
        (S fuel) (ESequence rest) = true).
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
  - simpl in Hsafe.
    apply andb_true_iff in Hsafe as [Hitem_safe Hrest_safe].
    pose proof
      (choice_safe_implies_nullable_depth_safe
        fuel item Hitem_safe)
      as Hitem_depth_safe.
    pose proof
      (computed_nullable_sem_sound
        fuel item Hnullable Hitem_depth_safe)
      as Hitem_nullable.
    destruct (choice_safe_first_defined fuel item Hitem_safe)
      as [item_first Hitem_first].
    destruct (IHrest Hrest_safe)
      as [rest_first [Hrest_first Hrest_mem]].
    simpl in Hrest_first.
    simpl.
    rewrite Hitem_first, Hitem_nullable, Hrest_first.
    exists (token_union item_first rest_first). split.
    + reflexivity.
    + apply token_mem_union_right. exact Hrest_mem.
Qed.

Lemma computed_first_alternative_here_from_results :
  forall token fuel item rest item_first rest_first,
    first_expression_fuel
      fuel
      phase1_surface_nullable_facts
      phase1_surface_first_facts
      item = Some item_first ->
    token_mem token item_first = true ->
    first_expression_fuel
      (S fuel)
      phase1_surface_nullable_facts
      phase1_surface_first_facts
      (EAlternative rest) = Some rest_first ->
    exists tokens,
      first_expression_fuel
        (S fuel)
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        (EAlternative (item :: rest)) = Some tokens /\
      token_mem token tokens = true.
Proof.
  intros token fuel item rest item_first rest_first
    Hitem_first Hitem_mem Hrest_first.
  pose proof Hrest_first as Hrest_local.
  simpl in Hrest_local.
  simpl.
  rewrite Hitem_first, Hrest_local.
  exists (token_union item_first rest_first). split.
  - reflexivity.
  - apply token_mem_union_left. exact Hitem_mem.
Qed.

Lemma computed_first_alternative_later_from_results :
  forall token fuel item rest item_first rest_first,
    first_expression_fuel
      fuel
      phase1_surface_nullable_facts
      phase1_surface_first_facts
      item = Some item_first ->
    first_expression_fuel
      (S fuel)
      phase1_surface_nullable_facts
      phase1_surface_first_facts
      (EAlternative rest) = Some rest_first ->
    token_mem token rest_first = true ->
    exists tokens,
      first_expression_fuel
        (S fuel)
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        (EAlternative (item :: rest)) = Some tokens /\
      token_mem token tokens = true.
Proof.
  intros token fuel item rest item_first rest_first
    Hitem_first Hrest_first Hrest_mem.
  pose proof Hrest_first as Hrest_local.
  simpl in Hrest_local.
  simpl.
  rewrite Hitem_first, Hrest_local.
  exists (token_union item_first rest_first). split.
  - reflexivity.
  - apply token_mem_union_right. exact Hrest_mem.
Qed.

Lemma forallb_member_true :
  forall (A : Type) (predicate : A -> bool) items item,
    forallb predicate items = true ->
    In item items ->
    predicate item = true.
Proof.
  intros A predicate items.
  induction items as [| head rest IH]; intros item Hall Hin.
  - inversion Hin.
  - simpl in Hall.
    apply andb_true_iff in Hall as [Hhead Hrest].
    destruct Hin as [Heq | Hin].
    + subst item. exact Hhead.
    + eapply IH; eauto.
Qed.

Lemma computed_first_alternative_has_member :
  forall token items,
    ComputedFirstAlternativeSem token items ->
    exists item,
      In item items /\ ComputedFirstSem token item.
Proof.
  intros token items Hsem.
  induction Hsem as
    [item rest Hitem
    | item rest Hrest IHrest].
  - exists item. split.
    + left. reflexivity.
    + exact Hitem.
  - destruct IHrest as [selected [Hin Hselected]].
    exists selected. split.
    + right. exact Hin.
    + exact Hselected.
Qed.

Lemma computed_first_alternative_choices_defined :
  forall fuel items,
    forallb (choice_bodies_nonnullable_fuel fuel) items = true ->
    exists tokens,
      first_expression_fuel
        (S fuel)
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        (EAlternative items) = Some tokens.
Proof.
  intros fuel items Hsafe.
  exact
    (choice_safe_first_alternative_choices_defined
      fuel items (choice_safe_first_defined fuel) Hsafe).
Qed.

Lemma first_alternative_member_preserved :
  forall token fuel items selected selected_tokens,
    forallb (choice_bodies_nonnullable_fuel fuel) items = true ->
    In selected items ->
    first_expression_fuel
      fuel
      phase1_surface_nullable_facts
      phase1_surface_first_facts
      selected = Some selected_tokens ->
    token_mem token selected_tokens = true ->
    exists tokens,
      first_expression_fuel
        (S fuel)
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        (EAlternative items) = Some tokens /\
      token_mem token tokens = true.
Proof.
  intros token fuel items.
  induction items as [| head rest IH];
    intros selected selected_tokens Hsafe Hin Hselected Hmem.
  - inversion Hin.
  - simpl in Hsafe.
    apply andb_true_iff in Hsafe as [Hhead_safe Hrest_safe].
    destruct (choice_safe_first_defined fuel head Hhead_safe)
      as [head_tokens Hhead_first].
    destruct Hin as [Heq | Hin].
    + subst selected.
      rewrite Hselected in Hhead_first.
      inversion Hhead_first. subst head_tokens.
      destruct
        (computed_first_alternative_choices_defined
          fuel rest Hrest_safe)
        as [rest_tokens Hrest_first].
      exact
        (computed_first_alternative_here_from_results
          token fuel head rest selected_tokens rest_tokens
          Hselected Hmem Hrest_first).
    + destruct
        (IH selected selected_tokens Hrest_safe Hin Hselected Hmem)
        as [rest_tokens [Hrest_first Hrest_mem]].
      exact
        (computed_first_alternative_later_from_results
          token fuel head rest head_tokens rest_tokens
          Hhead_first Hrest_first Hrest_mem).
Qed.

Lemma computed_first_alternative_sem_sound :
  forall token fuel items,
    (forall expression,
      ComputedFirstSem token expression ->
      choice_bodies_nonnullable_fuel fuel expression = true ->
      exists tokens,
        first_expression_fuel
          fuel
          phase1_surface_nullable_facts
          phase1_surface_first_facts
          expression = Some tokens /\
        token_mem token tokens = true) ->
    ComputedFirstAlternativeSem token items ->
    forallb
      (fun item =>
        andb
          (negb
            (nullable_expression
              phase1_surface_nullable_facts item))
          (choice_bodies_nonnullable_fuel fuel item))
      items = true ->
    exists tokens,
      first_expression_fuel
        (S fuel)
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        (EAlternative items) = Some tokens /\
      token_mem token tokens = true.
Proof.
  intros token fuel items Hsound Hsem Hsafe.
  destruct (computed_first_alternative_has_member token items Hsem)
    as [selected [Hin Hselected_sem]].
  pose proof
    (forallb_andb_right
      EbnfExpression
      (fun item =>
        negb
          (nullable_expression phase1_surface_nullable_facts item))
      (choice_bodies_nonnullable_fuel fuel)
      items Hsafe)
    as Hbodies_safe.
  pose proof
    (forallb_member_true
      EbnfExpression
      (choice_bodies_nonnullable_fuel fuel)
      items selected Hbodies_safe Hin)
    as Hselected_safe.
  destruct (Hsound selected Hselected_sem Hselected_safe)
    as [selected_tokens [Hselected_first Hselected_mem]].
  exact
    (first_alternative_member_preserved
      token fuel items selected selected_tokens
      Hbodies_safe Hin Hselected_first Hselected_mem).
Qed.

Lemma computed_first_optional_result_lift :
  forall token fuel body,
    (exists tokens,
      first_expression_fuel
        fuel
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        body = Some tokens /\
      token_mem token tokens = true) ->
    exists tokens,
      first_expression_fuel
        (S fuel)
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        (EOptional body) = Some tokens /\
      token_mem token tokens = true.
Proof.
  intros token fuel body [tokens [Hfirst Hmem]].
  exists tokens. split.
  - simpl. exact Hfirst.
  - exact Hmem.
Qed.

Lemma computed_first_repetition_result_lift :
  forall token fuel body,
    (exists tokens,
      first_expression_fuel
        fuel
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        body = Some tokens /\
      token_mem token tokens = true) ->
    exists tokens,
      first_expression_fuel
        (S fuel)
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        (ERepetition body) = Some tokens /\
      token_mem token tokens = true.
Proof.
  intros token fuel body [tokens [Hfirst Hmem]].
  exists tokens. split.
  - simpl. exact Hfirst.
  - exact Hmem.
Qed.

Definition ComputedFirstFuelProperty
  (token : OverlapToken) (expression : EbnfExpression) : Prop :=
  forall fuel,
    choice_bodies_nonnullable_fuel fuel expression = true ->
    exists tokens,
      first_expression_fuel
        fuel
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        expression = Some tokens /\
      token_mem token tokens = true.

Definition ComputedFirstSequenceFuelProperty
  (token : OverlapToken) (items : list EbnfExpression) : Prop :=
  forall fuel,
    forallb (choice_bodies_nonnullable_fuel fuel) items = true ->
    exists tokens,
      first_expression_fuel
        (S fuel)
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        (ESequence items) = Some tokens /\
      token_mem token tokens = true.

Definition ComputedFirstAlternativeFuelProperty
  (token : OverlapToken) (items : list EbnfExpression) : Prop :=
  forall fuel,
    forallb
      (fun item =>
        andb
          (negb
            (nullable_expression phase1_surface_nullable_facts item))
          (choice_bodies_nonnullable_fuel fuel item))
      items = true ->
    exists tokens,
      first_expression_fuel
        (S fuel)
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        (EAlternative items) = Some tokens /\
      token_mem token tokens = true.

Scheme ComputedFirstSem_ind' := Induction for ComputedFirstSem Sort Prop
with ComputedFirstSequenceSem_ind' := Induction for ComputedFirstSequenceSem Sort Prop
with ComputedFirstAlternativeSem_ind' := Induction for ComputedFirstAlternativeSem Sort Prop.

Combined Scheme ComputedFirst_mutind
  from ComputedFirstSem_ind', ComputedFirstSequenceSem_ind',
       ComputedFirstAlternativeSem_ind'.

Lemma computed_first_literal_fuel_case :
  forall token literal,
    token = OverlapLiteral literal ->
    ComputedFirstFuelProperty token (ELiteral literal).
Proof.
  intros token literal Htoken.
  unfold ComputedFirstFuelProperty.
  intros fuel Hsafe.
  destruct fuel as [| fuel].
  - simpl in Hsafe. discriminate.
  - subst token.
    exists [OverlapLiteral literal]. split.
    + reflexivity.
    + unfold token_mem.
      rewrite overlap_token_eqb_refl.
      reflexivity.
Qed.

Lemma computed_first_lexical_fuel_case :
  forall token class_name,
    token = OverlapLexicalClass class_name ->
    ComputedFirstFuelProperty token (ELexicalClass class_name).
Proof.
  intros token class_name Htoken.
  unfold ComputedFirstFuelProperty.
  intros fuel Hsafe.
  destruct fuel as [| fuel].
  - simpl in Hsafe. discriminate.
  - subst token.
    exists [OverlapLexicalClass class_name]. split.
    + reflexivity.
    + unfold token_mem.
      rewrite overlap_token_eqb_refl.
      reflexivity.
Qed.

Lemma computed_first_nonterminal_fuel_case :
  forall token name,
    token_mem token
      (lookup_tokens name phase1_surface_first_facts) = true ->
    ComputedFirstFuelProperty token (ENonterminal name).
Proof.
  intros token name Hmem.
  unfold ComputedFirstFuelProperty.
  intros fuel Hsafe.
  destruct fuel as [| fuel].
  - simpl in Hsafe. discriminate.
  - exists (lookup_tokens name phase1_surface_first_facts). split.
    + reflexivity.
    + exact Hmem.
Qed.

Lemma computed_first_sequence_expression_fuel_case :
  forall token items,
    ComputedFirstSequenceFuelProperty token items ->
    ComputedFirstFuelProperty token (ESequence items).
Proof.
  intros token items IHitems.
  unfold ComputedFirstFuelProperty, ComputedFirstSequenceFuelProperty in *.
  intros fuel Hsafe.
  destruct fuel as [| fuel].
  - simpl in Hsafe. discriminate.
  - simpl in Hsafe.
    exact (IHitems fuel Hsafe).
Qed.

Lemma computed_first_alternative_expression_fuel_case :
  forall token items,
    ComputedFirstAlternativeFuelProperty token items ->
    ComputedFirstFuelProperty token (EAlternative items).
Proof.
  intros token items IHitems.
  unfold ComputedFirstFuelProperty, ComputedFirstAlternativeFuelProperty in *.
  intros fuel Hsafe.
  destruct fuel as [| fuel].
  - simpl in Hsafe. discriminate.
  - simpl in Hsafe.
    exact (IHitems fuel Hsafe).
Qed.

Lemma computed_first_fuel_property_intro :
  forall token expression,
    (forall fuel,
      choice_bodies_nonnullable_fuel fuel expression = true ->
      exists tokens,
        first_expression_fuel
          fuel
          phase1_surface_nullable_facts
          phase1_surface_first_facts
          expression = Some tokens /\
        token_mem token tokens = true) ->
    ComputedFirstFuelProperty token expression.
Proof.
  intros token expression Hproperty.
  unfold ComputedFirstFuelProperty.
  exact Hproperty.
Qed.

Lemma computed_first_fuel_property_result :
  forall token expression fuel,
    ComputedFirstFuelProperty token expression ->
    choice_bodies_nonnullable_fuel fuel expression = true ->
    exists tokens,
      first_expression_fuel
        fuel
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        expression = Some tokens /\
      token_mem token tokens = true.
Proof.
  intros token expression fuel Hproperty Hsafe.
  unfold ComputedFirstFuelProperty in Hproperty.
  exact (Hproperty fuel Hsafe).
Qed.

Lemma computed_first_optional_zero_not_safe :
  forall body,
    choice_bodies_nonnullable_fuel 0 (EOptional body) = true -> False.
Proof.
  intros body Hsafe.
  simpl in Hsafe.
  discriminate.
Qed.

Lemma choice_bodies_nonnullable_optional_step :
  forall fuel body,
    choice_bodies_nonnullable_fuel (S fuel) (EOptional body) =
    andb
      (negb (nullable_expression phase1_surface_nullable_facts body))
      (choice_bodies_nonnullable_fuel fuel body).
Proof.
  reflexivity.
Qed.

Lemma computed_first_optional_body_safe :
  forall fuel body,
    choice_bodies_nonnullable_fuel (S fuel) (EOptional body) = true ->
    choice_bodies_nonnullable_fuel fuel body = true.
Proof.
  intros fuel body Hsafe.
  rewrite choice_bodies_nonnullable_optional_step in Hsafe.
  apply andb_true_iff in Hsafe as [_ Hbody_safe].
  exact Hbody_safe.
Qed.

Opaque ComputedFirstFuelProperty.

Lemma computed_first_optional_fuel_case :
  forall token body,
    ComputedFirstFuelProperty token body ->
    ComputedFirstFuelProperty token (EOptional body).
Proof.
  intros token body IHbody.
  apply computed_first_fuel_property_intro.
  intros fuel Hsafe.
  destruct fuel as [| fuel].
  - exfalso.
    exact (computed_first_optional_zero_not_safe body Hsafe).
  - exact
      (computed_first_optional_result_lift
        token fuel body
        (computed_first_fuel_property_result
          token body fuel IHbody
          (computed_first_optional_body_safe fuel body Hsafe))).
Qed.

Lemma computed_first_repetition_zero_not_safe :
  forall body,
    choice_bodies_nonnullable_fuel 0 (ERepetition body) = true -> False.
Proof.
  intros body Hsafe.
  simpl in Hsafe.
  discriminate.
Qed.

Lemma choice_bodies_nonnullable_repetition_step :
  forall fuel body,
    choice_bodies_nonnullable_fuel (S fuel) (ERepetition body) =
    andb
      (negb (nullable_expression phase1_surface_nullable_facts body))
      (choice_bodies_nonnullable_fuel fuel body).
Proof.
  reflexivity.
Qed.

Lemma computed_first_repetition_body_safe :
  forall fuel body,
    choice_bodies_nonnullable_fuel (S fuel) (ERepetition body) = true ->
    choice_bodies_nonnullable_fuel fuel body = true.
Proof.
  intros fuel body Hsafe.
  rewrite choice_bodies_nonnullable_repetition_step in Hsafe.
  apply andb_true_iff in Hsafe as [_ Hbody_safe].
  exact Hbody_safe.
Qed.

Lemma computed_first_repetition_fuel_case :
  forall token body,
    ComputedFirstFuelProperty token body ->
    ComputedFirstFuelProperty token (ERepetition body).
Proof.
  intros token body IHbody.
  apply computed_first_fuel_property_intro.
  intros fuel Hsafe.
  destruct fuel as [| fuel].
  - exfalso.
    exact (computed_first_repetition_zero_not_safe body Hsafe).
  - exact
      (computed_first_repetition_result_lift
        token fuel body
        (computed_first_fuel_property_result
          token body fuel IHbody
          (computed_first_repetition_body_safe fuel body Hsafe))).
Qed.

Transparent ComputedFirstFuelProperty.

Lemma computed_first_sequence_here_fuel_case :
  forall token item rest,
    ComputedFirstFuelProperty token item ->
    ComputedFirstSequenceFuelProperty token (item :: rest).
Proof.
  intros token item rest IHitem.
  unfold ComputedFirstSequenceFuelProperty in *.
  intros fuel Hsafe.
  simpl in Hsafe.
  apply andb_true_iff in Hsafe as [Hitem_safe Hrest_safe].
  destruct (IHitem fuel Hitem_safe)
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
  - rewrite Hrest_first.
    exists (token_union item_first rest_first). split.
    + reflexivity.
    + apply token_mem_union_left. exact Hitem_mem.
  - exists item_first. split; [reflexivity | exact Hitem_mem].
Qed.

Lemma computed_first_sequence_later_fuel_case :
  forall token item rest,
    ComputedNullableSem item ->
    ComputedFirstSequenceFuelProperty token rest ->
    ComputedFirstSequenceFuelProperty token (item :: rest).
Proof.
  intros token item rest Hnullable IHrest.
  unfold ComputedFirstSequenceFuelProperty in *.
  intros fuel Hsafe.
  simpl in Hsafe.
  apply andb_true_iff in Hsafe as [Hitem_safe Hrest_safe].
  pose proof
    (choice_safe_implies_nullable_depth_safe
      fuel item Hitem_safe)
    as Hitem_depth_safe.
  pose proof
    (computed_nullable_sem_sound
      fuel item Hnullable Hitem_depth_safe)
    as Hitem_nullable.
  destruct (choice_safe_first_defined fuel item Hitem_safe)
    as [item_first Hitem_first].
  destruct (IHrest fuel Hrest_safe)
    as [rest_first [Hrest_first Hrest_mem]].
  simpl in Hrest_first.
  simpl.
  rewrite Hitem_first, Hitem_nullable, Hrest_first.
  exists (token_union item_first rest_first). split.
  - reflexivity.
  - apply token_mem_union_right. exact Hrest_mem.
Qed.

Lemma computed_first_forallb_cons_step :
  forall (A : Type) (predicate : A -> bool) item rest,
    forallb predicate (item :: rest) =
    andb (predicate item) (forallb predicate rest).
Proof.
  reflexivity.
Qed.

Lemma choice_bodies_nonnullable_alternative_step :
  forall fuel items,
    choice_bodies_nonnullable_fuel (S fuel) (EAlternative items) =
    forallb
      (fun item =>
        andb
          (negb
            (nullable_expression phase1_surface_nullable_facts item))
          (choice_bodies_nonnullable_fuel fuel item))
      items.
Proof.
  reflexivity.
Qed.

Lemma computed_first_alternative_here_fuel_case :
  forall token item rest,
    ComputedFirstFuelProperty token item ->
    ComputedFirstAlternativeFuelProperty token (item :: rest).
Proof.
  intros token item rest IHitem.
  unfold ComputedFirstAlternativeFuelProperty.
  intros fuel Hsafe.
  rewrite computed_first_forallb_cons_step in Hsafe.
  apply andb_true_iff in Hsafe as [Hhead_safe Hrest_safe].
  apply andb_true_iff in Hhead_safe as [_ Hitem_safe].
  destruct (IHitem fuel Hitem_safe)
    as [item_first [Hitem_first Hitem_mem]].
  assert (Hrest_expr_safe :
    choice_bodies_nonnullable_fuel (S fuel) (EAlternative rest) = true).
  {
    rewrite choice_bodies_nonnullable_alternative_step.
    exact Hrest_safe.
  }
  destruct
    (choice_safe_first_defined
      (S fuel) (EAlternative rest) Hrest_expr_safe)
    as [rest_first Hrest_first].
  exact
    (computed_first_alternative_here_from_results
      token fuel item rest item_first rest_first
      Hitem_first Hitem_mem Hrest_first).
Qed.

Lemma computed_first_alternative_later_fuel_case :
  forall token item rest,
    ComputedFirstAlternativeFuelProperty token rest ->
    ComputedFirstAlternativeFuelProperty token (item :: rest).
Proof.
  intros token item rest IHrest.
  unfold ComputedFirstAlternativeFuelProperty.
  intros fuel Hsafe.
  rewrite computed_first_forallb_cons_step in Hsafe.
  apply andb_true_iff in Hsafe as [Hhead_safe Hrest_safe].
  apply andb_true_iff in Hhead_safe as [_ Hitem_safe].
  destruct (choice_safe_first_defined fuel item Hitem_safe)
    as [item_first Hitem_first].
  destruct (IHrest fuel Hrest_safe)
    as [rest_first [Hrest_first Hrest_mem]].
  exact
    (computed_first_alternative_later_from_results
      token fuel item rest item_first rest_first
      Hitem_first Hrest_first Hrest_mem).
Qed.

Theorem computed_first_sem_sound_mutual :
  forall token,
    (forall expression (witness : ComputedFirstSem token expression),
      ComputedFirstFuelProperty token expression) /\
    (forall items (witness : ComputedFirstSequenceSem token items),
      ComputedFirstSequenceFuelProperty token items) /\
    (forall items (witness : ComputedFirstAlternativeSem token items),
      ComputedFirstAlternativeFuelProperty token items).
Proof.
  intro token.
  apply ComputedFirst_mutind.
  - intros literal Htoken.
    eapply computed_first_literal_fuel_case.
    exact Htoken.
  - intros class_name Htoken.
    eapply computed_first_lexical_fuel_case.
    exact Htoken.
  - intros name Hmem.
    eapply computed_first_nonterminal_fuel_case.
    exact Hmem.
  - intros items Hitems IHitems.
    eapply computed_first_sequence_expression_fuel_case.
    exact IHitems.
  - intros items Hitems IHitems.
    eapply computed_first_alternative_expression_fuel_case.
    exact IHitems.
  - intros body Hbody IHbody.
    eapply computed_first_optional_fuel_case.
    exact IHbody.
  - intros body Hbody IHbody.
    eapply computed_first_repetition_fuel_case.
    exact IHbody.
  - intros item rest Hitem IHitem.
    eapply computed_first_sequence_here_fuel_case.
    exact IHitem.
  - intros item rest Hnullable Hrest IHrest.
    eapply computed_first_sequence_later_fuel_case.
    + exact Hnullable.
    + exact IHrest.
  - intros item rest Hitem IHitem.
    eapply computed_first_alternative_here_fuel_case.
    exact IHitem.
  - intros item rest Hrest IHrest.
    eapply computed_first_alternative_later_fuel_case.
    exact IHrest.
Qed.

Theorem computed_first_sem_sound :
  forall token fuel expression,
    ComputedFirstSem token expression ->
    choice_bodies_nonnullable_fuel fuel expression = true ->
    exists tokens,
      first_expression_fuel
        fuel
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        expression = Some tokens /\
      token_mem token tokens = true.
Proof.
  intros token fuel expression Hsem Hsafe.
  exact
    (proj1 (computed_first_sem_sound_mutual token)
      expression Hsem fuel Hsafe).
Qed.

Lemma computed_first_sem_sound_at_expression_fuel :
  forall token body,
    ComputedFirstSem token body ->
    choice_bodies_nonnullable_fuel expression_fuel body = true ->
    exists tokens,
      first_expression_fuel
        expression_fuel
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        body = Some tokens /\
      token_mem token tokens = true.
Proof.
  intros token body Hsem Hsafe.
  exact
    (computed_first_sem_sound
      token expression_fuel body Hsem Hsafe).
Qed.

Lemma first_expression_fuel_result_eq :
  forall nullable_facts first_facts expression tokens,
    first_expression_fuel
      expression_fuel nullable_facts first_facts expression = Some tokens ->
    first_expression nullable_facts first_facts expression = tokens.
Proof.
  intros nullable_facts first_facts expression tokens Hfirst.
  unfold first_expression.
  rewrite Hfirst.
  reflexivity.
Qed.

Lemma token_mem_eq_transport :
  forall token left right,
    left = right ->
    token_mem token right = true ->
    token_mem token left = true.
Proof.
  intros token left right Heq Hmem.
  rewrite Heq.
  exact Hmem.
Qed.

Lemma phase1_surface_first_lookup_mem :
  forall token name body tokens,
    lookupRule name phase1_surface_rules = Some body ->
    first_expression_fuel
      expression_fuel
      phase1_surface_nullable_facts
      phase1_surface_first_facts
      body = Some tokens ->
    token_mem token tokens = true ->
    token_mem token
      (lookup_tokens name phase1_surface_first_facts) = true.
Proof.
  intros token name body tokens Hlookup Hbody_first Hmem.
  eapply token_mem_eq_transport.
  - eapply eq_trans.
    + exact (phase1_surface_first_lookup_rule name body Hlookup).
    + exact
        (first_expression_fuel_result_eq
          phase1_surface_nullable_facts
          phase1_surface_first_facts
          body tokens Hbody_first).
  - exact Hmem.
Qed.

Lemma first_witness_nonterminal_sem_case :
  forall token name body,
    lookupRule name phase1_surface_rules = Some body ->
    ComputedFirstSem token body ->
    ComputedFirstSem token (ENonterminal name).
Proof.
  intros token name body Hlookup Hbody_sem.
  assert (Hbody_safe :
    choice_bodies_nonnullable_fuel expression_fuel body = true).
  {
    apply phase1_surface_rule_body_choice_safe with name.
    exact Hlookup.
  }
  destruct
    (computed_first_sem_sound_at_expression_fuel
      token body Hbody_sem Hbody_safe)
    as [tokens [Hbody_first Hbody_mem]].
  apply computed_first_nonterminal_sem.
  eapply phase1_surface_first_lookup_mem.
  - exact Hlookup.
  - exact Hbody_first.
  - exact Hbody_mem.
Qed.

Theorem first_witness_implies_computed_sem_for_token :
  forall token,
  (forall expression,
    FirstWitness phase1_surface_rules token expression ->
    ComputedFirstSem token expression) /\
  (forall items,
    FirstSequenceWitness phase1_surface_rules token items ->
    ComputedFirstSequenceSem token items) /\
  (forall items,
    FirstAlternativeWitness phase1_surface_rules token items ->
    ComputedFirstAlternativeSem token items).
Proof.
  intros token.
  apply FirstWitness_mutind.
  - intros literal Htoken.
    apply computed_first_literal_sem.
    exact Htoken.
  - intros class_name Htoken.
    apply computed_first_lexical_sem.
    exact Htoken.
  - intros name body Hlookup Hbody IHbody.
    exact
      (first_witness_nonterminal_sem_case
        token name body Hlookup IHbody).
  - intros items Hitems IHitems.
    apply computed_first_sequence_sem.
    exact IHitems.
  - intros items Hitems IHitems.
    apply computed_first_alternative_sem.
    exact IHitems.
  - intros body Hbody IHbody.
    apply computed_first_optional_sem.
    exact IHbody.
  - intros body Hbody IHbody.
    apply computed_first_repetition_sem.
    exact IHbody.
  - intros item rest Hitem IHitem.
    apply computed_first_sequence_here_sem.
    exact IHitem.
  - intros item rest Hnullable Hrest IHrest.
    apply computed_first_sequence_later_sem.
    + exact
        ((proj1 nullable_witness_implies_computed_sem)
          item Hnullable).
    + exact IHrest.
  - intros item rest Hitem IHitem.
    apply computed_first_alternative_here_sem.
    exact IHitem.
  - intros item rest Hrest IHrest.
    apply computed_first_alternative_later_sem.
    exact IHrest.
Qed.

Lemma computed_first_sem_fuel_property :
  forall token expression,
    ComputedFirstSem token expression ->
    FirstWitnessFuelProperty token expression.
Proof.
  intros token expression Hsem.
  unfold FirstWitnessFuelProperty.
  intros fuel Hfuel Hsafe.
  exact
    (computed_first_sem_sound
      token fuel expression Hsem Hsafe).
Qed.

Lemma computed_first_sequence_sem_fuel_property :
  forall token items,
    ComputedFirstSequenceSem token items ->
    FirstSequenceFuelProperty token items.
Proof.
  intros token items Hsem.
  unfold FirstSequenceFuelProperty.
  intros fuel Hfuel Hsafe.
  exact
    (computed_first_sequence_sem_sound
      token fuel items
      (computed_first_sem_sound token fuel)
      Hsem Hsafe).
Qed.

Lemma computed_first_alternative_sem_fuel_property :
  forall token items,
    ComputedFirstAlternativeSem token items ->
    FirstAlternativeFuelProperty token items.
Proof.
  intros token items Hsem.
  unfold FirstAlternativeFuelProperty.
  intros fuel Hfuel Hsafe.
  exact
    (computed_first_alternative_sem_sound
      token fuel items
      (computed_first_sem_sound token fuel)
      Hsem Hsafe).
Qed.

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
  split.
  - intros token expression Hfirst.
    apply computed_first_sem_fuel_property.
    exact
      ((proj1
        (first_witness_implies_computed_sem_for_token token))
        expression Hfirst).
  - split.
    + intros token items Hfirst.
      apply computed_first_sequence_sem_fuel_property.
      exact
        ((proj1 (proj2
          (first_witness_implies_computed_sem_for_token token)))
          items Hfirst).
    + intros token items Hfirst.
      apply computed_first_alternative_sem_fuel_property.
      exact
        ((proj2 (proj2
          (first_witness_implies_computed_sem_for_token token)))
          items Hfirst).
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
