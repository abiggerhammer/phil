From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Strings.String Lia.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyNullableFirst
  GrammarDeterminacyPredictiveOracle
  GrammarDeterminacyWitnessSoundness
  GrammarDeterminacyContinuationSoundness
  GrammarDeterminacyPredictiveBridge
  GrammarParserGoalRank
  GrammarParserGlobalGoalRank.

Import ListNotations.
Open Scope string_scope.

(*
  Static interface for the concrete total-fuel proof.

  GrammarParserGlobalGoalRank.v already contains the exact finite collection of
  every expression, sequence-suffix, and repetition rank option reachable in
  Grammar v1.  This file gives the runtime derivation goals a public view onto
  that collection and proves that every recursive child remains inside it.

  Choice-body safety is exposed to the total-fuel induction through a structural
  Prop-valued certificate.  The executable boolean remains the checked source
  of truth at the boundary, but recursive theorem statements no longer carry
  reflected computations.  Nonterminal expansion is the one reset edge: it
  returns to expression_fuel and obtains both certificates from the exact rule
  tables.
*)

Fixpoint parser_sequence_goal_rank_options_fuel
  (fuel : nat)
  (facts : list (string * nat))
  (items : list EbnfExpression) : list (option nat) :=
  match items with
  | [] => [parser_sequence_goal_rank_fuel fuel facts []]
  | item :: rest =>
      parser_sequence_goal_rank_fuel fuel facts (item :: rest) ::
      List.app
        (parser_expression_goal_rank_options_fuel fuel facts item)
        (parser_sequence_goal_rank_options_fuel fuel facts rest)
  end.

Fixpoint parser_alternative_member_rank_options_fuel
  (fuel : nat)
  (facts : list (string * nat))
  (items : list EbnfExpression) : list (option nat) :=
  match items with
  | [] => []
  | item :: rest =>
      List.app
        (parser_expression_goal_rank_options_fuel fuel facts item)
        (parser_alternative_member_rank_options_fuel fuel facts rest)
  end.

Definition parser_repetition_goal_rank_options_fuel
  (fuel : nat)
  (facts : list (string * nat))
  (body : EbnfExpression) : list (option nat) :=
  parser_repetition_goal_rank_fuel fuel facts body ::
  parser_expression_goal_rank_options_fuel fuel facts body.

Definition phase1_surface_parser_goal_rank_options_fuel
  (fuel : nat)
  (goal : DerivationGoal) : list (option nat) :=
  match goal with
  | GoalExpression _ expression =>
      parser_expression_goal_rank_options_fuel
        fuel phase1_surface_parser_rank_facts expression
  | GoalSequence _ _ items =>
      parser_sequence_goal_rank_options_fuel
        fuel phase1_surface_parser_rank_facts items
  | GoalRepetition _ body =>
      parser_repetition_goal_rank_options_fuel
        fuel phase1_surface_parser_rank_facts body
  end.

Definition phase1_surface_parser_goal_rank_fuel
  (fuel : nat)
  (goal : DerivationGoal) : option nat :=
  match goal with
  | GoalExpression _ expression =>
      parser_expression_rank_fuel
        fuel phase1_surface_parser_rank_facts expression
  | GoalSequence _ _ items =>
      parser_sequence_goal_rank_fuel
        fuel phase1_surface_parser_rank_facts items
  | GoalRepetition _ body =>
      parser_repetition_goal_rank_fuel
        fuel phase1_surface_parser_rank_facts body
  end.

Definition phase1_surface_parser_goal_options_global
  (fuel : nat)
  (goal : DerivationGoal) : Prop :=
  forall value,
    In value (phase1_surface_parser_goal_rank_options_fuel fuel goal) ->
    In value phase1_surface_parser_all_goal_rank_options.

Definition phase1_surface_parser_goal_choice_safeb
  (fuel : nat)
  (goal : DerivationGoal) : bool :=
  match goal with
  | GoalExpression _ expression =>
      choice_bodies_nonnullable_fuel fuel expression
  | GoalSequence _ _ items =>
      forallb (choice_bodies_nonnullable_fuel fuel) items
  | GoalRepetition _ body =>
      choice_bodies_nonnullable_fuel fuel body
  end.

Fixpoint phase1_surface_expression_choice_safe
  (fuel : nat)
  (expression : EbnfExpression) : Prop :=
  match fuel with
  | O => False
  | S remaining =>
      match expression with
      | ELiteral _ => True
      | ELexicalClass _ => True
      | ENonterminal _ => True
      | ESequence items =>
          Forall (phase1_surface_expression_choice_safe remaining) items
      | EAlternative items =>
          Forall
            (fun item =>
              nullable_expression phase1_surface_nullable_facts item = false /\
              phase1_surface_expression_choice_safe remaining item)
            items
      | EOptional body =>
          nullable_expression phase1_surface_nullable_facts body = false /\
          phase1_surface_expression_choice_safe remaining body
      | ERepetition body =>
          nullable_expression phase1_surface_nullable_facts body = false /\
          phase1_surface_expression_choice_safe remaining body
      end
  end.

Definition phase1_surface_parser_goal_choice_safe_structural
  (fuel : nat)
  (goal : DerivationGoal) : Prop :=
  match goal with
  | GoalExpression _ expression =>
      phase1_surface_expression_choice_safe fuel expression
  | GoalSequence _ _ items =>
      Forall (phase1_surface_expression_choice_safe fuel) items
  | GoalRepetition _ body =>
      phase1_surface_expression_choice_safe fuel body
  end.

Inductive phase1_surface_parser_goal_choice_safe
  (fuel : nat)
  (goal : DerivationGoal) : Prop :=
| Phase1SurfaceParserGoalChoiceSafe :
    phase1_surface_parser_goal_choice_safe_structural fuel goal ->
    phase1_surface_parser_goal_choice_safe fuel goal.

Lemma phase1_surface_expression_choice_safe_of_bool :
  forall fuel expression,
    choice_bodies_nonnullable_fuel fuel expression = true ->
    phase1_surface_expression_choice_safe fuel expression.
Proof.
  induction fuel as [| fuel IH]; intros expression Hsafe.
  - simpl in Hsafe. discriminate.
  - destruct expression as
      [literal | class_name | name | items | items | body | body].
    + exact I.
    + exact I.
    + exact I.
    + rewrite continuation_choice_bodies_nonnullable_sequence_step in Hsafe.
      rewrite forallb_forall in Hsafe.
      apply Forall_forall.
      intros item Hin.
      apply IH.
      exact (Hsafe item Hin).
    + rewrite choice_bodies_nonnullable_alternative_step in Hsafe.
      rewrite forallb_forall in Hsafe.
      apply Forall_forall.
      intros item Hin.
      pose proof (Hsafe item Hin) as Hitem.
      apply andb_true_iff in Hitem as [Hnonnullable Hchild].
      apply negb_true_iff in Hnonnullable.
      split.
      * exact Hnonnullable.
      * apply IH. exact Hchild.
    + rewrite choice_safe_first_optional_safety_equation in Hsafe.
      apply andb_true_iff in Hsafe as [Hnonnullable Hchild].
      apply negb_true_iff in Hnonnullable.
      split.
      * exact Hnonnullable.
      * apply IH. exact Hchild.
    + rewrite choice_safe_first_repetition_safety_equation in Hsafe.
      apply andb_true_iff in Hsafe as [Hnonnullable Hchild].
      apply negb_true_iff in Hnonnullable.
      split.
      * exact Hnonnullable.
      * apply IH. exact Hchild.
Qed.

Lemma phase1_surface_expression_choice_safe_bool :
  forall fuel expression,
    phase1_surface_expression_choice_safe fuel expression ->
    choice_bodies_nonnullable_fuel fuel expression = true.
Proof.
  induction fuel as [| fuel IH]; intros expression Hsafe.
  - contradiction.
  - destruct expression as
      [literal | class_name | name | items | items | body | body].
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + rewrite continuation_choice_bodies_nonnullable_sequence_step.
      apply forallb_forall.
      intros item Hin.
      change
        (Forall (phase1_surface_expression_choice_safe fuel) items)
        in Hsafe.
      apply Forall_forall in Hsafe.
      apply IH.
      exact (Hsafe item Hin).
    + rewrite choice_bodies_nonnullable_alternative_step.
      apply forallb_forall.
      intros item Hin.
      change
        (Forall
          (fun candidate =>
            nullable_expression
              phase1_surface_nullable_facts candidate = false /\
            phase1_surface_expression_choice_safe fuel candidate)
          items)
        in Hsafe.
      apply Forall_forall in Hsafe.
      specialize (Hsafe item Hin).
      destruct Hsafe as [Hnonnullable Hchild].
      apply andb_true_iff.
      split.
      * apply negb_true_iff. exact Hnonnullable.
      * apply IH. exact Hchild.
    + rewrite choice_safe_first_optional_safety_equation.
      destruct Hsafe as [Hnonnullable Hchild].
      apply andb_true_iff.
      split.
      * apply negb_true_iff. exact Hnonnullable.
      * apply IH. exact Hchild.
    + rewrite choice_safe_first_repetition_safety_equation.
      destruct Hsafe as [Hnonnullable Hchild].
      apply andb_true_iff.
      split.
      * apply negb_true_iff. exact Hnonnullable.
      * apply IH. exact Hchild.
Qed.

Lemma phase1_surface_parser_goal_choice_safe_bool :
  forall fuel goal,
    phase1_surface_parser_goal_choice_safe fuel goal ->
    phase1_surface_parser_goal_choice_safeb fuel goal = true.
Proof.
  intros fuel goal Hsafe.
  destruct Hsafe as [Hsafe].
  destruct goal as [path expression | path index items | path body].
  - unfold phase1_surface_parser_goal_choice_safe_structural in Hsafe.
    unfold phase1_surface_parser_goal_choice_safeb.
    apply phase1_surface_expression_choice_safe_bool.
    exact Hsafe.
  - unfold phase1_surface_parser_goal_choice_safe_structural in Hsafe.
    unfold phase1_surface_parser_goal_choice_safeb.
    apply forallb_forall.
    rewrite Forall_forall in Hsafe.
    intros item Hin.
    apply phase1_surface_expression_choice_safe_bool.
    exact (Hsafe item Hin).
  - unfold phase1_surface_parser_goal_choice_safe_structural in Hsafe.
    unfold phase1_surface_parser_goal_choice_safeb.
    apply phase1_surface_expression_choice_safe_bool.
    exact Hsafe.
Qed.

Lemma phase1_surface_expression_goal_choice_safe_bool :
  forall fuel path expression,
    phase1_surface_parser_goal_choice_safe
      fuel (GoalExpression path expression) ->
    choice_bodies_nonnullable_fuel fuel expression = true.
Proof.
  intros fuel path expression Hsafe.
  pose proof
    (phase1_surface_parser_goal_choice_safe_bool
      fuel (GoalExpression path expression) Hsafe) as Hbool.
  exact Hbool.
Qed.

Lemma parser_expression_sequence_goal_rank_options_equation :
  forall fuel facts items,
    parser_expression_goal_rank_options_fuel
      (S fuel) facts (ESequence items) =
    parser_expression_rank_fuel (S fuel) facts (ESequence items) ::
    parser_sequence_goal_rank_options_fuel fuel facts items.
Proof.
  intros fuel facts items.
  induction items as [| item rest IH].
  - reflexivity.
  - simpl.
    pose proof (f_equal (@List.tl (option nat)) IH) as Htail.
    simpl in Htail.
    rewrite Htail.
    reflexivity.
Qed.

Lemma parser_expression_alternative_goal_rank_options_equation :
  forall fuel facts items,
    parser_expression_goal_rank_options_fuel
      (S fuel) facts (EAlternative items) =
    parser_expression_rank_fuel (S fuel) facts (EAlternative items) ::
    parser_alternative_member_rank_options_fuel fuel facts items.
Proof.
  intros fuel facts items.
  induction items as [| item rest IH].
  - reflexivity.
  - simpl.
    pose proof (f_equal (@List.tl (option nat)) IH) as Htail.
    simpl in Htail.
    rewrite Htail.
    reflexivity.
Qed.

Lemma parser_expression_optional_goal_rank_options_equation :
  forall fuel facts body,
    parser_expression_goal_rank_options_fuel
      (S fuel) facts (EOptional body) =
    parser_expression_rank_fuel (S fuel) facts (EOptional body) ::
    parser_expression_goal_rank_options_fuel fuel facts body.
Proof.
  reflexivity.
Qed.

Lemma parser_expression_repetition_goal_rank_options_equation :
  forall fuel facts body,
    parser_expression_goal_rank_options_fuel
      (S fuel) facts (ERepetition body) =
    parser_expression_rank_fuel (S fuel) facts (ERepetition body) ::
    parser_repetition_goal_rank_options_fuel fuel facts body.
Proof.
  reflexivity.
Qed.

Lemma parser_expression_rank_option_is_collected :
  forall fuel facts expression,
    In
      (parser_expression_rank_fuel fuel facts expression)
      (parser_expression_goal_rank_options_fuel fuel facts expression).
Proof.
  intros fuel facts expression.
  destruct fuel; simpl; auto.
Qed.

Lemma phase1_surface_parser_goal_rank_option_is_collected :
  forall fuel goal,
    In
      (phase1_surface_parser_goal_rank_fuel fuel goal)
      (phase1_surface_parser_goal_rank_options_fuel fuel goal).
Proof.
  intros fuel goal.
  destruct goal as [path expression | path index items | path body].
  - simpl. apply parser_expression_rank_option_is_collected.
  - simpl. destruct items as [| item rest]; simpl; auto.
  - simpl. auto.
Qed.

Lemma parser_sequence_goal_options_head_subset :
  forall fuel facts item rest value,
    In value
      (parser_expression_goal_rank_options_fuel fuel facts item) ->
    In value
      (parser_sequence_goal_rank_options_fuel fuel facts (item :: rest)).
Proof.
  intros fuel facts item rest value Hin.
  simpl.
  right.
  apply in_or_app.
  left.
  exact Hin.
Qed.

Lemma parser_sequence_goal_options_tail_subset :
  forall fuel facts item rest value,
    In value
      (parser_sequence_goal_rank_options_fuel fuel facts rest) ->
    In value
      (parser_sequence_goal_rank_options_fuel fuel facts (item :: rest)).
Proof.
  intros fuel facts item rest value Hin.
  simpl.
  right.
  apply in_or_app.
  right.
  exact Hin.
Qed.

Lemma parser_alternative_member_rank_options_subset :
  forall fuel facts items index item value,
    nth_error items index = Some item ->
    In value
      (parser_expression_goal_rank_options_fuel fuel facts item) ->
    In value
      (parser_alternative_member_rank_options_fuel fuel facts items).
Proof.
  intros fuel facts items.
  induction items as [| head tail IH];
    intros index item value Hnth Hin.
  - destruct index; discriminate.
  - destruct index as [| index].
    + simpl in Hnth. inversion Hnth; subst item.
      simpl.
      apply in_or_app.
      left.
      exact Hin.
    + simpl in Hnth.
      simpl.
      apply in_or_app.
      right.
      eapply IH; eauto.
Qed.

Lemma phase1_surface_root_goal_options_global :
  phase1_surface_parser_goal_options_global
    expression_fuel
    (GoalExpression [] (ENonterminal phase1_surface_start)).
Proof.
  unfold phase1_surface_parser_goal_options_global,
    phase1_surface_parser_goal_rank_options_fuel,
    phase1_surface_parser_all_goal_rank_options.
  intros value Hin.
  apply in_or_app.
  left.
  exact Hin.
Qed.

Lemma phase1_surface_lookup_rule_goal_options_global :
  forall path name body,
    lookupRule name phase1_surface_rules = Some body ->
    phase1_surface_parser_goal_options_global
      expression_fuel
      (GoalExpression path body).
Proof.
  intros path name body Hlookup.
  unfold phase1_surface_parser_goal_options_global,
    phase1_surface_parser_goal_rank_options_fuel.
  intros value Hin.
  eapply phase1_surface_lookup_rule_goal_rank_options_are_global; eauto.
Qed.

Lemma phase1_surface_sequence_wrapper_options_global :
  forall fuel path items,
    phase1_surface_parser_goal_options_global
      (S fuel) (GoalExpression path (ESequence items)) ->
    phase1_surface_parser_goal_options_global
      fuel (GoalSequence path 0 items).
Proof.
  intros fuel path items Hglobal value Hin.
  apply Hglobal.
  unfold phase1_surface_parser_goal_rank_options_fuel in *.
  rewrite parser_expression_sequence_goal_rank_options_equation.
  simpl.
  right.
  exact Hin.
Qed.

Lemma phase1_surface_alternative_member_options_global :
  forall fuel path items index item,
    nth_error items index = Some item ->
    phase1_surface_parser_goal_options_global
      (S fuel) (GoalExpression path (EAlternative items)) ->
    phase1_surface_parser_goal_options_global
      fuel (GoalExpression (descend path (AtAlternative index)) item).
Proof.
  intros fuel path items index item Hnth Hglobal value Hin.
  apply Hglobal.
  unfold phase1_surface_parser_goal_rank_options_fuel in *.
  rewrite parser_expression_alternative_goal_rank_options_equation.
  simpl.
  right.
  eapply parser_alternative_member_rank_options_subset; eauto.
Qed.

Lemma phase1_surface_optional_body_options_global :
  forall fuel path body,
    phase1_surface_parser_goal_options_global
      (S fuel) (GoalExpression path (EOptional body)) ->
    phase1_surface_parser_goal_options_global
      fuel (GoalExpression (descend path AtOptionalBody) body).
Proof.
  intros fuel path body Hglobal value Hin.
  apply Hglobal.
  unfold phase1_surface_parser_goal_rank_options_fuel in *.
  rewrite parser_expression_optional_goal_rank_options_equation.
  simpl.
  right.
  exact Hin.
Qed.

Lemma phase1_surface_repetition_wrapper_options_global :
  forall fuel path body,
    phase1_surface_parser_goal_options_global
      (S fuel) (GoalExpression path (ERepetition body)) ->
    phase1_surface_parser_goal_options_global
      fuel (GoalRepetition path body).
Proof.
  intros fuel path body Hglobal value Hin.
  apply Hglobal.
  unfold phase1_surface_parser_goal_rank_options_fuel in *.
  rewrite parser_expression_repetition_goal_rank_options_equation.
  simpl.
  right.
  exact Hin.
Qed.

Lemma phase1_surface_sequence_head_options_global :
  forall fuel path index item rest,
    phase1_surface_parser_goal_options_global
      fuel (GoalSequence path index (item :: rest)) ->
    phase1_surface_parser_goal_options_global
      fuel (GoalExpression (descend path (AtSequence index)) item).
Proof.
  intros fuel path index item rest Hglobal value Hin.
  apply Hglobal.
  unfold phase1_surface_parser_goal_rank_options_fuel in *.
  eapply parser_sequence_goal_options_head_subset.
  exact Hin.
Qed.

Lemma phase1_surface_sequence_tail_options_global :
  forall fuel path index item rest,
    phase1_surface_parser_goal_options_global
      fuel (GoalSequence path index (item :: rest)) ->
    phase1_surface_parser_goal_options_global
      fuel (GoalSequence path (S index) rest).
Proof.
  intros fuel path index item rest Hglobal value Hin.
  apply Hglobal.
  unfold phase1_surface_parser_goal_rank_options_fuel in *.
  eapply parser_sequence_goal_options_tail_subset.
  exact Hin.
Qed.

Lemma phase1_surface_repetition_body_options_global :
  forall fuel path body,
    phase1_surface_parser_goal_options_global
      fuel (GoalRepetition path body) ->
    phase1_surface_parser_goal_options_global
      fuel (GoalExpression (descend path AtRepetitionBody) body).
Proof.
  intros fuel path body Hglobal value Hin.
  apply Hglobal.
  unfold phase1_surface_parser_goal_rank_options_fuel,
    parser_repetition_goal_rank_options_fuel in *.
  simpl.
  right.
  exact Hin.
Qed.

Lemma phase1_surface_parser_goal_rank_exists :
  forall fuel goal,
    phase1_surface_parser_goal_options_global fuel goal ->
    exists rank,
      phase1_surface_parser_goal_rank_fuel fuel goal = Some rank.
Proof.
  intros fuel goal Hglobal.
  pose proof
    (phase1_surface_parser_goal_rank_option_is_collected fuel goal) as Hlocal.
  pose proof (Hglobal _ Hlocal) as Hmember.
  pose proof phase1_surface_parser_all_goal_ranks_are_defined as Hall.
  destruct
    (forallb_forall
      option_nat_definedb
      phase1_surface_parser_all_goal_rank_options)
    as [Hall_to _].
  pose proof (Hall_to Hall) as Hall_defined.
  specialize (Hall_defined _ Hmember).
  destruct (phase1_surface_parser_goal_rank_fuel fuel goal)
    as [rank |] eqn:Hrank.
  - exists rank. reflexivity.
  - simpl in Hall_defined. discriminate.
Qed.

Lemma phase1_surface_parser_goal_rank_below_global_bound :
  forall fuel goal rank,
    phase1_surface_parser_goal_options_global fuel goal ->
    phase1_surface_parser_goal_rank_fuel fuel goal = Some rank ->
    rank < phase1_surface_parser_global_goal_rank_bound.
Proof.
  intros fuel goal rank Hglobal Hrank.
  eapply phase1_surface_parser_global_goal_rank_bounds_member.
  apply Hglobal.
  pose proof
    (phase1_surface_parser_goal_rank_option_is_collected fuel goal) as Hlocal.
  rewrite Hrank in Hlocal.
  exact Hlocal.
Qed.

Lemma phase1_surface_lookup_rule_choice_safe :
  forall name body,
    lookupRule name phase1_surface_rules = Some body ->
    choice_bodies_nonnullable_fuel expression_fuel body = true.
Proof.
  intros name body Hlookup.
  eapply phase1_surface_rule_body_choice_safe.
  exact Hlookup.
Qed.

Lemma phase1_surface_root_goal_choice_safe :
  phase1_surface_parser_goal_choice_safe
    expression_fuel
    (GoalExpression [] (ENonterminal phase1_surface_start)).
Proof.
  constructor.
  unfold phase1_surface_parser_goal_choice_safe_structural.
  apply phase1_surface_expression_choice_safe_of_bool.
  unfold expression_fuel.
  reflexivity.
Qed.

Lemma phase1_surface_sequence_wrapper_choice_safe :
  forall fuel path items,
    phase1_surface_parser_goal_choice_safe
      (S fuel) (GoalExpression path (ESequence items)) ->
    phase1_surface_parser_goal_choice_safe
      fuel (GoalSequence path 0 items).
Proof.
  intros fuel path items Hsafe.
  destruct Hsafe as [Hsafe].
  constructor.
  exact Hsafe.
Qed.

Lemma phase1_surface_alternative_member_choice_safe :
  forall fuel path items index item,
    nth_error items index = Some item ->
    phase1_surface_parser_goal_choice_safe
      (S fuel) (GoalExpression path (EAlternative items)) ->
    phase1_surface_parser_goal_choice_safe
      fuel (GoalExpression (descend path (AtAlternative index)) item).
Proof.
  intros fuel path items index item Hnth Hsafe.
  destruct Hsafe as [Hsafe].
  constructor.
  unfold phase1_surface_parser_goal_choice_safe_structural in Hsafe |- *.
  rewrite Forall_forall in Hsafe.
  assert (Hin : In item items).
  {
    eapply nth_error_In. exact Hnth.
  }
  exact (proj2 (Hsafe item Hin)).
Qed.

Lemma phase1_surface_optional_body_choice_safe :
  forall fuel path body,
    phase1_surface_parser_goal_choice_safe
      (S fuel) (GoalExpression path (EOptional body)) ->
    phase1_surface_parser_goal_choice_safe
      fuel (GoalExpression (descend path AtOptionalBody) body).
Proof.
  intros fuel path body Hsafe.
  destruct Hsafe as [Hsafe].
  constructor.
  unfold phase1_surface_parser_goal_choice_safe_structural in Hsafe |- *.
  exact (proj2 Hsafe).
Qed.

Lemma phase1_surface_repetition_wrapper_choice_safe :
  forall fuel path body,
    phase1_surface_parser_goal_choice_safe
      (S fuel) (GoalExpression path (ERepetition body)) ->
    phase1_surface_parser_goal_choice_safe
      fuel (GoalRepetition path body).
Proof.
  intros fuel path body Hsafe.
  destruct Hsafe as [Hsafe].
  constructor.
  unfold phase1_surface_parser_goal_choice_safe_structural in Hsafe |- *.
  exact (proj2 Hsafe).
Qed.

Lemma phase1_surface_sequence_cons_choice_safe :
  forall fuel path index item rest,
    phase1_surface_parser_goal_choice_safe
      fuel (GoalSequence path index (item :: rest)) ->
    phase1_surface_parser_goal_choice_safe
      fuel (GoalExpression (descend path (AtSequence index)) item) /\
    phase1_surface_parser_goal_choice_safe
      fuel (GoalSequence path (S index) rest).
Proof.
  intros fuel path index item rest Hsafe.
  destruct Hsafe as [Hsafe].
  unfold phase1_surface_parser_goal_choice_safe_structural in Hsafe.
  inversion Hsafe as [|head tail Hhead Htail]; subst.
  split.
  - constructor. exact Hhead.
  - constructor. exact Htail.
Qed.

Lemma phase1_surface_repetition_body_choice_safe :
  forall fuel path body,
    phase1_surface_parser_goal_choice_safe
      fuel (GoalRepetition path body) ->
    phase1_surface_parser_goal_choice_safe
      fuel (GoalExpression (descend path AtRepetitionBody) body).
Proof.
  intros fuel path body Hsafe.
  destruct Hsafe as [Hsafe].
  constructor.
  exact Hsafe.
Qed.

Lemma phase1_surface_nonterminal_child_rank_decreases_fuel :
  forall fuel name body parent_rank child_rank,
    lookupRule name phase1_surface_rules = Some body ->
    parser_expression_rank_fuel
      (S fuel) phase1_surface_parser_rank_facts (ENonterminal name) =
      Some parent_rank ->
    parser_expression_rank_fuel
      expression_fuel phase1_surface_parser_rank_facts body =
      Some child_rank ->
    child_rank < parent_rank.
Proof.
  intros fuel name body parent_rank child_rank Hlookup Hparent Hchild.
  simpl in Hparent.
  inversion Hparent; subst parent_rank.
  pose proof
    (parser_nonterminal_child_rank_decreases name body Hlookup) as Hdecrease.
  unfold parser_expression_rank in Hdecrease.
  rewrite Hchild in Hdecrease.
  exact Hdecrease.
Qed.