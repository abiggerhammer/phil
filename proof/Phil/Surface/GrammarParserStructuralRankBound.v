From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Strings.String Lia.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDeterminacyNullableFirst
  GrammarParserRank
  GrammarParserGoalRank.

Import ListNotations.
Open Scope string_scope.

(*
  Structural reset bound for the finite Grammar-v1 parser measure.

  The exact global-rank certificate in GrammarParserGlobalGoalRank.v checks the
  concrete Grammar-v1 internal goal set.  This file supplies the complementary
  symbolic theorem needed by the total-fuel induction: any successful parser
  rank computation is bounded by the maximum nonterminal rank in the fixed
  table plus a purely structural weight of the current EBNF subtree.

  The bound is intentionally coarse.  Its purpose is to make token-consuming
  recursive edges cheap to reason about: after consumption the rank component
  may reset, but it remains below a grammar-structural constant.  Same-input
  edges continue to use the strict exact-rank lemmas from GrammarParserGoalRank.
*)

Fixpoint parser_expression_weight_fuel
  (fuel : nat)
  (expression : EbnfExpression) : nat :=
  match fuel with
  | 0 => 0
  | S remaining =>
      match expression with
      | ELiteral _ => 1
      | ELexicalClass _ => 1
      | ENonterminal _ => 1
      | ESequence items =>
          let fix sequence_weight
            (pending : list EbnfExpression) : nat :=
            match pending with
            | [] => 1
            | item :: rest =>
                S
                  (parser_expression_weight_fuel remaining item +
                   sequence_weight rest)
            end
          in S (sequence_weight items)
      | EAlternative items =>
          let fix alternative_weight
            (pending : list EbnfExpression) : nat :=
            match pending with
            | [] => 0
            | item :: rest =>
                parser_expression_weight_fuel remaining item +
                alternative_weight rest
            end
          in S (alternative_weight items)
      | EOptional body =>
          S (parser_expression_weight_fuel remaining body)
      | ERepetition body =>
          S (S (parser_expression_weight_fuel remaining body))
      end
  end.

Fixpoint parser_sequence_weight_fuel
  (fuel : nat)
  (items : list EbnfExpression) : nat :=
  match items with
  | [] => 1
  | item :: rest =>
      S
        (parser_expression_weight_fuel fuel item +
         parser_sequence_weight_fuel fuel rest)
  end.

Fixpoint parser_alternative_weight_fuel
  (fuel : nat)
  (items : list EbnfExpression) : nat :=
  match items with
  | [] => 0
  | item :: rest =>
      parser_expression_weight_fuel fuel item +
      parser_alternative_weight_fuel fuel rest
  end.

Definition parser_repetition_weight_fuel
  (fuel : nat)
  (body : EbnfExpression) : nat :=
  S (parser_expression_weight_fuel fuel body).

Lemma parser_expression_sequence_weight_equation :
  forall fuel items,
    parser_expression_weight_fuel (S fuel) (ESequence items) =
      S (parser_sequence_weight_fuel fuel items).
Proof.
  intros fuel items.
  induction items as [| item rest IH].
  - reflexivity.
  - simpl in IH |- *.
    lia.
Qed.

Lemma parser_expression_alternative_weight_equation :
  forall fuel items,
    parser_expression_weight_fuel (S fuel) (EAlternative items) =
      S (parser_alternative_weight_fuel fuel items).
Proof.
  intros fuel items.
  induction items as [| item rest IH].
  - reflexivity.
  - simpl in IH |- *.
    lia.
Qed.

Lemma parser_rank_lookup_le_max :
  forall name facts,
    parser_rank_lookup name facts <= parser_rank_max facts.
Proof.
  intros name facts.
  induction facts as [| [candidate rank] rest IH].
  - simpl. lia.
  - simpl.
    destruct (String.eqb name candidate) eqn:Hname.
    + apply Nat.le_max_l.
    + eapply Nat.le_trans.
      * exact IH.
      * apply Nat.le_max_r.
Qed.

Lemma parser_sequence_rank_upper_from_expression :
  forall fuel facts,
    (forall expression rank,
      parser_expression_rank_fuel fuel facts expression = Some rank ->
      rank <=
        parser_rank_max facts +
        parser_expression_weight_fuel fuel expression) ->
    forall items rank,
      parser_sequence_goal_rank_fuel fuel facts items = Some rank ->
      rank <=
        parser_rank_max facts +
        parser_sequence_weight_fuel fuel items.
Proof.
  intros fuel facts Hexpr items.
  induction items as [| item rest IH]; intros rank Hrank.
  - simpl in Hrank. inversion Hrank; subst. simpl. lia.
  - simpl in Hrank.
    destruct (parser_expression_rank_fuel fuel facts item)
      as [head_rank |] eqn:Hhead; try discriminate.
    pose proof (Hexpr item head_rank Hhead) as Hhead_bound.
    destruct (nullable_expression phase1_surface_nullable_facts item) eqn:Hnullable.
    + destruct (parser_sequence_goal_rank_fuel fuel facts rest)
        as [tail_rank |] eqn:Htail; try discriminate.
      pose proof (IH tail_rank eq_refl) as Htail_bound.
      inversion Hrank; subst rank.
      assert
        (Hmax :
          Nat.max head_rank tail_rank <=
            parser_rank_max facts +
            parser_expression_weight_fuel fuel item +
            parser_sequence_weight_fuel fuel rest).
      {
        apply Nat.max_lub; lia.
      }
      simpl.
      lia.
    + inversion Hrank; subst rank.
      simpl.
      lia.
Qed.

Lemma parser_alternative_rank_upper_from_expression :
  forall fuel facts,
    (forall expression rank,
      parser_expression_rank_fuel fuel facts expression = Some rank ->
      rank <=
        parser_rank_max facts +
        parser_expression_weight_fuel fuel expression) ->
    forall items rank,
      parser_alternative_goal_rank_fuel fuel facts items = Some rank ->
      rank <=
        parser_rank_max facts +
        parser_alternative_weight_fuel fuel items.
Proof.
  intros fuel facts Hexpr items.
  induction items as [| item rest IH]; intros rank Hrank.
  - simpl in Hrank. inversion Hrank; subst. simpl. lia.
  - simpl in Hrank.
    destruct (parser_expression_rank_fuel fuel facts item)
      as [head_rank |] eqn:Hhead; try discriminate.
    destruct (parser_alternative_goal_rank_fuel fuel facts rest)
      as [tail_rank |] eqn:Htail; try discriminate.
    pose proof (Hexpr item head_rank Hhead) as Hhead_bound.
    pose proof (IH tail_rank eq_refl) as Htail_bound.
    inversion Hrank; subst rank.
    assert
      (Hmax :
        Nat.max head_rank tail_rank <=
          parser_rank_max facts +
          parser_expression_weight_fuel fuel item +
          parser_alternative_weight_fuel fuel rest).
    {
      apply Nat.max_lub; lia.
    }
    simpl.
    lia.
Qed.

Theorem parser_expression_rank_fuel_upper_bound :
  forall fuel facts expression rank,
    parser_expression_rank_fuel fuel facts expression = Some rank ->
    rank <=
      parser_rank_max facts +
      parser_expression_weight_fuel fuel expression.
Proof.
  induction fuel as [| fuel IH]; intros facts expression rank Hrank.
  - discriminate Hrank.
  - destruct expression as
      [literal | class | name | items | items | body | body].
    + simpl in Hrank. inversion Hrank; subst. simpl. lia.
    + simpl in Hrank. inversion Hrank; subst. simpl. lia.
    + simpl in Hrank. inversion Hrank; subst.
      simpl.
      pose proof (parser_rank_lookup_le_max name facts) as Hlookup.
      lia.
    + rewrite parser_expression_sequence_rank_equation in Hrank.
      destruct (parser_sequence_goal_rank_fuel fuel facts items)
        as [sequence_rank |] eqn:Hsequence; try discriminate.
      inversion Hrank; subst rank.
      pose proof
        (parser_sequence_rank_upper_from_expression
          fuel facts (IH facts) items sequence_rank Hsequence)
        as Hsequence_bound.
      rewrite parser_expression_sequence_weight_equation.
      lia.
    + rewrite parser_expression_alternative_rank_equation in Hrank.
      destruct (parser_alternative_goal_rank_fuel fuel facts items)
        as [alternative_rank |] eqn:Halternative; try discriminate.
      inversion Hrank; subst rank.
      pose proof
        (parser_alternative_rank_upper_from_expression
          fuel facts (IH facts) items alternative_rank Halternative)
        as Halternative_bound.
      rewrite parser_expression_alternative_weight_equation.
      lia.
    + simpl in Hrank.
      destruct (parser_expression_rank_fuel fuel facts body)
        as [body_rank |] eqn:Hbody; try discriminate.
      inversion Hrank; subst rank.
      pose proof (IH facts body body_rank Hbody) as Hbody_bound.
      simpl.
      lia.
    + simpl in Hrank.
      destruct (parser_expression_rank_fuel fuel facts body)
        as [body_rank |] eqn:Hbody; try discriminate.
      inversion Hrank; subst rank.
      pose proof (IH facts body body_rank Hbody) as Hbody_bound.
      simpl.
      lia.
Qed.

Corollary parser_sequence_goal_rank_fuel_upper_bound :
  forall fuel facts items rank,
    parser_sequence_goal_rank_fuel fuel facts items = Some rank ->
    rank <=
      parser_rank_max facts +
      parser_sequence_weight_fuel fuel items.
Proof.
  intros fuel facts items rank Hrank.
  eapply parser_sequence_rank_upper_from_expression.
  - intros expression expression_rank Hexpression.
    eapply parser_expression_rank_fuel_upper_bound.
    exact Hexpression.
  - exact Hrank.
Qed.

Corollary parser_alternative_goal_rank_fuel_upper_bound :
  forall fuel facts items rank,
    parser_alternative_goal_rank_fuel fuel facts items = Some rank ->
    rank <=
      parser_rank_max facts +
      parser_alternative_weight_fuel fuel items.
Proof.
  intros fuel facts items rank Hrank.
  eapply parser_alternative_rank_upper_from_expression.
  - intros expression expression_rank Hexpression.
    eapply parser_expression_rank_fuel_upper_bound.
    exact Hexpression.
  - exact Hrank.
Qed.

Corollary parser_repetition_goal_rank_fuel_upper_bound :
  forall fuel facts body rank,
    parser_repetition_goal_rank_fuel fuel facts body = Some rank ->
    rank <=
      parser_rank_max facts +
      parser_repetition_weight_fuel fuel body.
Proof.
  intros fuel facts body rank Hrank.
  unfold parser_repetition_goal_rank_fuel,
    parser_repetition_weight_fuel in *.
  destruct (parser_expression_rank_fuel fuel facts body)
    as [body_rank |] eqn:Hbody; try discriminate.
  inversion Hrank; subst rank.
  pose proof
    (parser_expression_rank_fuel_upper_bound
      fuel facts body body_rank Hbody) as Hbody_bound.
  lia.
Qed.

Fixpoint parser_rule_weight_max
  (rules : list GrammarRule) : nat :=
  match rules with
  | [] => 0
  | (_, body) :: rest =>
      Nat.max
        (parser_expression_weight_fuel expression_fuel body)
        (parser_rule_weight_max rest)
  end.

Lemma lookup_rule_weight_le_max :
  forall rules name body,
    lookupRule name rules = Some body ->
    parser_expression_weight_fuel expression_fuel body <=
      parser_rule_weight_max rules.
Proof.
  intros rules.
  induction rules as [| [candidate expression] rest IH].
  - intros name body Hlookup.
    cbn [lookupRule parser_rule_weight_max] in Hlookup |- *.
    discriminate Hlookup.
  - intros name body Hlookup.
    cbn [lookupRule parser_rule_weight_max] in Hlookup |- *.
    destruct (String.eqb name candidate) eqn:Hname.
    + inversion Hlookup; subst body.
      apply Nat.le_max_l.
    + eapply Nat.le_trans.
      * eapply IH. exact Hlookup.
      * apply Nat.le_max_r.
Qed.

Definition phase1_surface_parser_structural_rank_bound : nat :=
  S
    (parser_rank_max phase1_surface_parser_rank_facts +
     parser_rule_weight_max phase1_surface_rules).

Theorem phase1_surface_rule_body_rank_below_structural_bound :
  forall name body rank,
    lookupRule name phase1_surface_rules = Some body ->
    parser_expression_rank_fuel
      expression_fuel phase1_surface_parser_rank_facts body = Some rank ->
    rank < phase1_surface_parser_structural_rank_bound.
Proof.
  intros name body rank Hlookup Hrank.
  pose proof
    (parser_expression_rank_fuel_upper_bound
      expression_fuel phase1_surface_parser_rank_facts body rank Hrank)
    as Hupper.
  pose proof
    (lookup_rule_weight_le_max
      phase1_surface_rules name body Hlookup) as Hweight.
  unfold phase1_surface_parser_structural_rank_bound.
  lia.
Qed.

Theorem phase1_surface_parser_structural_rank_bound_positive :
  0 < phase1_surface_parser_structural_rank_bound.
Proof.
  unfold phase1_surface_parser_structural_rank_bound.
  lia.
Qed.

Lemma parser_sequence_head_weight_decreases :
  forall fuel item rest,
    parser_expression_weight_fuel fuel item <
      parser_sequence_weight_fuel fuel (item :: rest).
Proof.
  intros fuel item rest.
  simpl.
  lia.
Qed.

Lemma parser_sequence_tail_weight_decreases :
  forall fuel item rest,
    parser_sequence_weight_fuel fuel rest <
      parser_sequence_weight_fuel fuel (item :: rest).
Proof.
  intros fuel item rest.
  simpl.
  lia.
Qed.

Lemma parser_optional_body_weight_decreases :
  forall fuel body,
    parser_expression_weight_fuel fuel body <
      parser_expression_weight_fuel (S fuel) (EOptional body).
Proof.
  intros fuel body.
  simpl.
  lia.
Qed.

Lemma parser_repetition_goal_weight_decreases :
  forall fuel body,
    parser_repetition_weight_fuel fuel body <
      parser_expression_weight_fuel (S fuel) (ERepetition body).
Proof.
  intros fuel body.
  unfold parser_repetition_weight_fuel.
  simpl.
  lia.
Qed.

Lemma parser_repetition_body_weight_decreases :
  forall fuel body,
    parser_expression_weight_fuel fuel body <
      parser_repetition_weight_fuel fuel body.
Proof.
  intros fuel body.
  unfold parser_repetition_weight_fuel.
  lia.
Qed.
