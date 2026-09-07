From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Strings.String Lia.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDeterminacyNullableFirst
  GrammarParserRank.

Import ListNotations.
Open Scope string_scope.

(*
  Public goal-rank equations for the finite Grammar-v1 parser measure.

  GrammarParserRank.v computes the exact same-input nonterminal fixed point.
  This file exposes the structural ranks hidden inside its fuelled expression
  traversal so the total-fuel proof can reason about the recognizer's recursive
  expression, sequence, and repetition goals directly.
*)

Fixpoint parser_sequence_goal_rank_fuel
  (fuel : nat)
  (facts : list (string * nat))
  (items : list EbnfExpression) : option nat :=
  match items with
  | [] => Some 1
  | item :: rest =>
      match parser_expression_rank_fuel fuel facts item with
      | None => None
      | Some head_rank =>
          if nullable_expression phase1_surface_nullable_facts item
          then
            match parser_sequence_goal_rank_fuel fuel facts rest with
            | Some tail_rank => Some (S (Nat.max head_rank tail_rank))
            | None => None
            end
          else Some (S head_rank)
      end
  end.

Fixpoint parser_alternative_goal_rank_fuel
  (fuel : nat)
  (facts : list (string * nat))
  (items : list EbnfExpression) : option nat :=
  match items with
  | [] => Some 0
  | item :: rest =>
      match
        parser_expression_rank_fuel fuel facts item,
        parser_alternative_goal_rank_fuel fuel facts rest
      with
      | Some head_rank, Some tail_rank =>
          Some (Nat.max head_rank tail_rank)
      | _, _ => None
      end
  end.

Definition parser_repetition_goal_rank_fuel
  (fuel : nat)
  (facts : list (string * nat))
  (body : EbnfExpression) : option nat :=
  match parser_expression_rank_fuel fuel facts body with
  | Some rank => Some (S rank)
  | None => None
  end.

Lemma option_successor_match_injective :
  forall left right,
    (match left with
     | Some rank => Some (S rank)
     | None => None
     end) =
    (match right with
     | Some rank => Some (S rank)
     | None => None
     end) ->
    left = right.
Proof.
  intros left right Hequal.
  destruct left as [left|], right as [right|];
    simpl in Hequal; try discriminate; try reflexivity.
  inversion Hequal.
  reflexivity.
Qed.

Lemma parser_expression_sequence_rank_equation :
  forall fuel facts items,
    parser_expression_rank_fuel (S fuel) facts (ESequence items) =
    match parser_sequence_goal_rank_fuel fuel facts items with
    | Some rank => Some (S rank)
    | None => None
    end.
Proof.
  intros fuel facts items.
  induction items as [|item rest IH].
  - reflexivity.
  - simpl in IH |- *.
    destruct (parser_expression_rank_fuel fuel facts item) as [head_rank|]
      eqn:Hhead; simpl; try reflexivity.
    destruct (nullable_expression phase1_surface_nullable_facts item) eqn:Hnull;
      simpl; try reflexivity.
    pose proof (option_successor_match_injective _ _ IH) as Hraw.
    rewrite Hraw.
    reflexivity.
Qed.

Lemma parser_expression_alternative_rank_equation :
  forall fuel facts items,
    parser_expression_rank_fuel (S fuel) facts (EAlternative items) =
    match parser_alternative_goal_rank_fuel fuel facts items with
    | Some rank => Some (S rank)
    | None => None
    end.
Proof.
  intros fuel facts items.
  induction items as [|item rest IH].
  - reflexivity.
  - simpl in IH |- *.
    destruct (parser_expression_rank_fuel fuel facts item) as [head_rank|]
      eqn:Hhead; simpl; try reflexivity.
    pose proof (option_successor_match_injective _ _ IH) as Hraw.
    rewrite Hraw.
    reflexivity.
Qed.

Lemma parser_expression_repetition_rank_equation :
  forall fuel facts body,
    parser_expression_rank_fuel (S fuel) facts (ERepetition body) =
    match parser_repetition_goal_rank_fuel fuel facts body with
    | Some rank => Some (S rank)
    | None => None
    end.
Proof.
  intros fuel facts body.
  unfold parser_repetition_goal_rank_fuel.
  simpl.
  destruct (parser_expression_rank_fuel fuel facts body); reflexivity.
Qed.

Lemma parser_rank_lookup_pass :
  forall rules facts name body,
    lookupRule name rules = Some body ->
    parser_rank_lookup name (parser_rank_pass rules facts) =
      parser_expression_rank facts body.
Proof.
  intros rules facts.
  induction rules as [|[candidate expression] rest IH];
    intros name body Hlookup; simpl in *.
  - discriminate.
  - destruct (String.eqb name candidate) eqn:Hname.
    + apply String.eqb_eq in Hname. subst candidate.
      inversion Hlookup. subst body.
      reflexivity.
    + eapply IH. exact Hlookup.
Qed.

Lemma phase1_surface_parser_rank_lookup_rule :
  forall name body,
    lookupRule name phase1_surface_rules = Some body ->
    parser_rank_lookup name phase1_surface_parser_rank_facts =
      parser_expression_rank phase1_surface_parser_rank_facts body.
Proof.
  intros name body Hlookup.
  pose proof
    (parser_rank_lookup_pass
      phase1_surface_rules
      phase1_surface_parser_rank_facts
      name body Hlookup) as Hrank.
  rewrite phase1_surface_parser_rank_facts_are_stable in Hrank.
  exact Hrank.
Qed.

Lemma parser_nonterminal_child_rank_decreases :
  forall name body body_rank,
    lookupRule name phase1_surface_rules = Some body ->
    parser_expression_rank_fuel
      expression_fuel phase1_surface_parser_rank_facts body = Some body_rank ->
    parser_expression_rank_fuel
      expression_fuel phase1_surface_parser_rank_facts (ENonterminal name) =
      Some (S body_rank).
Proof.
  intros name body body_rank Hlookup Hbody.
  pose proof (phase1_surface_parser_rank_lookup_rule name body Hlookup) as Hrank.
  unfold parser_expression_rank in Hrank.
  rewrite Hbody in Hrank.
  simpl in Hrank.
  unfold expression_fuel.
  simpl.
  rewrite Hrank.
  reflexivity.
Qed.

Lemma parser_sequence_wrapper_rank_decreases :
  forall fuel facts items parent_rank sequence_rank,
    parser_expression_rank_fuel (S fuel) facts (ESequence items) =
      Some parent_rank ->
    parser_sequence_goal_rank_fuel fuel facts items = Some sequence_rank ->
    sequence_rank < parent_rank.
Proof.
  intros fuel facts items parent_rank sequence_rank Hparent Hsequence.
  rewrite parser_expression_sequence_rank_equation in Hparent.
  rewrite Hsequence in Hparent.
  inversion Hparent; subst.
  lia.
Qed.

Lemma parser_sequence_head_rank_decreases :
  forall fuel facts item rest sequence_rank head_rank,
    parser_sequence_goal_rank_fuel fuel facts (item :: rest) =
      Some sequence_rank ->
    parser_expression_rank_fuel fuel facts item = Some head_rank ->
    head_rank < sequence_rank.
Proof.
  intros fuel facts item rest sequence_rank head_rank Hsequence Hhead.
  simpl in Hsequence.
  rewrite Hhead in Hsequence.
  destruct (nullable_expression phase1_surface_nullable_facts item) eqn:Hnull.
  - destruct (parser_sequence_goal_rank_fuel fuel facts rest) as [tail_rank|]
      eqn:Htail; try discriminate.
    inversion Hsequence; subst.
    lia.
  - inversion Hsequence; subst.
    lia.
Qed.

Lemma parser_sequence_nullable_tail_rank_decreases :
  forall fuel facts item rest sequence_rank tail_rank,
    nullable_expression phase1_surface_nullable_facts item = true ->
    parser_sequence_goal_rank_fuel fuel facts (item :: rest) =
      Some sequence_rank ->
    parser_sequence_goal_rank_fuel fuel facts rest = Some tail_rank ->
    tail_rank < sequence_rank.
Proof.
  intros fuel facts item rest sequence_rank tail_rank Hnullable Hsequence Htail.
  simpl in Hsequence.
  destruct (parser_expression_rank_fuel fuel facts item) as [head_rank|]
    eqn:Hhead; try discriminate.
  rewrite Hnullable, Htail in Hsequence.
  inversion Hsequence; subst.
  lia.
Qed.

Lemma parser_alternative_member_rank_le :
  forall fuel facts items index item alternative_rank item_rank,
    nth_error items index = Some item ->
    parser_alternative_goal_rank_fuel fuel facts items = Some alternative_rank ->
    parser_expression_rank_fuel fuel facts item = Some item_rank ->
    item_rank <= alternative_rank.
Proof.
  intros fuel facts items.
  induction items as [|head tail IH];
    intros index item alternative_rank item_rank Hnth Halternative Hitem.
  - destruct index; discriminate.
  - destruct index as [|index].
    + simpl in Hnth. inversion Hnth; subst item.
      simpl in Halternative.
      rewrite Hitem in Halternative.
      destruct (parser_alternative_goal_rank_fuel fuel facts tail)
        as [tail_rank|] eqn:Htail; try discriminate.
      inversion Halternative; subst alternative_rank.
      apply Nat.le_max_l.
    + simpl in Hnth.
      simpl in Halternative.
      destruct (parser_expression_rank_fuel fuel facts head)
        as [head_rank|] eqn:Hhead; try discriminate.
      destruct (parser_alternative_goal_rank_fuel fuel facts tail)
        as [tail_rank|] eqn:Htail; try discriminate.
      inversion Halternative; subst alternative_rank.
      eapply Nat.le_trans.
      * eapply IH; eauto.
      * apply Nat.le_max_r.
Qed.

Lemma parser_alternative_member_rank_decreases :
  forall fuel facts items index item parent_rank alternative_rank item_rank,
    parser_expression_rank_fuel (S fuel) facts (EAlternative items) =
      Some parent_rank ->
    parser_alternative_goal_rank_fuel fuel facts items = Some alternative_rank ->
    nth_error items index = Some item ->
    parser_expression_rank_fuel fuel facts item = Some item_rank ->
    item_rank < parent_rank.
Proof.
  intros fuel facts items index item parent_rank alternative_rank item_rank
    Hparent Halternative Hnth Hitem.
  rewrite parser_expression_alternative_rank_equation in Hparent.
  rewrite Halternative in Hparent.
  inversion Hparent; subst parent_rank.
  pose proof
    (parser_alternative_member_rank_le
      fuel facts items index item alternative_rank item_rank
      Hnth Halternative Hitem) as Hle.
  lia.
Qed.

Lemma parser_optional_body_rank_decreases :
  forall fuel facts body parent_rank body_rank,
    parser_expression_rank_fuel (S fuel) facts (EOptional body) =
      Some parent_rank ->
    parser_expression_rank_fuel fuel facts body = Some body_rank ->
    body_rank < parent_rank.
Proof.
  intros fuel facts body parent_rank body_rank Hparent Hbody.
  simpl in Hparent.
  rewrite Hbody in Hparent.
  inversion Hparent; subst.
  lia.
Qed.

Lemma parser_repetition_wrapper_rank_decreases :
  forall fuel facts body parent_rank repetition_rank,
    parser_expression_rank_fuel (S fuel) facts (ERepetition body) =
      Some parent_rank ->
    parser_repetition_goal_rank_fuel fuel facts body = Some repetition_rank ->
    repetition_rank < parent_rank.
Proof.
  intros fuel facts body parent_rank repetition_rank Hparent Hrepeat.
  rewrite parser_expression_repetition_rank_equation in Hparent.
  rewrite Hrepeat in Hparent.
  inversion Hparent; subst.
  lia.
Qed.

Lemma parser_repetition_body_rank_decreases :
  forall fuel facts body repetition_rank body_rank,
    parser_repetition_goal_rank_fuel fuel facts body = Some repetition_rank ->
    parser_expression_rank_fuel fuel facts body = Some body_rank ->
    body_rank < repetition_rank.
Proof.
  intros fuel facts body repetition_rank body_rank Hrepeat Hbody.
  unfold parser_repetition_goal_rank_fuel in Hrepeat.
  rewrite Hbody in Hrepeat.
  inversion Hrepeat; subst.
  lia.
Qed.
