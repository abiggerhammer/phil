From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Strings.String Lia.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDeterminacyNullableFirst
  GrammarParserRank
  GrammarParserGoalRank.

Import ListNotations.

(*
  Global parser-goal rank coverage for PHIL-SURFACE-GRAMMAR-CORR-001.

  GrammarParserRank.v computes the zero-consumption rank at rule roots, while
  GrammarParserGoalRank.v exposes the recognizer's internal sequence and
  repetition goal ranks.  A consuming sequence head may continue at a later
  suffix whose rank is intentionally absent from the parent's same-input rank,
  so the total parser-fuel theorem needs a separate global bound over every
  internal goal that can occur inside an exact Grammar-v1 rule body.

  This file collects those exact rank computations, checks mechanically that
  none exhaust expression_fuel, and defines a strict bound over the complete
  finite collection.  Nonterminal bodies are covered by rule lookup; guarded
  recursive expansion remains a runtime token-progress issue rather than being
  unfolded here.
*)

Fixpoint parser_expression_goal_rank_options_fuel
  (fuel : nat)
  (facts : list (string * nat))
  (expression : EbnfExpression) : list (option nat) :=
  match fuel with
  | 0 => [None]
  | S remaining =>
      parser_expression_rank_fuel (S remaining) facts expression ::
      match expression with
      | ELiteral _ => []
      | ELexicalClass _ => []
      | ENonterminal _ => []
      | ESequence items =>
          let fix sequence_options
            (pending : list EbnfExpression) : list (option nat) :=
            match pending with
            | [] =>
                [parser_sequence_goal_rank_fuel remaining facts []]
            | item :: rest =>
                parser_sequence_goal_rank_fuel remaining facts pending ::
                List.app
                  (parser_expression_goal_rank_options_fuel
                    remaining facts item)
                  (sequence_options rest)
            end
          in sequence_options items
      | EAlternative items =>
          let fix alternative_options
            (pending : list EbnfExpression) : list (option nat) :=
            match pending with
            | [] => []
            | item :: rest =>
                List.app
                  (parser_expression_goal_rank_options_fuel
                    remaining facts item)
                  (alternative_options rest)
            end
          in alternative_options items
      | EOptional body =>
          parser_expression_goal_rank_options_fuel remaining facts body
      | ERepetition body =>
          parser_repetition_goal_rank_fuel remaining facts body ::
          parser_expression_goal_rank_options_fuel remaining facts body
      end
  end.

Fixpoint parser_rules_goal_rank_options_fuel
  (fuel : nat)
  (facts : list (string * nat))
  (rules : list GrammarRule) : list (option nat) :=
  match rules with
  | [] => []
  | (_, body) :: rest =>
      List.app
        (parser_expression_goal_rank_options_fuel fuel facts body)
        (parser_rules_goal_rank_options_fuel fuel facts rest)
  end.

Definition phase1_surface_parser_all_goal_rank_options : list (option nat) :=
  List.app
    (parser_expression_goal_rank_options_fuel
      expression_fuel
      phase1_surface_parser_rank_facts
      (ENonterminal phase1_surface_start))
    (parser_rules_goal_rank_options_fuel
      expression_fuel
      phase1_surface_parser_rank_facts
      phase1_surface_rules).

Definition option_nat_definedb (value : option nat) : bool :=
  match value with
  | Some _ => true
  | None => false
  end.

Theorem phase1_surface_parser_all_goal_ranks_are_defined :
  forallb option_nat_definedb
    phase1_surface_parser_all_goal_rank_options = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Fixpoint parser_option_rank_max (values : list (option nat)) : nat :=
  match values with
  | [] => 0
  | Some rank :: rest => Nat.max rank (parser_option_rank_max rest)
  | None :: rest => parser_option_rank_max rest
  end.

Definition phase1_surface_parser_global_goal_rank_bound : nat :=
  S (parser_option_rank_max phase1_surface_parser_all_goal_rank_options).

Lemma option_rank_member_below_successor_max :
  forall values rank,
    In (Some rank) values ->
    rank < S (parser_option_rank_max values).
Proof.
  induction values as [|value rest IH]; intros rank Hin.
  - contradiction.
  - simpl in Hin.
    destruct Hin as [Hequal | Hin].
    + subst value.
      simpl.
      pose proof (Nat.le_max_l rank (parser_option_rank_max rest)) as Hmax.
      lia.
    + destruct value as [head_rank |].
      * simpl.
        pose proof (IH rank Hin) as Htail.
        pose proof
          (Nat.le_max_r head_rank (parser_option_rank_max rest)) as Hmax.
        lia.
      * simpl.
        exact (IH rank Hin).
Qed.

Theorem phase1_surface_parser_global_goal_rank_bounds_member :
  forall rank,
    In (Some rank) phase1_surface_parser_all_goal_rank_options ->
    rank < phase1_surface_parser_global_goal_rank_bound.
Proof.
  intros rank Hin.
  unfold phase1_surface_parser_global_goal_rank_bound.
  eapply option_rank_member_below_successor_max.
  exact Hin.
Qed.

Lemma lookup_rule_goal_rank_options_are_collected :
  forall fuel facts rules name body value,
    lookupRule name rules = Some body ->
    In value (parser_expression_goal_rank_options_fuel fuel facts body) ->
    In value (parser_rules_goal_rank_options_fuel fuel facts rules).
Proof.
  intros fuel facts rules.
  induction rules as [|[candidate expression] rest IH];
    intros name body value Hlookup Hin; simpl in *.
  - discriminate.
  - destruct (String.eqb name candidate) eqn:Hname.
    + inversion Hlookup; subst body.
      apply in_or_app.
      left.
      exact Hin.
    + apply in_or_app.
      right.
      eapply IH; eauto.
Qed.

Corollary phase1_surface_lookup_rule_goal_rank_options_are_global :
  forall name body value,
    lookupRule name phase1_surface_rules = Some body ->
    In value
      (parser_expression_goal_rank_options_fuel
        expression_fuel phase1_surface_parser_rank_facts body) ->
    In value phase1_surface_parser_all_goal_rank_options.
Proof.
  intros name body value Hlookup Hin.
  unfold phase1_surface_parser_all_goal_rank_options.
  apply in_or_app.
  right.
  eapply lookup_rule_goal_rank_options_are_collected; eauto.
Qed.

Theorem phase1_surface_parser_global_goal_rank_bound_positive :
  0 < phase1_surface_parser_global_goal_rank_bound.
Proof.
  unfold phase1_surface_parser_global_goal_rank_bound.
  lia.
Qed.

(*
  Downstream parser proofs use the certified nullable equations, not reduction of
  the concrete 128-pass fixed point itself.  Keeping these definitions opaque
  prevents kernel conversion from expanding that table while checking small
  structural lemmas in GrammarParserTotalFuelStatic.v.
*)
Opaque phase1_surface_nullable_facts nullable_expression.
