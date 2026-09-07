From Stdlib Require Import Bool.Bool Lists.List Arith.PeanoNat Strings.String.

From Phil.Surface Require Import
  Grammar
  GrammarDeterminacyNullableFirst.

Import ListNotations.
Open Scope string_scope.

(*
  Grammar-v1 parser same-input recursion rank for
  PHIL-SURFACE-GRAMMAR-CORR-001.

  The fuel-bounded reference recognizer from GrammarParserRecognizer.v only
  needs a global fuel because Rocq's structural termination checker cannot see
  the semantic decrease that happens when a recursive parse consumes input.
  Parser recursion therefore has two independent decreases:

  - a recursive call may consume at least one ConcreteToken; or
  - while the input is unchanged, the exact Grammar-v1 call graph must descend
    through a finite zero-consumption rank.

  This file computes the second component inside Rocq.  In a sequence, the tail
  can be reached with the same input only when the head is nullable, so tail rank
  is propagated only across nullable prefixes.  Repetition recursively parses
  its tail only after its body makes progress, so that consuming recursive edge
  is deliberately excluded from the same-input rank.  Ordinary guarded grammar
  recursion such as parenthesized expressions therefore does not create a false
  rank cycle, while a genuine left/non-consuming recursive cycle would keep the
  rank pass increasing and fail the checked stability theorem below.
*)

Fixpoint parser_rank_lookup
  (name : string)
  (facts : list (string * nat)) : nat :=
  match facts with
  | [] => 0
  | (candidate, rank) :: rest =>
      if String.eqb name candidate
      then rank
      else parser_rank_lookup name rest
  end.

Fixpoint parser_expression_rank_fuel
  (fuel : nat)
  (facts : list (string * nat))
  (expression : EbnfExpression) : option nat :=
  match fuel with
  | 0 => None
  | S remaining =>
      match expression with
      | ELiteral _ => Some 1
      | ELexicalClass _ => Some 1
      | ENonterminal name =>
          Some (S (parser_rank_lookup name facts))
      | ESequence items =>
          let fix sequence_rank
            (pending : list EbnfExpression) : option nat :=
            match pending with
            | [] => Some 1
            | item :: rest =>
                match parser_expression_rank_fuel remaining facts item with
                | None => None
                | Some head_rank =>
                    if nullable_expression
                         phase1_surface_nullable_facts item
                    then
                      match sequence_rank rest with
                      | Some tail_rank =>
                          Some (S (Nat.max head_rank tail_rank))
                      | None => None
                      end
                    else Some (S head_rank)
                end
            end
          in
          match sequence_rank items with
          | Some rank => Some (S rank)
          | None => None
          end
      | EAlternative items =>
          let fix alternative_rank
            (pending : list EbnfExpression) : option nat :=
            match pending with
            | [] => Some 0
            | item :: rest =>
                match
                  parser_expression_rank_fuel remaining facts item,
                  alternative_rank rest
                with
                | Some head_rank, Some tail_rank =>
                    Some (Nat.max head_rank tail_rank)
                | _, _ => None
                end
            end
          in
          match alternative_rank items with
          | Some rank => Some (S rank)
          | None => None
          end
      | EOptional body =>
          match parser_expression_rank_fuel remaining facts body with
          | Some rank => Some (S rank)
          | None => None
          end
      | ERepetition body =>
          match parser_expression_rank_fuel remaining facts body with
          | Some rank => Some (S (S rank))
          | None => None
          end
      end
  end.

Definition parser_expression_rank
  (facts : list (string * nat))
  (expression : EbnfExpression) : nat :=
  match parser_expression_rank_fuel expression_fuel facts expression with
  | Some rank => rank
  | None => 0
  end.

Fixpoint parser_rank_pass
  (rules : list GrammarRule)
  (facts : list (string * nat)) : list (string * nat) :=
  match rules with
  | [] => []
  | (name, body) :: rest =>
      (name, parser_expression_rank facts body)
        :: parser_rank_pass rest facts
  end.

Fixpoint parser_initial_ranks
  (rules : list GrammarRule) : list (string * nat) :=
  match rules with
  | [] => []
  | (name, _) :: rest =>
      (name, 0) :: parser_initial_ranks rest
  end.

Fixpoint parser_iterate_ranks
  (fuel : nat)
  (rules : list GrammarRule)
  (facts : list (string * nat)) : list (string * nat) :=
  match fuel with
  | 0 => facts
  | S remaining =>
      parser_iterate_ranks remaining rules (parser_rank_pass rules facts)
  end.

Definition phase1_surface_parser_rank_facts : list (string * nat) :=
  parser_iterate_ranks
    256
    phase1_surface_rules
    (parser_initial_ranks phase1_surface_rules).

Definition parser_rank_rule_fuel_sufficient
  (rule : GrammarRule) : bool :=
  match rule with
  | (_, body) =>
      match
        parser_expression_rank_fuel
          expression_fuel phase1_surface_parser_rank_facts body
      with
      | Some _ => true
      | None => false
      end
  end.

Theorem phase1_surface_parser_rank_expression_fuel_is_sufficient :
  forallb parser_rank_rule_fuel_sufficient phase1_surface_rules = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem phase1_surface_parser_rank_facts_are_stable :
  parser_rank_pass
    phase1_surface_rules
    phase1_surface_parser_rank_facts =
  phase1_surface_parser_rank_facts.
Proof.
  vm_compute.
  reflexivity.
Qed.

Fixpoint parser_rank_max
  (facts : list (string * nat)) : nat :=
  match facts with
  | [] => 0
  | (_, rank) :: rest => Nat.max rank (parser_rank_max rest)
  end.

Definition phase1_surface_parser_max_goal_rank : nat :=
  S (parser_rank_max phase1_surface_parser_rank_facts).

Definition parser_rank_positiveb
  (entry : string * nat) : bool :=
  match entry with
  | (_, rank) => Nat.ltb 0 rank
  end.

Definition parser_rank_boundedb
  (entry : string * nat) : bool :=
  match entry with
  | (_, rank) => Nat.ltb rank phase1_surface_parser_max_goal_rank
  end.

Theorem phase1_surface_parser_rule_ranks_are_positive :
  forallb parser_rank_positiveb phase1_surface_parser_rank_facts = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem phase1_surface_parser_rule_ranks_are_bounded :
  forallb parser_rank_boundedb phase1_surface_parser_rank_facts = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Definition phase1_surface_parser_root_goal_rank : nat :=
  S (parser_rank_lookup
    phase1_surface_start phase1_surface_parser_rank_facts).

Theorem phase1_surface_parser_root_goal_rank_is_bounded :
  Nat.leb
    phase1_surface_parser_root_goal_rank
    phase1_surface_parser_max_goal_rank = true.
Proof.
  vm_compute.
  reflexivity.
Qed.
