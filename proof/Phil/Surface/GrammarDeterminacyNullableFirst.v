From Stdlib Require Import Bool.Bool Lists.List Strings.String.

From Phil.Surface Require Import Grammar GrammarDeterminacyCertificate.

Import ListNotations.
Open Scope string_scope.

(*
  Mechanized nullable/FIRST foundations for the exact Grammar-v1 determinacy
  completeness bridge.  These functions operate over the generated Grammar.v
  tree rather than importing nullable/FIRST facts from the Python audit.

  Expression traversal is explicitly fuelled so Rocq's termination checker does
  not need to infer nested recursion through list EbnfExpression fields.  The
  fuelled evaluators return option values; separate checked theorems below prove
  that the chosen fuel is sufficient for every exact Grammar-v1 rule, so fuel
  exhaustion cannot be confused with false nullability or an empty FIRST set.

  This tranche establishes fixed points for the exact Phase 1 grammar only.
  FOLLOW propagation and overlap enumeration are successor work.
*)

Fixpoint lookup_bool (name : string) (facts : list (string * bool)) : bool :=
  match facts with
  | [] => false
  | (candidate, value) :: rest =>
      if String.eqb name candidate then value else lookup_bool name rest
  end.

Definition overlap_token_eqb (left right : OverlapToken) : bool :=
  match left, right with
  | OverlapLiteral l, OverlapLiteral r => String.eqb l r
  | OverlapLexicalClass l, OverlapLexicalClass r => String.eqb l r
  | OverlapEof, OverlapEof => true
  | OverlapEpsilon, OverlapEpsilon => true
  | _, _ => false
  end.

Fixpoint token_mem (token : OverlapToken) (tokens : list OverlapToken) : bool :=
  match tokens with
  | [] => false
  | candidate :: rest =>
      if overlap_token_eqb token candidate then true else token_mem token rest
  end.

Definition token_insert (token : OverlapToken) (tokens : list OverlapToken)
  : list OverlapToken :=
  if token_mem token tokens then tokens else token :: tokens.

Fixpoint token_union (left right : list OverlapToken) : list OverlapToken :=
  match left with
  | [] => right
  | token :: rest => token_union rest (token_insert token right)
  end.

Fixpoint lookup_tokens
  (name : string)
  (facts : list (string * list OverlapToken)) : list OverlapToken :=
  match facts with
  | [] => []
  | (candidate, value) :: rest =>
      if String.eqb name candidate then value else lookup_tokens name rest
  end.

Fixpoint nullable_expression_fuel
  (fuel : nat)
  (facts : list (string * bool))
  (expression : EbnfExpression) : option bool :=
  match fuel with
  | O => None
  | S remaining =>
      match expression with
      | ELiteral _ => Some false
      | ELexicalClass _ => Some false
      | ENonterminal name => Some (lookup_bool name facts)
      | ESequence items =>
          let fix nullable_sequence_local
            (pending : list EbnfExpression) : option bool :=
            match pending with
            | [] => Some true
            | item :: rest =>
                match nullable_expression_fuel remaining facts item,
                      nullable_sequence_local rest with
                | Some head, Some tail => Some (andb head tail)
                | _, _ => None
                end
            end
          in nullable_sequence_local items
      | EAlternative items =>
          let fix nullable_alternative_local
            (pending : list EbnfExpression) : option bool :=
            match pending with
            | [] => Some false
            | item :: rest =>
                match nullable_expression_fuel remaining facts item,
                      nullable_alternative_local rest with
                | Some head, Some tail => Some (orb head tail)
                | _, _ => None
                end
            end
          in nullable_alternative_local items
      | EOptional _ => Some true
      | ERepetition _ => Some true
      end
  end.

Definition expression_fuel : nat := 256.

Definition nullable_expression
  (facts : list (string * bool))
  (expression : EbnfExpression) : bool :=
  match nullable_expression_fuel expression_fuel facts expression with
  | Some value => value
  | None => false
  end.

Fixpoint nullable_pass
  (rules : list GrammarRule)
  (facts : list (string * bool)) : list (string * bool) :=
  match rules with
  | [] => []
  | (name, expression) :: rest =>
      (name, nullable_expression facts expression) :: nullable_pass rest facts
  end.

Fixpoint initial_nullable (rules : list GrammarRule) : list (string * bool) :=
  match rules with
  | [] => []
  | (name, _) :: rest => (name, false) :: initial_nullable rest
  end.

Fixpoint iterate_nullable
  (fuel : nat)
  (rules : list GrammarRule)
  (facts : list (string * bool)) : list (string * bool) :=
  match fuel with
  | O => facts
  | S remaining => iterate_nullable remaining rules (nullable_pass rules facts)
  end.

Definition phase1_surface_nullable_facts : list (string * bool) :=
  iterate_nullable 128 phase1_surface_rules (initial_nullable phase1_surface_rules).

Definition nullable_rule_fuel_sufficient (rule : GrammarRule) : bool :=
  match rule with
  | (_, expression) =>
      match nullable_expression_fuel
        expression_fuel phase1_surface_nullable_facts expression with
      | Some _ => true
      | None => false
      end
  end.

Theorem phase1_surface_nullable_expression_fuel_is_sufficient :
  forallb nullable_rule_fuel_sufficient phase1_surface_rules = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem phase1_surface_nullable_facts_are_stable :
  nullable_pass phase1_surface_rules phase1_surface_nullable_facts =
  phase1_surface_nullable_facts.
Proof.
  vm_compute.
  reflexivity.
Qed.

Fixpoint first_expression_fuel
  (fuel : nat)
  (nullable_facts : list (string * bool))
  (first_facts : list (string * list OverlapToken))
  (expression : EbnfExpression) : option (list OverlapToken) :=
  match fuel with
  | O => None
  | S remaining =>
      match expression with
      | ELiteral literal => Some [OverlapLiteral literal]
      | ELexicalClass class => Some [OverlapLexicalClass class]
      | ENonterminal name => Some (lookup_tokens name first_facts)
      | ESequence items =>
          let fix first_sequence_local
            (pending : list EbnfExpression) : option (list OverlapToken) :=
            match pending with
            | [] => Some []
            | item :: rest =>
                match first_expression_fuel
                        remaining nullable_facts first_facts item,
                      nullable_expression_fuel remaining nullable_facts item with
                | Some head, Some true =>
                    match first_sequence_local rest with
                    | Some tail => Some (token_union head tail)
                    | None => None
                    end
                | Some head, Some false => Some head
                | _, _ => None
                end
            end
          in first_sequence_local items
      | EAlternative items =>
          let fix first_alternative_local
            (pending : list EbnfExpression) : option (list OverlapToken) :=
            match pending with
            | [] => Some []
            | item :: rest =>
                match first_expression_fuel
                        remaining nullable_facts first_facts item,
                      first_alternative_local rest with
                | Some head, Some tail => Some (token_union head tail)
                | _, _ => None
                end
            end
          in first_alternative_local items
      | EOptional body =>
          first_expression_fuel remaining nullable_facts first_facts body
      | ERepetition body =>
          first_expression_fuel remaining nullable_facts first_facts body
      end
  end.

Definition first_expression
  (nullable_facts : list (string * bool))
  (first_facts : list (string * list OverlapToken))
  (expression : EbnfExpression) : list OverlapToken :=
  match first_expression_fuel
    expression_fuel nullable_facts first_facts expression with
  | Some value => value
  | None => []
  end.

Fixpoint first_pass
  (rules : list GrammarRule)
  (nullable_facts : list (string * bool))
  (first_facts : list (string * list OverlapToken))
  : list (string * list OverlapToken) :=
  match rules with
  | [] => []
  | (name, expression) :: rest =>
      (name, first_expression nullable_facts first_facts expression)
        :: first_pass rest nullable_facts first_facts
  end.

Fixpoint initial_first
  (rules : list GrammarRule) : list (string * list OverlapToken) :=
  match rules with
  | [] => []
  | (name, _) :: rest => (name, []) :: initial_first rest
  end.

Fixpoint iterate_first
  (fuel : nat)
  (rules : list GrammarRule)
  (nullable_facts : list (string * bool))
  (first_facts : list (string * list OverlapToken))
  : list (string * list OverlapToken) :=
  match fuel with
  | O => first_facts
  | S remaining =>
      iterate_first remaining rules nullable_facts
        (first_pass rules nullable_facts first_facts)
  end.

Definition phase1_surface_first_facts : list (string * list OverlapToken) :=
  iterate_first 256 phase1_surface_rules phase1_surface_nullable_facts
    (initial_first phase1_surface_rules).

Definition first_rule_fuel_sufficient (rule : GrammarRule) : bool :=
  match rule with
  | (_, expression) =>
      match first_expression_fuel
        expression_fuel phase1_surface_nullable_facts
        phase1_surface_first_facts expression with
      | Some _ => true
      | None => false
      end
  end.

Theorem phase1_surface_first_expression_fuel_is_sufficient :
  forallb first_rule_fuel_sufficient phase1_surface_rules = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem phase1_surface_first_facts_are_stable :
  first_pass phase1_surface_rules phase1_surface_nullable_facts
    phase1_surface_first_facts = phase1_surface_first_facts.
Proof.
  vm_compute.
  reflexivity.
Qed.
