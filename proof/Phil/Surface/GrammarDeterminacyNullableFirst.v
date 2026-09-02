From Stdlib Require Import Bool.Bool Lists.List Strings.String.

From Phil.Surface Require Import Grammar GrammarDeterminacyCertificate.

Import ListNotations.
Open Scope string_scope.

(*
  Mechanized nullable/FIRST foundations for the exact Grammar-v1 determinacy
  completeness bridge.  These functions operate over the generated Grammar.v
  tree rather than importing nullable/FIRST facts from the Python audit.

  This tranche establishes fixed points for the exact Phase 1 grammar only.
  FOLLOW propagation and overlap enumeration are successor work.
*)

Fixpoint lookup_bool (name : string) (facts : list (string * bool)) : bool :=
  match facts with
  | [] => false
  | (candidate, value) :: rest =>
      if String.eqb name candidate then value else lookup_bool name rest
  end.

Fixpoint overlap_token_eqb (left right : OverlapToken) : bool :=
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

Fixpoint nullable_sequence
  (facts : list (string * bool))
  (items : list EbnfExpression) : bool :=
  match items with
  | [] => true
  | item :: rest => andb (nullable_expression facts item) (nullable_sequence facts rest)
  end
with nullable_alternative
  (facts : list (string * bool))
  (items : list EbnfExpression) : bool :=
  match items with
  | [] => false
  | item :: rest => orb (nullable_expression facts item) (nullable_alternative facts rest)
  end
with nullable_expression
  (facts : list (string * bool))
  (expression : EbnfExpression) : bool :=
  match expression with
  | ELiteral _ => false
  | ELexicalClass _ => false
  | ENonterminal name => lookup_bool name facts
  | ESequence items => nullable_sequence facts items
  | EAlternative items => nullable_alternative facts items
  | EOptional _ => true
  | ERepetition _ => true
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

Theorem phase1_surface_nullable_facts_are_stable :
  nullable_pass phase1_surface_rules phase1_surface_nullable_facts =
  phase1_surface_nullable_facts.
Proof.
  vm_compute.
  reflexivity.
Qed.

Fixpoint first_sequence
  (nullable_facts : list (string * bool))
  (first_facts : list (string * list OverlapToken))
  (items : list EbnfExpression) : list OverlapToken :=
  match items with
  | [] => []
  | item :: rest =>
      let head := first_expression nullable_facts first_facts item in
      if nullable_expression nullable_facts item
      then token_union head (first_sequence nullable_facts first_facts rest)
      else head
  end
with first_alternative
  (nullable_facts : list (string * bool))
  (first_facts : list (string * list OverlapToken))
  (items : list EbnfExpression) : list OverlapToken :=
  match items with
  | [] => []
  | item :: rest =>
      token_union
        (first_expression nullable_facts first_facts item)
        (first_alternative nullable_facts first_facts rest)
  end
with first_expression
  (nullable_facts : list (string * bool))
  (first_facts : list (string * list OverlapToken))
  (expression : EbnfExpression) : list OverlapToken :=
  match expression with
  | ELiteral literal => [OverlapLiteral literal]
  | ELexicalClass class => [OverlapLexicalClass class]
  | ENonterminal name => lookup_tokens name first_facts
  | ESequence items => first_sequence nullable_facts first_facts items
  | EAlternative items => first_alternative nullable_facts first_facts items
  | EOptional body => first_expression nullable_facts first_facts body
  | ERepetition body => first_expression nullable_facts first_facts body
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

Theorem phase1_surface_first_facts_are_stable :
  first_pass phase1_surface_rules phase1_surface_nullable_facts
    phase1_surface_first_facts = phase1_surface_first_facts.
Proof.
  vm_compute.
  reflexivity.
Qed.
