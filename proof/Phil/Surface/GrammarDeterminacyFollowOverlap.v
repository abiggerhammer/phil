From Stdlib Require Import Bool.Bool Lists.List Strings.String.

From Phil.Surface Require Import
  Grammar
  GrammarDeterminacyCertificate
  GrammarDeterminacyNullableFirst.

Import ListNotations.
Open Scope string_scope.

(*
  FOLLOW propagation and exact local-overlap enumeration for the current
  generated Grammar-v1 tree.

  #569 established nullable/FIRST fixed points directly over Grammar.v.  This
  file continues the proof-facing audit in Rocq: it computes the FOLLOW fixed
  point, traverses every generated EBNF node with the same local-overlap rules,
  and checks that the resulting finite set is exactly the generated 15-site
  certificate from #565 (mutual membership plus exact cardinality).

  This still does not prove that any certified overlap is harmless.  Resolver
  lemmas and the admissible-oracle bridge remain successor work.
*)

Definition FollowFacts : Type := list (string * list OverlapToken).

Fixpoint update_tokens
  (name : string)
  (additions : list OverlapToken)
  (facts : FollowFacts) : FollowFacts :=
  match facts with
  | [] => [(name, additions)]
  | (candidate, tokens) :: rest =>
      if String.eqb name candidate
      then (candidate, token_union additions tokens) :: rest
      else (candidate, tokens) :: update_tokens name additions rest
  end.

Fixpoint initial_follow (rules : list GrammarRule) : FollowFacts :=
  match rules with
  | [] => []
  | (name, _) :: rest =>
      (name,
        if String.eqb name phase1_surface_start
        then [OverlapEof]
        else []) :: initial_follow rest
  end.

Fixpoint follow_expression_fuel
  (fuel : nat)
  (outer_follow : list OverlapToken)
  (facts : FollowFacts)
  (expression : EbnfExpression) : option FollowFacts :=
  match fuel with
  | O => None
  | S remaining =>
      match expression with
      | ELiteral _ => Some facts
      | ELexicalClass _ => Some facts
      | ENonterminal name => Some (update_tokens name outer_follow facts)
      | ESequence items =>
          let fix follow_sequence_local
            (pending : list EbnfExpression)
            (current : FollowFacts) : option FollowFacts :=
            match pending with
            | [] => Some current
            | item :: rest =>
                let suffix := ESequence rest in
                let suffix_first :=
                  first_expression
                    phase1_surface_nullable_facts
                    phase1_surface_first_facts
                    suffix in
                let local_follow :=
                  if nullable_expression phase1_surface_nullable_facts suffix
                  then token_union suffix_first outer_follow
                  else suffix_first in
                match follow_expression_fuel
                        remaining local_follow current item with
                | Some next => follow_sequence_local rest next
                | None => None
                end
            end
          in follow_sequence_local items facts
      | EAlternative items =>
          let fix follow_alternative_local
            (pending : list EbnfExpression)
            (current : FollowFacts) : option FollowFacts :=
            match pending with
            | [] => Some current
            | item :: rest =>
                match follow_expression_fuel
                        remaining outer_follow current item with
                | Some next => follow_alternative_local rest next
                | None => None
                end
            end
          in follow_alternative_local items facts
      | EOptional body =>
          follow_expression_fuel remaining outer_follow facts body
      | ERepetition body =>
          let repeated_follow :=
            token_union
              (first_expression
                phase1_surface_nullable_facts
                phase1_surface_first_facts
                body)
              outer_follow in
          follow_expression_fuel remaining repeated_follow facts body
      end
  end.

Fixpoint follow_pass_rules
  (rules : list GrammarRule)
  (facts : FollowFacts) : option FollowFacts :=
  match rules with
  | [] => Some facts
  | (name, expression) :: rest =>
      match follow_expression_fuel
              expression_fuel
              (lookup_tokens name facts)
              facts
              expression with
      | Some next => follow_pass_rules rest next
      | None => None
      end
  end.

Definition follow_pass (facts : FollowFacts) : FollowFacts :=
  match follow_pass_rules phase1_surface_rules facts with
  | Some next => next
  | None => facts
  end.

Fixpoint iterate_follow (fuel : nat) (facts : FollowFacts) : FollowFacts :=
  match fuel with
  | O => facts
  | S remaining => iterate_follow remaining (follow_pass facts)
  end.

Definition phase1_surface_follow_facts : FollowFacts :=
  iterate_follow 128 (initial_follow phase1_surface_rules).

Definition follow_rule_fuel_sufficient (rule : GrammarRule) : bool :=
  match rule with
  | (name, expression) =>
      match follow_expression_fuel
        expression_fuel
        (lookup_tokens name phase1_surface_follow_facts)
        phase1_surface_follow_facts
        expression with
      | Some _ => true
      | None => false
      end
  end.

Theorem phase1_surface_follow_expression_fuel_is_sufficient :
  forallb follow_rule_fuel_sufficient phase1_surface_rules = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem phase1_surface_follow_facts_are_stable :
  follow_pass phase1_surface_follow_facts = phase1_surface_follow_facts.
Proof.
  vm_compute.
  reflexivity.
Qed.

Fixpoint token_intersection
  (left right : list OverlapToken) : list OverlapToken :=
  match left with
  | [] => []
  | token :: rest =>
      if token_mem token right
      then token :: token_intersection rest right
      else token_intersection rest right
  end.

Definition index_string (index : nat) : string :=
  match index with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
  | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | 9 => "9"
  | 10 => "10" | 11 => "11" | 12 => "12" | 13 => "13" | 14 => "14"
  | 15 => "15" | 16 => "16" | 17 => "17" | 18 => "18" | 19 => "19"
  | 20 => "20"
  | _ => "many"
  end.

Definition indexed_step (kind : string) (index : nat) : string :=
  String.append kind
    (String.append "[" (String.append (index_string index) "]")).

Definition child_path (path step : string) : string :=
  String.append path (String.append "/" step).

Definition branch_detail (left right : nat) : string :=
  String.append "branches "
    (String.append (index_string left)
      (String.append " and " (index_string right))).

Definition make_overlap_site
  (kind : OverlapKind)
  (rule path : string)
  (tokens : list OverlapToken)
  (detail : string) : OverlapSite :=
  {| overlap_kind := kind;
     overlap_rule := rule;
     overlap_path := path;
     overlap_tokens := tokens;
     overlap_detail := detail |}.

Definition site_if_tokens
  (kind : OverlapKind)
  (rule path : string)
  (tokens : list OverlapToken)
  (detail : string) : list OverlapSite :=
  match tokens with
  | [] => []
  | _ => [make_overlap_site kind rule path tokens detail]
  end.

Fixpoint alternative_against_rest
  (rule path : string)
  (left_index right_index : nat)
  (left : EbnfExpression)
  (rights : list EbnfExpression) : list OverlapSite :=
  match rights with
  | [] => []
  | right_expression :: rest =>
      let shared :=
        token_intersection
          (first_expression
            phase1_surface_nullable_facts phase1_surface_first_facts left)
          (first_expression
            phase1_surface_nullable_facts phase1_surface_first_facts right_expression) in
      let shared_with_epsilon :=
        if andb
             (nullable_expression phase1_surface_nullable_facts left)
             (nullable_expression phase1_surface_nullable_facts right_expression)
        then token_insert OverlapEpsilon shared
        else shared in
      List.app
        (site_if_tokens
          AlternativeFirstOverlap rule path shared_with_epsilon
          (branch_detail left_index right_index))
        (alternative_against_rest
          rule path left_index (S right_index) left rest)
  end.

Fixpoint alternative_pair_sites
  (rule path : string)
  (left_index : nat)
  (items : list EbnfExpression) : list OverlapSite :=
  match items with
  | [] => []
  | left_expression :: rest =>
      List.app
        (alternative_against_rest
          rule path left_index (S left_index) left_expression rest)
        (alternative_pair_sites rule path (S left_index) rest)
  end.

Fixpoint enumerate_overlap_expression_fuel
  (fuel : nat)
  (rule path : string)
  (outer_follow : list OverlapToken)
  (expression : EbnfExpression) : option (list OverlapSite) :=
  match fuel with
  | O => None
  | S remaining =>
      match expression with
      | ELiteral _ => Some []
      | ELexicalClass _ => Some []
      | ENonterminal _ => Some []
      | ESequence items =>
          let fix enumerate_sequence_local
            (index : nat)
            (pending : list EbnfExpression) : option (list OverlapSite) :=
            match pending with
            | [] => Some []
            | item :: rest =>
                let suffix := ESequence rest in
                let suffix_first :=
                  first_expression
                    phase1_surface_nullable_facts
                    phase1_surface_first_facts
                    suffix in
                let local_follow :=
                  if nullable_expression phase1_surface_nullable_facts suffix
                  then token_union suffix_first outer_follow
                  else suffix_first in
                match enumerate_overlap_expression_fuel
                        remaining rule
                        (child_path path (indexed_step "seq" index))
                        local_follow item,
                      enumerate_sequence_local (S index) rest with
                | Some head, Some tail => Some (List.app head tail)
                | _, _ => None
                end
            end
          in enumerate_sequence_local 0 items
      | EAlternative items =>
          let fix enumerate_alternative_local
            (index : nat)
            (pending : list EbnfExpression) : option (list OverlapSite) :=
            match pending with
            | [] => Some []
            | item :: rest =>
                match enumerate_overlap_expression_fuel
                        remaining rule
                        (child_path path (indexed_step "alt" index))
                        outer_follow item,
                      enumerate_alternative_local (S index) rest with
                | Some head, Some tail => Some (List.app head tail)
                | _, _ => None
                end
            end
          in
          match enumerate_alternative_local 0 items with
          | Some nested =>
              Some (List.app (alternative_pair_sites rule path 0 items) nested)
          | None => None
          end
      | EOptional body =>
          let shared :=
            token_intersection
              (first_expression
                phase1_surface_nullable_facts phase1_surface_first_facts body)
              outer_follow in
          let shared_with_epsilon :=
            if nullable_expression phase1_surface_nullable_facts body
            then token_insert OverlapEpsilon shared
            else shared in
          match enumerate_overlap_expression_fuel
                  remaining rule (child_path path "optional") outer_follow body with
          | Some nested =>
              Some
                (List.app
                  (site_if_tokens
                    OptionalFollowOverlap rule path shared_with_epsilon
                    "optional body can begin with a token that can also follow the optional")
                  nested)
          | None => None
          end
      | ERepetition body =>
          let first_body :=
            first_expression
              phase1_surface_nullable_facts phase1_surface_first_facts body in
          let shared := token_intersection first_body outer_follow in
          let nullable_site :=
            if nullable_expression phase1_surface_nullable_facts body
            then [make_overlap_site
                    NullableRepetition rule path [OverlapEpsilon]
                    "repetition body is nullable"]
            else [] in
          let repeat_site :=
            site_if_tokens
              RepeatFollowOverlap rule path shared
              "another repetition can begin with a token that can also follow the repetition" in
          let repeated_follow := token_union first_body outer_follow in
          match enumerate_overlap_expression_fuel
                  remaining rule (child_path path "repeat") repeated_follow body with
          | Some nested =>
              Some (List.app nullable_site (List.app repeat_site nested))
          | None => None
          end
      end
  end.

Fixpoint enumerate_overlap_rules
  (rules : list GrammarRule) : option (list OverlapSite) :=
  match rules with
  | [] => Some []
  | (name, expression) :: rest =>
      match enumerate_overlap_expression_fuel
              expression_fuel name name
              (lookup_tokens name phase1_surface_follow_facts)
              expression,
            enumerate_overlap_rules rest with
      | Some head, Some tail => Some (List.app head tail)
      | _, _ => None
      end
  end.

Definition phase1_surface_computed_overlap_option : option (list OverlapSite) :=
  enumerate_overlap_rules phase1_surface_rules.

Definition phase1_surface_computed_overlaps : list OverlapSite :=
  match phase1_surface_computed_overlap_option with
  | Some sites => sites
  | None => []
  end.

Definition overlap_kind_eqb (left right : OverlapKind) : bool :=
  match left, right with
  | AlternativeFirstOverlap, AlternativeFirstOverlap => true
  | OptionalFollowOverlap, OptionalFollowOverlap => true
  | RepeatFollowOverlap, RepeatFollowOverlap => true
  | NullableRepetition, NullableRepetition => true
  | _, _ => false
  end.

Fixpoint overlap_token_list_eqb
  (left right : list OverlapToken) : bool :=
  match left, right with
  | [], [] => true
  | l :: ls, r :: rs =>
      andb (overlap_token_eqb l r) (overlap_token_list_eqb ls rs)
  | _, _ => false
  end.

Definition overlap_site_eqb (left right : OverlapSite) : bool :=
  andb (overlap_kind_eqb (overlap_kind left) (overlap_kind right))
  (andb (String.eqb (overlap_rule left) (overlap_rule right))
  (andb (String.eqb (overlap_path left) (overlap_path right))
  (andb (overlap_token_list_eqb
          (overlap_tokens left) (overlap_tokens right))
        (String.eqb (overlap_detail left) (overlap_detail right))))).

Fixpoint overlap_site_mem
  (site : OverlapSite)
  (sites : list OverlapSite) : bool :=
  match sites with
  | [] => false
  | candidate :: rest =>
      if overlap_site_eqb site candidate
      then true
      else overlap_site_mem site rest
  end.

Definition all_overlap_sites_in
  (left right : list OverlapSite) : bool :=
  forallb (fun site => overlap_site_mem site right) left.

Theorem phase1_surface_overlap_enumeration_fuel_is_sufficient :
  match phase1_surface_computed_overlap_option with
  | Some _ => true
  | None => false
  end = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem phase1_surface_computed_overlap_cardinality_is_exact :
  List.length phase1_surface_computed_overlaps = 15.
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem phase1_surface_overlap_certificate_is_complete_for_computed_grammar :
  andb
    (all_overlap_sites_in
      phase1_surface_computed_overlaps
      phase1_surface_determinacy_certificate)
    (all_overlap_sites_in
      phase1_surface_determinacy_certificate
      phase1_surface_computed_overlaps) = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Definition phase1_surface_pattern_follow : list OverlapToken :=
  lookup_tokens "pattern" phase1_surface_follow_facts.

Theorem phase1_surface_pattern_follow_structural_tail_check_true :
  andb
    (negb
      (token_mem
        (OverlapLiteral ".") phase1_surface_pattern_follow))
    (negb
      (token_mem
        (OverlapLiteral "{") phase1_surface_pattern_follow)) = true.
Proof.
  vm_compute.
  reflexivity.
Qed.
