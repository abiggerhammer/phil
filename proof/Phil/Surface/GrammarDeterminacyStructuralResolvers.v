From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyCertificate
  GrammarDeterminacySimpleResolvers.

Import ListNotations.
Open Scope string_scope.

(*
  Second resolver tranche for PHIL-SURFACE-DETERM-001.

  #575 bound seven simple overlap sites to checked token/path decisions.  This
  file covers the remaining eight sites with four structural resolver families:

    - maximal qualified-name commitment for pattern vs record_pattern;
    - balanced parenthesis comma/close commitment for tuple/grouped syntax;
    - brace colon/effect-set commitment for static arguments; and
    - explicit top-level relation-operator commitment for proposition atoms.

  Together with GrammarDeterminacySimpleResolvers.v this gives a functional
  path/input-indexed decision for all 15 certified overlap sites.  The successor
  proof still has to show that every ordinary Grammar-v1 derivation follows the
  combined oracle, including non-overlap choice points.
*)

Definition structural_resolver_siteb (site : OverlapSite) : bool :=
  orb
    (site_key_matches site AlternativeFirstOverlap
      "pattern" "pattern" [OverlapLexicalClass "IDENTIFIER"])
  (orb
    (site_key_matches site AlternativeFirstOverlap
      "primary_expression" "primary_expression" [OverlapLiteral "("])
  (orb
    (site_key_matches site AlternativeFirstOverlap
      "proposition_atom" "proposition_atom" [OverlapLexicalClass "IDENTIFIER"])
  (orb
    (site_key_matches site AlternativeFirstOverlap
      "proposition_atom" "proposition_atom" [OverlapLiteral "("])
  (orb
    (site_key_matches site AlternativeFirstOverlap
      "proposition_atom" "proposition_atom" [OverlapLiteral "false"])
  (orb
    (site_key_matches site AlternativeFirstOverlap
      "proposition_atom" "proposition_atom" [OverlapLiteral "true"])
  (orb
    (site_key_matches site AlternativeFirstOverlap
      "static_argument" "static_argument" [OverlapLiteral "("])
    (site_key_matches site AlternativeFirstOverlap
      "static_argument" "static_argument" [OverlapLiteral "{"]))))))).

Theorem phase1_surface_structural_resolver_sites_are_exactly_eight :
  List.length
    (filter structural_resolver_siteb phase1_surface_determinacy_certificate) = 8.
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem phase1_surface_simple_and_structural_resolver_sites_are_disjoint :
  forallb
    (fun site => negb
      (andb (simple_resolver_siteb site) (structural_resolver_siteb site)))
    phase1_surface_determinacy_certificate = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem phase1_surface_all_fifteen_certified_sites_have_a_resolver_family :
  forallb
    (fun site => orb
      (simple_resolver_siteb site) (structural_resolver_siteb site))
    phase1_surface_determinacy_certificate = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Definition pattern_suffix : SyntaxPath :=
  [AtNonterminal "pattern"].

Definition primary_expression_suffix : SyntaxPath :=
  [AtNonterminal "primary_expression"].

Definition proposition_atom_suffix : SyntaxPath :=
  [AtNonterminal "proposition_atom"].

Definition static_argument_suffix : SyntaxPath :=
  [AtNonterminal "static_argument"].

Fixpoint qualified_name_remainder
  (tokens : list ConcreteToken) : option (list ConcreteToken) :=
  match tokens with
  | TLiteral separator :: TLexical class_name _ :: rest =>
      if andb (String.eqb separator ".") (String.eqb class_name "IDENTIFIER")
      then qualified_name_remainder rest
      else Some tokens
  | _ => Some tokens
  end.

Definition pattern_decision
  (input : list ConcreteToken) : option OracleDecision :=
  match input with
  | TLexical class_name _ :: rest =>
      if String.eqb class_name "IDENTIFIER"
      then
        match rest with
        | TLiteral next_literal :: _ =>
            if String.eqb next_literal "{"
            then Some (ChooseAlternative 2)
            else if String.eqb next_literal "."
            then
              match qualified_name_remainder rest with
              | Some (TLiteral final_literal :: _) =>
                  if String.eqb final_literal "{"
                  then Some (ChooseAlternative 2)
                  else None
              | _ => None
              end
            else Some (ChooseAlternative 0)
        | _ => Some (ChooseAlternative 0)
        end
      else None
  | _ => None
  end.

Inductive ParenthesisCommit : Type :=
| CommitComma
| CommitClose.

Definition delimiter_open_literalb (literal : string) : bool :=
  orb (String.eqb literal "(")
    (orb (String.eqb literal "[") (String.eqb literal "{")).

Definition delimiter_close_literalb (literal : string) : bool :=
  orb (String.eqb literal ")")
    (orb (String.eqb literal "]") (String.eqb literal "}")).

Fixpoint parenthesis_commit_scan
  (depth : nat)
  (tokens : list ConcreteToken) : option ParenthesisCommit :=
  match tokens with
  | [] => None
  | TLiteral literal :: rest =>
      if delimiter_open_literalb literal
      then parenthesis_commit_scan (S depth) rest
      else if delimiter_close_literalb literal
      then
        match depth with
        | O =>
            if String.eqb literal ")" then Some CommitClose else None
        | S remaining_depth => parenthesis_commit_scan remaining_depth rest
        end
      else if andb (Nat.eqb depth 0) (String.eqb literal ",")
      then Some CommitComma
      else parenthesis_commit_scan depth rest
  | _ :: rest => parenthesis_commit_scan depth rest
  end.

Definition primary_expression_decision
  (input : list ConcreteToken) : option OracleDecision :=
  match input with
  | TLiteral first_literal :: rest =>
      if String.eqb first_literal "("
      then
        match parenthesis_commit_scan 0 rest with
        | Some CommitComma => Some (ChooseAlternative 0)
        | Some CommitClose => Some (ChooseAlternative 1)
        | None => None
        end
      else None
  | _ => None
  end.

Definition static_argument_parenthesis_decision
  (input : list ConcreteToken) : option OracleDecision :=
  match input with
  | TLiteral first_literal :: rest =>
      if String.eqb first_literal "("
      then
        match parenthesis_commit_scan 0 rest with
        | Some CommitComma => Some (ChooseAlternative 0)
        | Some CommitClose => Some (ChooseAlternative 2)
        | None => None
        end
      else None
  | _ => None
  end.

Definition static_argument_brace_decision
  (input : list ConcreteToken) : option OracleDecision :=
  match input with
  | TLiteral first_literal :: rest =>
      if String.eqb first_literal "{"
      then
        match rest with
        | TLiteral close_literal :: _ =>
            if String.eqb close_literal "}"
            then Some (ChooseAlternative 3)
            else None
        | TLexical class_name _ :: remaining =>
            if String.eqb class_name "IDENTIFIER"
            then
              match remaining with
              | TLiteral separator :: _ =>
                  if String.eqb separator ":"
                  then Some (ChooseAlternative 0)
                  else Some (ChooseAlternative 3)
              | _ => Some (ChooseAlternative 3)
              end
            else None
        | [] => None
        end
      else None
  | _ => None
  end.

Definition static_argument_decision
  (input : list ConcreteToken) : option OracleDecision :=
  match input with
  | TLiteral first_literal :: _ =>
      if String.eqb first_literal "("
      then static_argument_parenthesis_decision input
      else if String.eqb first_literal "{"
      then static_argument_brace_decision input
      else None
  | _ => None
  end.

Definition relation_operator_literalb (literal : string) : bool :=
  orb (String.eqb literal "==")
  (orb (String.eqb literal "!=")
  (orb (String.eqb literal "<=")
  (orb (String.eqb literal ">=")
  (orb (String.eqb literal "<")
  (orb (String.eqb literal ">")
  (orb (String.eqb literal "in")
       (String.eqb literal "disjoint"))))))).

Definition proposition_atom_boundary_literalb (literal : string) : bool :=
  orb (String.eqb literal "and")
    (orb (String.eqb literal "or")
      (orb (String.eqb literal ";")
        (orb (String.eqb literal ",")
          (orb (String.eqb literal "=>")
            (orb (String.eqb literal "then")
              (orb (String.eqb literal "within")
                (orb (String.eqb literal "{")
                     (String.eqb literal "}")))))))).

Fixpoint relation_commit_scan
  (depth : nat)
  (tokens : list ConcreteToken) : bool :=
  match tokens with
  | [] => false
  | TLiteral literal :: rest =>
      if andb
        (Nat.eqb depth 0)
        (proposition_atom_boundary_literalb literal)
      then false
      else if delimiter_open_literalb literal
      then relation_commit_scan (S depth) rest
      else if delimiter_close_literalb literal
      then
        match depth with
        | O => false
        | S remaining_depth => relation_commit_scan remaining_depth rest
        end
      else if Nat.eqb depth 0
      then
        if relation_operator_literalb literal
        then true
        else relation_commit_scan depth rest
      else relation_commit_scan depth rest
  | _ :: rest => relation_commit_scan depth rest
  end.

Definition proposition_atom_decision
  (input : list ConcreteToken) : option OracleDecision :=
  match input with
  | TLexical class_name _ :: rest =>
      if String.eqb class_name "IDENTIFIER"
      then
        if relation_commit_scan 0 rest
        then Some (ChooseAlternative 0)
        else Some (ChooseAlternative 4)
      else None
  | TLiteral first_literal :: rest =>
      if String.eqb first_literal "("
      then
        if relation_commit_scan 1 rest
        then Some (ChooseAlternative 0)
        else Some (ChooseAlternative 1)
      else if String.eqb first_literal "true"
      then
        if relation_commit_scan 0 rest
        then Some (ChooseAlternative 0)
        else Some (ChooseAlternative 2)
      else if String.eqb first_literal "false"
      then
        if relation_commit_scan 0 rest
        then Some (ChooseAlternative 0)
        else Some (ChooseAlternative 3)
      else None
  | _ => None
  end.

Definition phase1_surface_structural_resolver : DerivationOracle :=
  fun path input =>
    if path_has_suffixb path pattern_suffix
    then pattern_decision input
    else if path_has_suffixb path primary_expression_suffix
    then primary_expression_decision input
    else if path_has_suffixb path proposition_atom_suffix
    then proposition_atom_decision input
    else if path_has_suffixb path static_argument_suffix
    then static_argument_decision input
    else None.

Definition phase1_surface_certified_overlap_resolver : DerivationOracle :=
  fun path input =>
    match phase1_surface_simple_resolver path input with
    | Some decision => Some decision
    | None => phase1_surface_structural_resolver path input
    end.

Theorem pattern_identifier_alone_commits_plain_pattern :
  pattern_decision [TLexical "IDENTIFIER" "x"] =
  Some (ChooseAlternative 0).
Proof. reflexivity. Qed.

Theorem pattern_name_then_brace_commits_record_pattern :
  pattern_decision
    [TLexical "IDENTIFIER" "R"; TLiteral "{"; TLexical "IDENTIFIER" "x"] =
    Some (ChooseAlternative 2).
Proof. reflexivity. Qed.

Theorem qualified_pattern_name_then_brace_commits_record_pattern :
  pattern_decision
    [TLexical "IDENTIFIER" "M"; TLiteral "."; TLexical "IDENTIFIER" "R";
     TLiteral "{"; TLexical "IDENTIFIER" "x"] =
    Some (ChooseAlternative 2).
Proof. reflexivity. Qed.

Theorem parenthesized_expression_close_commits_grouping :
  primary_expression_decision
    [TLiteral "("; TLiteral "true"; TLiteral ")"] =
  Some (ChooseAlternative 1).
Proof. reflexivity. Qed.

Theorem parenthesized_expression_comma_commits_tuple :
  primary_expression_decision
    [TLiteral "("; TLiteral "true"; TLiteral ","; TLiteral "false";
     TLiteral ")"] =
  Some (ChooseAlternative 0).
Proof. reflexivity. Qed.

Theorem static_argument_parenthesis_close_commits_static_value :
  static_argument_decision
    [TLiteral "("; TLiteral "true"; TLiteral ")"] =
  Some (ChooseAlternative 2).
Proof. reflexivity. Qed.

Theorem static_argument_parenthesis_comma_commits_tuple_type :
  static_argument_decision
    [TLiteral "("; TLiteral "Unit"; TLiteral ","; TLiteral "Bool";
     TLiteral ")"] =
  Some (ChooseAlternative 0).
Proof. reflexivity. Qed.

Theorem static_argument_brace_colon_commits_refinement_type :
  static_argument_decision
    [TLiteral "{"; TLexical "IDENTIFIER" "x"; TLiteral ":";
     TLiteral "Unit"; TLiteral "|"; TLiteral "true"; TLiteral "}"] =
  Some (ChooseAlternative 0).
Proof. reflexivity. Qed.

Theorem static_argument_brace_name_commits_effect_set :
  static_argument_decision
    [TLiteral "{"; TLexical "IDENTIFIER" "Read"; TLiteral "}"] =
  Some (ChooseAlternative 3).
Proof. reflexivity. Qed.

Theorem proposition_true_without_relation_commits_literal :
  proposition_atom_decision [TLiteral "true"; TLiteral ";"] =
  Some (ChooseAlternative 2).
Proof. reflexivity. Qed.

Theorem proposition_true_then_tail_commits_literal :
  forall tail,
    proposition_atom_decision
      (TLiteral "true" :: TLiteral "then" :: tail) =
    Some (ChooseAlternative 2).
Proof. reflexivity. Qed.

Theorem proposition_true_within_tail_commits_literal :
  forall tail,
    proposition_atom_decision
      (TLiteral "true" :: TLiteral "within" :: tail) =
    Some (ChooseAlternative 2).
Proof. reflexivity. Qed.

Theorem proposition_true_open_brace_tail_commits_literal :
  forall tail,
    proposition_atom_decision
      (TLiteral "true" :: TLiteral "{" :: tail) =
    Some (ChooseAlternative 2).
Proof. reflexivity. Qed.

Theorem proposition_true_with_relation_commits_relation :
  proposition_atom_decision
    [TLiteral "true"; TLiteral "=="; TLiteral "false"] =
  Some (ChooseAlternative 0).
Proof. reflexivity. Qed.

Theorem proposition_false_without_relation_commits_literal :
  proposition_atom_decision [TLiteral "false"; TLiteral ";"] =
  Some (ChooseAlternative 3).
Proof. reflexivity. Qed.

Theorem proposition_name_without_relation_commits_claim_application :
  proposition_atom_decision
    [TLexical "IDENTIFIER" "Claim"; TLiteral "("; TLiteral ")";
     TLiteral ";"] =
  Some (ChooseAlternative 4).
Proof. reflexivity. Qed.

Theorem proposition_name_with_relation_commits_relation :
  proposition_atom_decision
    [TLexical "IDENTIFIER" "x"; TLiteral "==";
     TLexical "IDENTIFIER" "y"] =
  Some (ChooseAlternative 0).
Proof. reflexivity. Qed.

Theorem proposition_parentheses_without_outer_relation_commit_grouping :
  proposition_atom_decision
    [TLiteral "("; TLiteral "true"; TLiteral ")"; TLiteral ";"] =
  Some (ChooseAlternative 1).
Proof. reflexivity. Qed.

Theorem proposition_parentheses_with_outer_relation_commit_relation :
  proposition_atom_decision
    [TLiteral "("; TLexical "IDENTIFIER" "x"; TLiteral ")";
     TLiteral "=="; TLexical "IDENTIFIER" "y"] =
  Some (ChooseAlternative 0).
Proof. reflexivity. Qed.

Theorem phase1_surface_structural_resolver_is_functional :
  forall path input first_decision second_decision,
    phase1_surface_structural_resolver path input = Some first_decision ->
    phase1_surface_structural_resolver path input = Some second_decision ->
    first_decision = second_decision.
Proof.
  intros path input first_decision second_decision Hfirst Hsecond.
  congruence.
Qed.

Theorem phase1_surface_certified_overlap_resolver_is_functional :
  forall path input first_decision second_decision,
    phase1_surface_certified_overlap_resolver path input = Some first_decision ->
    phase1_surface_certified_overlap_resolver path input = Some second_decision ->
    first_decision = second_decision.
Proof.
  intros path input first_decision second_decision Hfirst Hsecond.
  congruence.
Qed.
