From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyCertificate
  GrammarDeterminacyFollowOverlap.

Import ListNotations.
Open Scope string_scope.

(*
  First resolver tranche for PHIL-SURFACE-DETERM-001.

  The proof-facing nullable/FIRST/FOLLOW traversal computes exactly the same
  local overlap set as the generated certificate.  This file binds the overlap
  sites decidable from a small fixed token prefix to three resolver families:

    - reserved keyword versus IDENTIFIER continuation (2 sites),
    - comma-list continuation versus closing/trailing-comma termination (5), and
    - maximal qualified-name repetition on "." IDENTIFIER (1).

  ConcreteToken already represents the admitted lexical contract at the proof
  boundary: literal tokens and lexical-class tokens are distinct constructors.
  Source-byte/lexer correspondence remains PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Theorem literal_token_and_identifier_token_are_disjoint :
  forall literal lexeme,
    TLiteral literal <> TLexical "IDENTIFIER" lexeme.
Proof.
  intros literal lexeme Hequal.
  discriminate Hequal.
Qed.

Definition site_key_matches
  (site : OverlapSite)
  (kind : OverlapKind)
  (rule path : string)
  (tokens : list OverlapToken) : bool :=
  andb (overlap_kind_eqb (overlap_kind site) kind)
  (andb (String.eqb (overlap_rule site) rule)
  (andb (String.eqb (overlap_path site) path)
        (overlap_token_list_eqb (overlap_tokens site) tokens))).

Definition reserved_keyword_resolver_siteb (site : OverlapSite) : bool :=
  orb
    (site_key_matches site AlternativeFirstOverlap
      "declaration" "declaration" [OverlapLiteral "provider"])
    (site_key_matches site AlternativeFirstOverlap
      "generic_requirement" "generic_requirement" [OverlapLiteral "boundary"]).

Definition trailing_comma_resolver_siteb (site : OverlapSite) : bool :=
  orb
    (site_key_matches site RepeatFollowOverlap
      "case_pattern"
      "case_pattern/seq[1]/optional/alt[1]/seq[1]/optional/seq[1]"
      [OverlapLiteral ","])
  (orb
    (site_key_matches site RepeatFollowOverlap
      "construct_expression"
      "construct_expression/seq[3]/optional/seq[1]"
      [OverlapLiteral ","])
  (orb
    (site_key_matches site RepeatFollowOverlap
      "record_decl"
      "record_decl/seq[6]/optional/seq[1]"
      [OverlapLiteral ","])
  (orb
    (site_key_matches site RepeatFollowOverlap
      "record_pattern"
      "record_pattern/seq[3]"
      [OverlapLiteral ","])
    (site_key_matches site RepeatFollowOverlap
      "variant_payload"
      "variant_payload/alt[0]/seq[1]/optional/seq[1]"
      [OverlapLiteral ","])))) .

Definition qualified_name_repeat_resolver_siteb (site : OverlapSite) : bool :=
  site_key_matches site RepeatFollowOverlap
    "qualified_name" "qualified_name/seq[1]" [OverlapLiteral "."].

Definition simple_resolver_siteb (site : OverlapSite) : bool :=
  orb
    (reserved_keyword_resolver_siteb site)
    (orb
      (trailing_comma_resolver_siteb site)
      (qualified_name_repeat_resolver_siteb site)).

Theorem phase1_surface_reserved_keyword_resolver_sites_are_exactly_two :
  List.length
    (filter reserved_keyword_resolver_siteb
      phase1_surface_determinacy_certificate) = 2.
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem phase1_surface_trailing_comma_resolver_sites_are_exactly_five :
  List.length
    (filter trailing_comma_resolver_siteb
      phase1_surface_determinacy_certificate) = 5.
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem phase1_surface_qualified_name_repeat_resolver_site_is_unique :
  List.length
    (filter qualified_name_repeat_resolver_siteb
      phase1_surface_determinacy_certificate) = 1.
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem phase1_surface_simple_resolver_sites_are_exactly_eight :
  List.length
    (filter simple_resolver_siteb phase1_surface_determinacy_certificate) = 8.
Proof.
  vm_compute.
  reflexivity.
Qed.

Definition syntax_path_step_eqb
  (first_step second_step : SyntaxPathStep) : bool :=
  match first_step, second_step with
  | AtNonterminal first_name, AtNonterminal second_name =>
      String.eqb first_name second_name
  | AtSequence first_index, AtSequence second_index =>
      Nat.eqb first_index second_index
  | AtAlternative first_index, AtAlternative second_index =>
      Nat.eqb first_index second_index
  | AtOptionalBody, AtOptionalBody => true
  | AtRepetitionBody, AtRepetitionBody => true
  | _, _ => false
  end.

Fixpoint reversed_path_prefixb
  (expected actual : list SyntaxPathStep) : bool :=
  match expected, actual with
  | [], _ => true
  | _, [] => false
  | expected_step :: expected_rest, actual_step :: actual_rest =>
      andb
        (syntax_path_step_eqb expected_step actual_step)
        (reversed_path_prefixb expected_rest actual_rest)
  end.

Definition path_has_suffixb
  (path suffix : SyntaxPath) : bool :=
  reversed_path_prefixb (rev suffix) (rev path).

Definition provider_declaration_suffix : SyntaxPath :=
  [AtNonterminal "declaration"].

Definition generic_requirement_suffix : SyntaxPath :=
  [AtNonterminal "generic_requirement"].

Definition case_pattern_comma_repeat_suffix : SyntaxPath :=
  [AtNonterminal "case_pattern";
   AtSequence 1;
   AtOptionalBody;
   AtAlternative 1;
   AtSequence 1;
   AtOptionalBody;
   AtSequence 1].

Definition construct_expression_comma_repeat_suffix : SyntaxPath :=
  [AtNonterminal "construct_expression";
   AtSequence 3;
   AtOptionalBody;
   AtSequence 1].

Definition record_decl_comma_repeat_suffix : SyntaxPath :=
  [AtNonterminal "record_decl";
   AtSequence 6;
   AtOptionalBody;
   AtSequence 1].

Definition record_pattern_comma_repeat_suffix : SyntaxPath :=
  [AtNonterminal "record_pattern";
   AtSequence 3].

Definition variant_payload_comma_repeat_suffix : SyntaxPath :=
  [AtNonterminal "variant_payload";
   AtAlternative 0;
   AtSequence 1;
   AtOptionalBody;
   AtSequence 1].

Definition trailing_comma_repeat_pathb (path : SyntaxPath) : bool :=
  orb (path_has_suffixb path case_pattern_comma_repeat_suffix)
  (orb (path_has_suffixb path construct_expression_comma_repeat_suffix)
  (orb (path_has_suffixb path record_decl_comma_repeat_suffix)
  (orb (path_has_suffixb path record_pattern_comma_repeat_suffix)
       (path_has_suffixb path variant_payload_comma_repeat_suffix)))).

Definition qualified_name_repeat_suffix : SyntaxPath :=
  [AtNonterminal "qualified_name"; AtSequence 1].

Definition qualified_name_repeat_pathb (path : SyntaxPath) : bool :=
  path_has_suffixb path qualified_name_repeat_suffix.

Definition provider_declaration_decision
  (input : list ConcreteToken) : option OracleDecision :=
  match input with
  | TLiteral first_literal :: remaining =>
      if String.eqb first_literal "provider"
      then
        match remaining with
        | TLiteral second_literal :: _ =>
            if String.eqb second_literal "implementation"
            then Some (ChooseAlternative 7)
            else None
        | TLexical class_name _ :: _ =>
            if String.eqb class_name "IDENTIFIER"
            then Some (ChooseAlternative 6)
            else None
        | [] => None
        end
      else None
  | _ => None
  end.

Definition generic_requirement_decision
  (input : list ConcreteToken) : option OracleDecision :=
  match input with
  | TLiteral first_literal :: remaining =>
      if String.eqb first_literal "boundary"
      then
        match remaining with
        | TLiteral second_literal :: _ =>
            if String.eqb second_literal "representation"
            then Some (ChooseAlternative 8)
            else None
        | TLexical class_name _ :: _ =>
            if String.eqb class_name "IDENTIFIER"
            then Some (ChooseAlternative 4)
            else None
        | [] => None
        end
      else None
  | _ => None
  end.

Definition trailing_comma_repeat_decision
  (input : list ConcreteToken) : option OracleDecision :=
  match input with
  | TLiteral first_literal :: remaining =>
      if String.eqb first_literal "}"
      then Some ChooseRepetitionStop
      else if String.eqb first_literal ","
      then
        match remaining with
        | TLexical class_name _ :: _ =>
            if String.eqb class_name "IDENTIFIER"
            then Some ChooseRepetitionContinue
            else None
        | TLiteral second_literal :: _ =>
            if String.eqb second_literal "}"
            then Some ChooseRepetitionStop
            else None
        | [] => None
        end
      else None
  | _ => None
  end.

Definition qualified_name_repeat_decision
  (input : list ConcreteToken) : option OracleDecision :=
  match input with
  | TLiteral separator :: TLexical class_name _ :: _ =>
      if andb
           (String.eqb separator ".")
           (String.eqb class_name "IDENTIFIER")
      then Some ChooseRepetitionContinue
      else None
  | _ => None
  end.

Definition phase1_surface_simple_resolver : DerivationOracle :=
  fun path input =>
    if path_has_suffixb path provider_declaration_suffix
    then provider_declaration_decision input
    else if path_has_suffixb path generic_requirement_suffix
    then generic_requirement_decision input
    else if trailing_comma_repeat_pathb path
    then trailing_comma_repeat_decision input
    else if qualified_name_repeat_pathb path
    then qualified_name_repeat_decision input
    else None.

Theorem provider_declaration_contract_prefix_commits_branch_six :
  provider_declaration_decision
    [TLiteral "provider"; TLexical "IDENTIFIER" "P"] =
  Some (ChooseAlternative 6).
Proof.
  reflexivity.
Qed.

Theorem provider_declaration_implementation_prefix_commits_branch_seven :
  provider_declaration_decision
    [TLiteral "provider"; TLiteral "implementation"] =
  Some (ChooseAlternative 7).
Proof.
  reflexivity.
Qed.

Theorem generic_requirement_boundary_name_commits_branch_four :
  generic_requirement_decision
    [TLiteral "boundary"; TLexical "IDENTIFIER" "B"] =
  Some (ChooseAlternative 4).
Proof.
  reflexivity.
Qed.

Theorem generic_requirement_boundary_representation_commits_branch_eight :
  generic_requirement_decision
    [TLiteral "boundary"; TLiteral "representation"] =
  Some (ChooseAlternative 8).
Proof.
  reflexivity.
Qed.

Theorem comma_then_identifier_continues_list_repetition :
  trailing_comma_repeat_decision
    [TLiteral ","; TLexical "IDENTIFIER" "field"] =
  Some ChooseRepetitionContinue.
Proof.
  reflexivity.
Qed.

Theorem comma_then_close_stops_for_trailing_comma :
  trailing_comma_repeat_decision
    [TLiteral ","; TLiteral "}"] =
  Some ChooseRepetitionStop.
Proof.
  reflexivity.
Qed.

Theorem close_without_comma_stops_list_repetition :
  trailing_comma_repeat_decision [TLiteral "}"] =
  Some ChooseRepetitionStop.
Proof.
  reflexivity.
Qed.

Theorem dot_then_identifier_continues_qualified_name :
  qualified_name_repeat_decision
    [TLiteral "."; TLexical "IDENTIFIER" "member"] =
  Some ChooseRepetitionContinue.
Proof.
  reflexivity.
Qed.

Theorem phase1_surface_simple_resolver_is_functional :
  forall path input first_decision second_decision,
    phase1_surface_simple_resolver path input = Some first_decision ->
    phase1_surface_simple_resolver path input = Some second_decision ->
    first_decision = second_decision.
Proof.
  intros path input first_decision second_decision Hfirst Hsecond.
  congruence.
Qed.
