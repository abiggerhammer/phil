From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Strings.String.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyCertificate
  GrammarDeterminacyNullableFirst
  GrammarDeterminacyFollowOverlap
  GrammarDeterminacySimpleResolvers
  GrammarDeterminacyStructuralResolvers.

Import ListNotations.
Open Scope string_scope.

(*
  Predictive oracle foundation for the final PHIL-SURFACE-DETERM-001 bridge.

  #576 gives one checked resolver for every one of the 15 exact machine-derived
  overlap sites.  Outside those sites, Grammar-v1 choice points can be selected
  from the next concrete-token shape and the mechanized nullable/FIRST facts.

  This file constructs that one path/input-indexed oracle.  It does not yet
  prove that every ordinary complete derivation follows it; that is the final
  structural-induction tranche.
*)

Definition concrete_token_shape (token : ConcreteToken) : OverlapToken :=
  match token with
  | TLiteral literal => OverlapLiteral literal
  | TLexical class_name _ => OverlapLexicalClass class_name
  end.

Definition expression_starts_inputb
  (expression : EbnfExpression)
  (input : list ConcreteToken) : bool :=
  match input with
  | [] => nullable_expression phase1_surface_nullable_facts expression
  | token :: _ =>
      token_mem (concrete_token_shape token)
        (first_expression
          phase1_surface_nullable_facts
          phase1_surface_first_facts
          expression)
  end.

Fixpoint first_matching_alternative
  (index : nat)
  (items : list EbnfExpression)
  (input : list ConcreteToken) : option nat :=
  match items with
  | [] => None
  | item :: rest =>
      if expression_starts_inputb item input
      then Some index
      else first_matching_alternative (S index) rest input
  end.

Definition predictive_fallback_decision
  (expression : EbnfExpression)
  (input : list ConcreteToken) : option OracleDecision :=
  match expression with
  | EAlternative items =>
      match first_matching_alternative 0 items input with
      | Some index => Some (ChooseAlternative index)
      | None => None
      end
  | EOptional body =>
      if expression_starts_inputb body input
      then Some ChooseOptionalPresent
      else Some ChooseOptionalAbsent
  | ERepetition body =>
      if expression_starts_inputb body input
      then Some ChooseRepetitionContinue
      else Some ChooseRepetitionStop
  | _ => None
  end.

Definition step_expression
  (rules : list GrammarRule)
  (expression : EbnfExpression)
  (step : SyntaxPathStep) : option EbnfExpression :=
  match step, expression with
  | AtNonterminal wanted, ENonterminal actual =>
      if String.eqb wanted actual then lookupRule wanted rules else None
  | AtSequence index, ESequence items => nth_error items index
  | AtAlternative index, EAlternative items => nth_error items index
  | AtOptionalBody, EOptional body => Some body
  | AtRepetitionBody, ERepetition body => Some body
  | _, _ => None
  end.

Fixpoint expression_at_path
  (rules : list GrammarRule)
  (expression : EbnfExpression)
  (path : SyntaxPath) : option EbnfExpression :=
  match path with
  | [] => Some expression
  | step :: rest =>
      match step_expression rules expression step with
      | Some next => expression_at_path rules next rest
      | None => None
      end
  end.

Definition phase1_surface_root_expression : EbnfExpression :=
  ENonterminal phase1_surface_start.

Definition phase1_surface_expression_at_path
  (path : SyntaxPath) : option EbnfExpression :=
  expression_at_path
    phase1_surface_rules
    phase1_surface_root_expression
    path.

Theorem expression_at_path_app :
  forall rules expression prefix suffix,
    expression_at_path rules expression (List.app prefix suffix) =
    match expression_at_path rules expression prefix with
    | Some middle => expression_at_path rules middle suffix
    | None => None
    end.
Proof.
  intros rules expression prefix.
  revert expression.
  induction prefix as [| step rest IH]; intros expression suffix; simpl.
  - reflexivity.
  - destruct (step_expression rules expression step) as [next|] eqn:Hstep;
      simpl.
    + apply IH.
    + reflexivity.
Qed.

Theorem phase1_surface_expression_at_descend :
  forall path expression step,
    phase1_surface_expression_at_path path = Some expression ->
    phase1_surface_expression_at_path (descend path step) =
      step_expression phase1_surface_rules expression step.
Proof.
  intros path expression step Hpath.
  unfold phase1_surface_expression_at_path in *.
  unfold descend.
  rewrite expression_at_path_app.
  rewrite Hpath.
  simpl.
  reflexivity.
Qed.

Definition phase1_surface_predictive_oracle : DerivationOracle :=
  fun path input =>
    match phase1_surface_certified_overlap_resolver path input with
    | Some decision => Some decision
    | None =>
        match phase1_surface_expression_at_path path with
        | Some expression => predictive_fallback_decision expression input
        | None => None
        end
    end.

Theorem phase1_surface_predictive_oracle_extends_certified_overlap_resolver :
  forall path input decision,
    phase1_surface_certified_overlap_resolver path input = Some decision ->
    phase1_surface_predictive_oracle path input = Some decision.
Proof.
  intros path input decision Hresolved.
  unfold phase1_surface_predictive_oracle.
  rewrite Hresolved.
  reflexivity.
Qed.

Theorem phase1_surface_predictive_oracle_is_functional :
  forall path input first_decision second_decision,
    phase1_surface_predictive_oracle path input = Some first_decision ->
    phase1_surface_predictive_oracle path input = Some second_decision ->
    first_decision = second_decision.
Proof.
  intros path input first_decision second_decision Hfirst Hsecond.
  congruence.
Qed.

Fixpoint choice_bodies_nonnullable_fuel
  (fuel : nat)
  (expression : EbnfExpression) : bool :=
  match fuel with
  | O => false
  | S remaining =>
      match expression with
      | ELiteral _ => true
      | ELexicalClass _ => true
      | ENonterminal _ => true
      | ESequence items =>
          forallb (choice_bodies_nonnullable_fuel remaining) items
      | EAlternative items =>
          forallb
            (fun item =>
              andb
                (negb (nullable_expression phase1_surface_nullable_facts item))
                (choice_bodies_nonnullable_fuel remaining item))
            items
      | EOptional body =>
          andb
            (negb (nullable_expression phase1_surface_nullable_facts body))
            (choice_bodies_nonnullable_fuel remaining body)
      | ERepetition body =>
          andb
            (negb (nullable_expression phase1_surface_nullable_facts body))
            (choice_bodies_nonnullable_fuel remaining body)
      end
  end.

Definition choice_bodies_nonnullable_rule (rule : GrammarRule) : bool :=
  match rule with
  | (_, expression) =>
      choice_bodies_nonnullable_fuel expression_fuel expression
  end.

Theorem phase1_surface_all_choice_bodies_are_nonnullable :
  forallb choice_bodies_nonnullable_rule phase1_surface_rules = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem phase1_surface_every_machine_overlap_has_certified_resolver_family :
  forallb
    (fun site => orb
      (simple_resolver_siteb site)
      (structural_resolver_siteb site))
    phase1_surface_determinacy_certificate = true.
Proof.
  exact phase1_surface_all_fifteen_certified_sites_have_a_resolver_family.
Qed.
