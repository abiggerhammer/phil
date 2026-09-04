From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyStructuralResolvers.

Import ListNotations.
Open Scope string_scope.

(*
  Scanner foundation for the eight structural resolver sites used by
  PHIL-SURFACE-DETERM-001.

  The structural resolvers deliberately inspect more than one token at the
  three genuinely shared-prefix families.  This file factors their mechanics
  into reusable state-preservation lemmas.  A later semantic tranche only has
  to prove that an ordinary derived subexpression contributes a neutral prefix;
  comma/close/relation events then force the resolver decision here.
*)

Fixpoint qualified_name_dot_tokens
  (names : list string)
  (tail : list ConcreteToken) : list ConcreteToken :=
  match names with
  | [] => tail
  | name :: rest =>
      TLiteral "." ::
      TLexical "IDENTIFIER" name ::
      qualified_name_dot_tokens rest tail
  end.

Lemma qualified_name_remainder_dot_tokens :
  forall names tail,
    qualified_name_remainder (qualified_name_dot_tokens names tail) =
    qualified_name_remainder tail.
Proof.
  induction names as [| name rest IH]; intros tail.
  - reflexivity.
  - simpl.
    exact (IH tail).
Qed.

Theorem pattern_decision_qualified_name_brace_tail :
  forall first_name more_names tail,
    pattern_decision
      (TLexical "IDENTIFIER" first_name ::
       qualified_name_dot_tokens
         more_names (TLiteral "{" :: tail)) =
    Some (ChooseAlternative 2).
Proof.
  intros first_name more_names tail.
  destruct more_names as [| next_name more_names].
  - reflexivity.
  - simpl.
    rewrite qualified_name_remainder_dot_tokens.
    destruct tail as [| token tail].
    + reflexivity.
    + destruct token; reflexivity.
Qed.

Theorem pattern_decision_identifier_other_literal_tail :
  forall lexeme literal tail,
    String.eqb literal "{" = false ->
    String.eqb literal "." = false ->
    pattern_decision
      (TLexical "IDENTIFIER" lexeme :: TLiteral literal :: tail) =
    Some (ChooseAlternative 0).
Proof.
  intros lexeme literal tail Hbrace Hdot.
  simpl.
  rewrite Hbrace, Hdot.
  reflexivity.
Qed.

Theorem pattern_decision_identifier_lexical_tail :
  forall lexeme class_name value tail,
    pattern_decision
      (TLexical "IDENTIFIER" lexeme ::
       TLexical class_name value :: tail) =
    Some (ChooseAlternative 0).
Proof.
  reflexivity.
Qed.

Theorem pattern_decision_identifier_end :
  forall lexeme,
    pattern_decision [TLexical "IDENTIFIER" lexeme] =
    Some (ChooseAlternative 0).
Proof.
  reflexivity.
Qed.

Definition parenthesis_neutral_step
  (depth : nat)
  (token : ConcreteToken) : option nat :=
  match token with
  | TLiteral literal =>
      if delimiter_open_literalb literal
      then Some (S depth)
      else if delimiter_close_literalb literal
      then
        match depth with
        | O => None
        | S remaining_depth => Some remaining_depth
        end
      else if andb (Nat.eqb depth 0) (String.eqb literal ",")
      then None
      else Some depth
  | TLexical _ _ => Some depth
  end.

Fixpoint parenthesis_neutral_scan
  (depth : nat)
  (tokens : list ConcreteToken) : option nat :=
  match tokens with
  | [] => Some depth
  | token :: rest =>
      match parenthesis_neutral_step depth token with
      | Some next_depth => parenthesis_neutral_scan next_depth rest
      | None => None
      end
  end.

Lemma parenthesis_commit_scan_after_neutral_prefix :
  forall depth prefix final_depth suffix,
    parenthesis_neutral_scan depth prefix = Some final_depth ->
    parenthesis_commit_scan depth (prefix ++ suffix) =
    parenthesis_commit_scan final_depth suffix.
Proof.
  intros depth prefix.
  revert depth.
  induction prefix as [| token prefix IH];
    intros depth final_depth suffix Hneutral.
  - simpl in Hneutral.
    inversion Hneutral.
    reflexivity.
  - destruct token as [literal | class_name lexeme].
    + simpl in Hneutral |- *.
      destruct (delimiter_open_literalb literal) eqn:Hopen.
      * eapply IH. exact Hneutral.
      * destruct (delimiter_close_literalb literal) eqn:Hclose.
        -- destruct depth as [| depth].
           ++ discriminate Hneutral.
           ++ eapply IH. exact Hneutral.
        -- destruct
             (andb (Nat.eqb depth 0) (String.eqb literal ","))
             eqn:Hcomma.
           ++ discriminate Hneutral.
           ++ eapply IH. exact Hneutral.
    + simpl in Hneutral |- *.
      eapply IH. exact Hneutral.
Qed.

Lemma parenthesis_commit_scan_neutral_comma :
  forall prefix suffix,
    parenthesis_neutral_scan 0 prefix = Some 0 ->
    parenthesis_commit_scan
      0 (prefix ++ TLiteral "," :: suffix) = Some CommitComma.
Proof.
  intros prefix suffix Hneutral.
  rewrite
    (parenthesis_commit_scan_after_neutral_prefix
      0 prefix 0 (TLiteral "," :: suffix) Hneutral).
  reflexivity.
Qed.

Lemma parenthesis_commit_scan_neutral_close :
  forall prefix suffix,
    parenthesis_neutral_scan 0 prefix = Some 0 ->
    parenthesis_commit_scan
      0 (prefix ++ TLiteral ")" :: suffix) = Some CommitClose.
Proof.
  intros prefix suffix Hneutral.
  rewrite
    (parenthesis_commit_scan_after_neutral_prefix
      0 prefix 0 (TLiteral ")" :: suffix) Hneutral).
  reflexivity.
Qed.

Theorem primary_expression_neutral_comma_commits_tuple :
  forall prefix suffix,
    parenthesis_neutral_scan 0 prefix = Some 0 ->
    primary_expression_decision
      (TLiteral "(" :: (prefix ++ TLiteral "," :: suffix)) =
    Some (ChooseAlternative 0).
Proof.
  intros prefix suffix Hneutral.
  unfold primary_expression_decision.
  simpl.
  rewrite (parenthesis_commit_scan_neutral_comma prefix suffix Hneutral).
  reflexivity.
Qed.

Theorem primary_expression_neutral_close_commits_grouping :
  forall prefix suffix,
    parenthesis_neutral_scan 0 prefix = Some 0 ->
    primary_expression_decision
      (TLiteral "(" :: (prefix ++ TLiteral ")" :: suffix)) =
    Some (ChooseAlternative 1).
Proof.
  intros prefix suffix Hneutral.
  unfold primary_expression_decision.
  simpl.
  rewrite (parenthesis_commit_scan_neutral_close prefix suffix Hneutral).
  reflexivity.
Qed.

Theorem static_argument_neutral_comma_commits_tuple_type :
  forall prefix suffix,
    parenthesis_neutral_scan 0 prefix = Some 0 ->
    static_argument_decision
      (TLiteral "(" :: (prefix ++ TLiteral "," :: suffix)) =
    Some (ChooseAlternative 0).
Proof.
  intros prefix suffix Hneutral.
  unfold static_argument_decision, static_argument_parenthesis_decision.
  simpl.
  rewrite (parenthesis_commit_scan_neutral_comma prefix suffix Hneutral).
  reflexivity.
Qed.

Theorem static_argument_neutral_close_commits_static_value :
  forall prefix suffix,
    parenthesis_neutral_scan 0 prefix = Some 0 ->
    static_argument_decision
      (TLiteral "(" :: (prefix ++ TLiteral ")" :: suffix)) =
    Some (ChooseAlternative 2).
Proof.
  intros prefix suffix Hneutral.
  unfold static_argument_decision, static_argument_parenthesis_decision.
  simpl.
  rewrite (parenthesis_commit_scan_neutral_close prefix suffix Hneutral).
  reflexivity.
Qed.

Theorem static_argument_brace_colon_tail_commits_refinement :
  forall lexeme tail,
    static_argument_decision
      (TLiteral "{" :: TLexical "IDENTIFIER" lexeme ::
       TLiteral ":" :: tail) =
    Some (ChooseAlternative 0).
Proof.
  reflexivity.
Qed.

Theorem static_argument_empty_brace_tail_commits_effect_set :
  forall tail,
    static_argument_decision
      (TLiteral "{" :: TLiteral "}" :: tail) =
    Some (ChooseAlternative 3).
Proof.
  reflexivity.
Qed.

Theorem static_argument_brace_other_separator_tail_commits_effect_set :
  forall lexeme separator tail,
    String.eqb separator ":" = false ->
    static_argument_decision
      (TLiteral "{" :: TLexical "IDENTIFIER" lexeme ::
       TLiteral separator :: tail) =
    Some (ChooseAlternative 3).
Proof.
  intros lexeme separator tail Hseparator.
  unfold static_argument_decision, static_argument_brace_decision.
  simpl.
  rewrite Hseparator.
  reflexivity.
Qed.

Definition relation_neutral_step
  (depth : nat)
  (token : ConcreteToken) : option nat :=
  match token with
  | TLiteral literal =>
      if delimiter_open_literalb literal
      then Some (S depth)
      else if delimiter_close_literalb literal
      then
        match depth with
        | O => None
        | S remaining_depth => Some remaining_depth
        end
      else if Nat.eqb depth 0
      then
        if relation_operator_literalb literal
        then None
        else if proposition_atom_boundary_literalb literal
        then None
        else Some depth
      else Some depth
  | TLexical _ _ => Some depth
  end.

Fixpoint relation_neutral_scan
  (depth : nat)
  (tokens : list ConcreteToken) : option nat :=
  match tokens with
  | [] => Some depth
  | token :: rest =>
      match relation_neutral_step depth token with
      | Some next_depth => relation_neutral_scan next_depth rest
      | None => None
      end
  end.

Lemma relation_commit_scan_after_neutral_prefix :
  forall depth prefix final_depth suffix,
    relation_neutral_scan depth prefix = Some final_depth ->
    relation_commit_scan depth (prefix ++ suffix) =
    relation_commit_scan final_depth suffix.
Proof.
  intros depth prefix.
  revert depth.
  induction prefix as [| token prefix IH];
    intros depth final_depth suffix Hneutral.
  - simpl in Hneutral.
    inversion Hneutral.
    reflexivity.
  - destruct token as [literal | class_name lexeme].
    + simpl in Hneutral |- *.
      destruct (delimiter_open_literalb literal) eqn:Hopen.
      * eapply IH. exact Hneutral.
      * destruct (delimiter_close_literalb literal) eqn:Hclose.
        -- destruct depth as [| depth].
           ++ discriminate Hneutral.
           ++ eapply IH. exact Hneutral.
        -- destruct (Nat.eqb depth 0) eqn:Hdepth.
           ++ destruct (relation_operator_literalb literal) eqn:Hoperator.
              ** discriminate Hneutral.
              ** destruct
                   (proposition_atom_boundary_literalb literal)
                   eqn:Hboundary.
                 --- discriminate Hneutral.
                 --- eapply IH. exact Hneutral.
           ++ eapply IH. exact Hneutral.
    + simpl in Hneutral |- *.
      eapply IH. exact Hneutral.
Qed.

Lemma relation_commit_scan_neutral_operator :
  forall depth prefix suffix literal,
    relation_neutral_scan depth prefix = Some 0 ->
    delimiter_open_literalb literal = false ->
    delimiter_close_literalb literal = false ->
    relation_operator_literalb literal = true ->
    relation_commit_scan
      depth (prefix ++ TLiteral literal :: suffix) = true.
Proof.
  intros depth prefix suffix literal Hneutral Hopen Hclose Hoperator.
  rewrite
    (relation_commit_scan_after_neutral_prefix
      depth prefix 0 (TLiteral literal :: suffix) Hneutral).
  simpl.
  rewrite Hopen, Hclose, Hoperator.
  reflexivity.
Qed.

Lemma relation_commit_scan_neutral_boundary :
  forall depth prefix suffix literal,
    relation_neutral_scan depth prefix = Some 0 ->
    delimiter_open_literalb literal = false ->
    delimiter_close_literalb literal = false ->
    relation_operator_literalb literal = false ->
    proposition_atom_boundary_literalb literal = true ->
    relation_commit_scan
      depth (prefix ++ TLiteral literal :: suffix) = false.
Proof.
  intros depth prefix suffix literal
    Hneutral Hopen Hclose Hoperator Hboundary.
  rewrite
    (relation_commit_scan_after_neutral_prefix
      depth prefix 0 (TLiteral literal :: suffix) Hneutral).
  simpl.
  rewrite Hopen, Hclose, Hoperator, Hboundary.
  reflexivity.
Qed.

Lemma relation_commit_scan_neutral_end :
  forall depth prefix,
    relation_neutral_scan depth prefix = Some 0 ->
    relation_commit_scan depth prefix = false.
Proof.
  intros depth prefix Hneutral.
  pose proof
    (relation_commit_scan_after_neutral_prefix
      depth prefix 0 [] Hneutral) as Hscan.
  rewrite List.app_nil_r in Hscan.
  simpl in Hscan.
  exact Hscan.
Qed.

Theorem proposition_identifier_scan_true_commits_relation :
  forall lexeme rest,
    relation_commit_scan 0 rest = true ->
    proposition_atom_decision
      (TLexical "IDENTIFIER" lexeme :: rest) =
    Some (ChooseAlternative 0).
Proof.
  intros lexeme rest Hscan.
  unfold proposition_atom_decision.
  simpl.
  rewrite Hscan.
  reflexivity.
Qed.

Theorem proposition_identifier_scan_false_commits_claim :
  forall lexeme rest,
    relation_commit_scan 0 rest = false ->
    proposition_atom_decision
      (TLexical "IDENTIFIER" lexeme :: rest) =
    Some (ChooseAlternative 4).
Proof.
  intros lexeme rest Hscan.
  unfold proposition_atom_decision.
  simpl.
  rewrite Hscan.
  reflexivity.
Qed.

Theorem proposition_parenthesis_scan_true_commits_relation :
  forall rest,
    relation_commit_scan 1 rest = true ->
    proposition_atom_decision (TLiteral "(" :: rest) =
    Some (ChooseAlternative 0).
Proof.
  intros rest Hscan.
  unfold proposition_atom_decision.
  simpl.
  rewrite Hscan.
  reflexivity.
Qed.

Theorem proposition_parenthesis_scan_false_commits_grouping :
  forall rest,
    relation_commit_scan 1 rest = false ->
    proposition_atom_decision (TLiteral "(" :: rest) =
    Some (ChooseAlternative 1).
Proof.
  intros rest Hscan.
  unfold proposition_atom_decision.
  simpl.
  rewrite Hscan.
  reflexivity.
Qed.

Theorem proposition_true_scan_true_commits_relation :
  forall rest,
    relation_commit_scan 0 rest = true ->
    proposition_atom_decision (TLiteral "true" :: rest) =
    Some (ChooseAlternative 0).
Proof.
  intros rest Hscan.
  unfold proposition_atom_decision.
  simpl.
  rewrite Hscan.
  reflexivity.
Qed.

Theorem proposition_true_scan_false_commits_literal :
  forall rest,
    relation_commit_scan 0 rest = false ->
    proposition_atom_decision (TLiteral "true" :: rest) =
    Some (ChooseAlternative 2).
Proof.
  intros rest Hscan.
  unfold proposition_atom_decision.
  simpl.
  rewrite Hscan.
  reflexivity.
Qed.

Theorem proposition_false_scan_true_commits_relation :
  forall rest,
    relation_commit_scan 0 rest = true ->
    proposition_atom_decision (TLiteral "false" :: rest) =
    Some (ChooseAlternative 0).
Proof.
  intros rest Hscan.
  unfold proposition_atom_decision.
  simpl.
  rewrite Hscan.
  reflexivity.
Qed.

Theorem proposition_false_scan_false_commits_literal :
  forall rest,
    relation_commit_scan 0 rest = false ->
    proposition_atom_decision (TLiteral "false" :: rest) =
    Some (ChooseAlternative 3).
Proof.
  intros rest Hscan.
  unfold proposition_atom_decision.
  simpl.
  rewrite Hscan.
  reflexivity.
Qed.
