From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyPredictiveOracle.

Import ListNotations.
Open Scope string_scope.

(*
  Executable reference recognizer for PHIL-SURFACE-GRAMMAR-CORR-001.

  The production Haskell parser is not made authoritative here.  Instead this
  file gives the already-proved oracle-resolved Grammar-v1 semantics an
  executable, fuel-bounded recognizer.  Later correspondence slices can prove
  completeness/fuel bounds and mechanically bind production parser acceptance
  to this grammar-derived reference decision without importing Haskell branch
  order into the language definition.
*)

Definition concrete_token_eq_dec :
  forall left right : ConcreteToken, {left = right} + {left <> right}.
Proof.
  decide equality; apply string_dec.
Defined.

Fixpoint oracle_parse_fuel
  (fuel : nat)
  (oracle : DerivationOracle)
  (rules : list GrammarRule)
  (goal : DerivationGoal)
  (input : list ConcreteToken)
  : option (list ConcreteToken * DerivationResult) :=
  match fuel with
  | 0 => None
  | S remaining =>
      match goal with
      | GoalExpression path expression =>
          match expression with
          | ELiteral literal =>
              match input with
              | TLiteral actual :: tail =>
                  if String.eqb actual literal
                  then Some (tail, ResultTree (PTLiteral literal))
                  else None
              | _ => None
              end
          | ELexicalClass class =>
              match input with
              | TLexical actual_class lexeme :: tail =>
                  if String.eqb actual_class class
                  then Some (tail, ResultTree (PTLexical class lexeme))
                  else None
              | _ => None
              end
          | ENonterminal name =>
              match lookupRule name rules with
              | Some body =>
                  match
                    oracle_parse_fuel remaining oracle rules
                      (GoalExpression
                        (descend path (AtNonterminal name)) body)
                      input
                  with
                  | Some (rest, ResultTree tree) =>
                      Some (rest, ResultTree (PTNonterminal name tree))
                  | _ => None
                  end
              | None => None
              end
          | ESequence items =>
              match
                oracle_parse_fuel remaining oracle rules
                  (GoalSequence path 0 items) input
              with
              | Some (rest, ResultTrees trees) =>
                  Some (rest, ResultTree (PTSequence trees))
              | _ => None
              end
          | EAlternative items =>
              match oracle path input with
              | Some (ChooseAlternative index) =>
                  match nth_error items index with
                  | Some item =>
                      match
                        oracle_parse_fuel remaining oracle rules
                          (GoalExpression
                            (descend path (AtAlternative index)) item)
                          input
                      with
                      | Some (rest, ResultTree tree) =>
                          Some
                            (rest, ResultTree (PTAlternative index tree))
                      | _ => None
                      end
                  | None => None
                  end
              | _ => None
              end
          | EOptional body =>
              match oracle path input with
              | Some ChooseOptionalAbsent =>
                  Some (input, ResultTree PTOptionalNone)
              | Some ChooseOptionalPresent =>
                  match
                    oracle_parse_fuel remaining oracle rules
                      (GoalExpression
                        (descend path AtOptionalBody) body)
                      input
                  with
                  | Some (rest, ResultTree tree) =>
                      Some (rest, ResultTree (PTOptionalSome tree))
                  | _ => None
                  end
              | _ => None
              end
          | ERepetition body =>
              match
                oracle_parse_fuel remaining oracle rules
                  (GoalRepetition path body) input
              with
              | Some (rest, ResultTrees trees) =>
                  Some (rest, ResultTree (PTRepetition trees))
              | _ => None
              end
          end
      | GoalSequence path index items =>
          match items with
          | [] => Some (input, ResultTrees [])
          | item :: tail_items =>
              match
                oracle_parse_fuel remaining oracle rules
                  (GoalExpression
                    (descend path (AtSequence index)) item)
                  input
              with
              | Some (middle, ResultTree tree) =>
                  match
                    oracle_parse_fuel remaining oracle rules
                      (GoalSequence path (S index) tail_items)
                      middle
                  with
                  | Some (rest, ResultTrees trees) =>
                      Some (rest, ResultTrees (tree :: trees))
                  | _ => None
                  end
              | _ => None
              end
          end
      | GoalRepetition path body =>
          match oracle path input with
          | Some ChooseRepetitionStop =>
              Some (input, ResultTrees [])
          | Some ChooseRepetitionContinue =>
              match
                oracle_parse_fuel remaining oracle rules
                  (GoalExpression
                    (descend path AtRepetitionBody) body)
                  input
              with
              | Some (middle, ResultTree tree) =>
                  match list_eq_dec concrete_token_eq_dec input middle with
                  | left _ => None
                  | right _ =>
                      match
                        oracle_parse_fuel remaining oracle rules
                          (GoalRepetition path body) middle
                      with
                      | Some (rest, ResultTrees trees) =>
                          Some (rest, ResultTrees (tree :: trees))
                      | _ => None
                      end
                  end
              | _ => None
              end
          | _ => None
          end
      end
  end.

Theorem oracle_parse_fuel_sound :
  forall fuel oracle rules goal input rest result,
    oracle_parse_fuel fuel oracle rules goal input = Some (rest, result) ->
    OracleDerives oracle rules goal input rest result.
Proof.
  induction fuel as [| fuel IH];
    intros oracle rules goal input rest result Hparse.
  - discriminate Hparse.
  - destruct goal as [path expression | path index items | path body].
    + destruct expression as
        [literal | class | name | items | items | body | body].
      * destruct input as [| token tail]; try discriminate Hparse.
        destruct token as [actual | actual_class lexeme];
          try discriminate Hparse.
        simpl in Hparse.
        destruct (String.eqb actual literal) eqn:Heq;
          try discriminate Hparse.
        apply String.eqb_eq in Heq.
        subst actual.
        inversion Hparse; subst.
        constructor.
      * destruct input as [| token tail]; try discriminate Hparse.
        destruct token as [actual | actual_class lexeme];
          try discriminate Hparse.
        simpl in Hparse.
        destruct (String.eqb actual_class class) eqn:Heq;
          try discriminate Hparse.
        apply String.eqb_eq in Heq.
        subst actual_class.
        inversion Hparse; subst.
        constructor.
      * simpl in Hparse.
        destruct (lookupRule name rules) as [child_body |] eqn:Hlookup;
          try discriminate Hparse.
        destruct
          (oracle_parse_fuel fuel oracle rules
            (GoalExpression
              (descend path (AtNonterminal name)) child_body)
            input)
          as [[child_rest child_result] |] eqn:Hchild;
          try discriminate Hparse.
        destruct child_result as [tree | trees]; try discriminate Hparse.
        inversion Hparse; subst.
        eapply oracle_nonterminal.
        -- exact Hlookup.
        -- eapply IH.
           exact Hchild.
      * simpl in Hparse.
        destruct
          (oracle_parse_fuel fuel oracle rules
            (GoalSequence path 0 items) input)
          as [[child_rest child_result] |] eqn:Hchild;
          try discriminate Hparse.
        destruct child_result as [tree | trees]; try discriminate Hparse.
        inversion Hparse; subst.
        apply oracle_sequence.
        eapply IH.
        exact Hchild.
      * simpl in Hparse.
        destruct (oracle path input) as [decision |] eqn:Hdecision;
          try discriminate Hparse.
        destruct decision as
          [chosen | | | |]; try discriminate Hparse.
        destruct (nth_error items chosen) as [item |] eqn:Hnth;
          try discriminate Hparse.
        destruct
          (oracle_parse_fuel fuel oracle rules
            (GoalExpression
              (descend path (AtAlternative chosen)) item)
            input)
          as [[child_rest child_result] |] eqn:Hchild;
          try discriminate Hparse.
        destruct child_result as [tree | trees]; try discriminate Hparse.
        inversion Hparse; subst.
        eapply oracle_alternative.
        -- exact Hdecision.
        -- exact Hnth.
        -- eapply IH.
           exact Hchild.
      * simpl in Hparse.
        destruct (oracle path input) as [decision |] eqn:Hdecision;
          try discriminate Hparse.
        destruct decision as
          [chosen | | | |]; try discriminate Hparse.
        -- inversion Hparse; subst.
           apply oracle_optional_none.
           exact Hdecision.
        -- destruct
             (oracle_parse_fuel fuel oracle rules
               (GoalExpression (descend path AtOptionalBody) body)
               input)
             as [[child_rest child_result] |] eqn:Hchild;
             try discriminate Hparse.
           destruct child_result as [tree | trees]; try discriminate Hparse.
           inversion Hparse; subst.
           apply oracle_optional_some.
           ++ exact Hdecision.
           ++ eapply IH.
              exact Hchild.
      * simpl in Hparse.
        destruct
          (oracle_parse_fuel fuel oracle rules
            (GoalRepetition path body) input)
          as [[child_rest child_result] |] eqn:Hchild;
          try discriminate Hparse.
        destruct child_result as [tree | trees]; try discriminate Hparse.
        inversion Hparse; subst.
        apply oracle_repetition.
        eapply IH.
        exact Hchild.
    + simpl in Hparse.
      destruct items as [| item tail_items].
      * inversion Hparse; subst.
        constructor.
      * destruct
          (oracle_parse_fuel fuel oracle rules
            (GoalExpression (descend path (AtSequence index)) item)
            input)
          as [[middle head_result] |] eqn:Hhead;
          try discriminate Hparse.
        destruct head_result as [tree | head_trees]; try discriminate Hparse.
        destruct
          (oracle_parse_fuel fuel oracle rules
            (GoalSequence path (S index) tail_items) middle)
          as [[tail_rest tail_result] |] eqn:Htail;
          try discriminate Hparse.
        destruct tail_result as [tail_tree | trees]; try discriminate Hparse.
        inversion Hparse; subst.
        eapply oracle_sequence_cons with (middle := middle).
        -- eapply IH.
           exact Hhead.
        -- eapply IH.
           exact Htail.
    + simpl in Hparse.
      destruct (oracle path input) as [decision |] eqn:Hdecision;
        try discriminate Hparse.
      destruct decision as
        [chosen | | | |]; try discriminate Hparse.
      * inversion Hparse; subst.
        apply oracle_repetition_stop.
        exact Hdecision.
      * destruct
          (oracle_parse_fuel fuel oracle rules
            (GoalExpression (descend path AtRepetitionBody) body)
            input)
          as [[middle body_result] |] eqn:Hbody;
          try discriminate Hparse.
        destruct body_result as [tree | body_trees]; try discriminate Hparse.
        destruct (list_eq_dec concrete_token_eq_dec input middle)
          as [Hequal | Hprogress]; try discriminate Hparse.
        destruct
          (oracle_parse_fuel fuel oracle rules
            (GoalRepetition path body) middle)
          as [[tail_rest tail_result] |] eqn:Htail;
          try discriminate Hparse.
        destruct tail_result as [tail_tree | trees]; try discriminate Hparse.
        inversion Hparse; subst.
        eapply oracle_repetition_step with (middle := middle).
        -- exact Hdecision.
        -- eapply IH.
           exact Hbody.
        -- exact Hprogress.
        -- eapply IH.
           exact Htail.
Qed.

Definition phase1_surface_predictive_parse_fuel
  (fuel : nat)
  (tokens : list ConcreteToken)
  : option (list ConcreteToken * DerivationResult) :=
  oracle_parse_fuel
    fuel
    phase1_surface_predictive_oracle
    phase1_surface_rules
    (GoalExpression [] (ENonterminal phase1_surface_start))
    tokens.

Theorem phase1_surface_predictive_parse_fuel_sound :
  forall fuel tokens tree,
    phase1_surface_predictive_parse_fuel fuel tokens =
      Some ([], ResultTree tree) ->
    OracleResolvedPhase1CompleteDerivation
      phase1_surface_predictive_oracle tokens tree.
Proof.
  intros fuel tokens tree Hparse.
  unfold phase1_surface_predictive_parse_fuel in Hparse.
  unfold OracleResolvedPhase1CompleteDerivation,
    OracleResolvedExpression.
  eapply oracle_parse_fuel_sound.
  exact Hparse.
Qed.

Corollary phase1_surface_predictive_parse_fuel_ordinary_sound :
  forall fuel tokens tree,
    phase1_surface_predictive_parse_fuel fuel tokens =
      Some ([], ResultTree tree) ->
    Phase1CompleteDerivation tokens tree.
Proof.
  intros fuel tokens tree Hparse.
  eapply oracle_resolved_phase1_erases.
  eapply phase1_surface_predictive_parse_fuel_sound.
  exact Hparse.
Qed.
