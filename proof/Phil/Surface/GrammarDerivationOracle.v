From Stdlib Require Import Arith.PeanoNat Lists.List Strings.String.

From Phil.Surface Require Import Grammar GrammarDerivation.

Import ListNotations.
Open Scope string_scope.

(*
  Reusable oracle-resolved determinism layer for PHIL-SURFACE-DETERM-001.

  #552 established a nondeterministic, implementation-independent derivation
  relation for the exact typed EBNF generated from grammar/phase1-surface.ebnf.
  This file adds only a path- and input-indexed decision oracle for EBNF choice
  points.  It does not encode Haskell parser order.

  The final determinacy tranche must construct one admissible oracle from the
  exact Grammar-v1 structure plus the complete 15-site overlap certificate and
  prove that every ordinary complete derivation is resolved by that oracle.
*)

Inductive OracleDecision : Type :=
| ChooseAlternative : nat -> OracleDecision
| ChooseOptionalAbsent : OracleDecision
| ChooseOptionalPresent : OracleDecision
| ChooseRepetitionStop : OracleDecision
| ChooseRepetitionContinue : OracleDecision.

Definition DerivationOracle : Type :=
  SyntaxPath -> list ConcreteToken -> option OracleDecision.

Inductive DerivationGoal : Type :=
| GoalExpression : SyntaxPath -> EbnfExpression -> DerivationGoal
| GoalSequence : SyntaxPath -> nat -> list EbnfExpression -> DerivationGoal
| GoalRepetition : SyntaxPath -> EbnfExpression -> DerivationGoal.

Inductive DerivationResult : Type :=
| ResultTree : ParseTree -> DerivationResult
| ResultTrees : list ParseTree -> DerivationResult.

Inductive OracleDerives
  (oracle : DerivationOracle)
  (rules : list GrammarRule)
  : DerivationGoal ->
    list ConcreteToken -> list ConcreteToken -> DerivationResult -> Prop :=
| oracle_literal :
    forall path literal tail,
      OracleDerives oracle rules
        (GoalExpression path (ELiteral literal))
        (TLiteral literal :: tail) tail
        (ResultTree (PTLiteral literal))
| oracle_lexical :
    forall path class lexeme tail,
      OracleDerives oracle rules
        (GoalExpression path (ELexicalClass class))
        (TLexical class lexeme :: tail) tail
        (ResultTree (PTLexical class lexeme))
| oracle_nonterminal :
    forall path name body input rest tree,
      lookupRule name rules = Some body ->
      OracleDerives oracle rules
        (GoalExpression (descend path (AtNonterminal name)) body)
        input rest (ResultTree tree) ->
      OracleDerives oracle rules
        (GoalExpression path (ENonterminal name))
        input rest (ResultTree (PTNonterminal name tree))
| oracle_sequence :
    forall path items input rest trees,
      OracleDerives oracle rules
        (GoalSequence path 0 items)
        input rest (ResultTrees trees) ->
      OracleDerives oracle rules
        (GoalExpression path (ESequence items))
        input rest (ResultTree (PTSequence trees))
| oracle_alternative :
    forall path items index item input rest tree,
      oracle path input = Some (ChooseAlternative index) ->
      nth_error items index = Some item ->
      OracleDerives oracle rules
        (GoalExpression (descend path (AtAlternative index)) item)
        input rest (ResultTree tree) ->
      OracleDerives oracle rules
        (GoalExpression path (EAlternative items))
        input rest (ResultTree (PTAlternative index tree))
| oracle_optional_none :
    forall path body input,
      oracle path input = Some ChooseOptionalAbsent ->
      OracleDerives oracle rules
        (GoalExpression path (EOptional body))
        input input (ResultTree PTOptionalNone)
| oracle_optional_some :
    forall path body input rest tree,
      oracle path input = Some ChooseOptionalPresent ->
      OracleDerives oracle rules
        (GoalExpression (descend path AtOptionalBody) body)
        input rest (ResultTree tree) ->
      OracleDerives oracle rules
        (GoalExpression path (EOptional body))
        input rest (ResultTree (PTOptionalSome tree))
| oracle_repetition :
    forall path body input rest trees,
      OracleDerives oracle rules
        (GoalRepetition path body)
        input rest (ResultTrees trees) ->
      OracleDerives oracle rules
        (GoalExpression path (ERepetition body))
        input rest (ResultTree (PTRepetition trees))
| oracle_sequence_nil :
    forall path index input,
      OracleDerives oracle rules
        (GoalSequence path index [])
        input input (ResultTrees [])
| oracle_sequence_cons :
    forall path index item items input middle rest tree trees,
      OracleDerives oracle rules
        (GoalExpression (descend path (AtSequence index)) item)
        input middle (ResultTree tree) ->
      OracleDerives oracle rules
        (GoalSequence path (S index) items)
        middle rest (ResultTrees trees) ->
      OracleDerives oracle rules
        (GoalSequence path index (item :: items))
        input rest (ResultTrees (tree :: trees))
| oracle_repetition_stop :
    forall path body input,
      oracle path input = Some ChooseRepetitionStop ->
      OracleDerives oracle rules
        (GoalRepetition path body)
        input input (ResultTrees [])
| oracle_repetition_step :
    forall path body input middle rest tree trees,
      oracle path input = Some ChooseRepetitionContinue ->
      OracleDerives oracle rules
        (GoalExpression (descend path AtRepetitionBody) body)
        input middle (ResultTree tree) ->
      input <> middle ->
      OracleDerives oracle rules
        (GoalRepetition path body)
        middle rest (ResultTrees trees) ->
      OracleDerives oracle rules
        (GoalRepetition path body)
        input rest (ResultTrees (tree :: trees)).

Definition OracleErases
  (rules : list GrammarRule)
  (goal : DerivationGoal)
  (input rest : list ConcreteToken)
  (result : DerivationResult) : Prop :=
  match goal, result with
  | GoalExpression path expression, ResultTree tree =>
      Derives rules path expression input rest tree
  | GoalSequence path index items, ResultTrees trees =>
      DerivesSequence rules path index items input rest trees
  | GoalRepetition path body, ResultTrees trees =>
      DerivesRepetition rules path body input rest trees
  | _, _ => False
  end.

Theorem oracle_derivation_erases :
  forall oracle rules goal input rest result,
    OracleDerives oracle rules goal input rest result ->
    OracleErases rules goal input rest result.
Proof.
  intros oracle rules goal input rest result Hderive.
  induction Hderive; simpl in *; econstructor; eauto.
Qed.

Ltac synchronize_some_results :=
  repeat match goal with
  | Hleft : ?f = Some ?left,
    Hright : ?f = Some ?right |- _ =>
      first
        [ constr_eq left right; fail 1
        | let Heq := fresh "Heq" in
          assert (Heq : left = right) by congruence;
          clear Hleft Hright;
          first [ discriminate Heq | inversion Heq; subst; clear Heq ] ]
  end.

Ltac consume_functional_ih :=
  repeat match goal with
  | IH : forall nextRest nextResult,
      OracleDerives ?oracle ?rules ?goal ?input nextRest nextResult ->
      ?leftRest = nextRest /\ ?leftResult = nextResult,
    H : OracleDerives ?oracle ?rules ?goal ?input ?rightRest ?rightResult |- _ =>
      let Hfunctional := fresh "Hfunctional" in
      let Hrest := fresh "Hrest" in
      let Hresult := fresh "Hresult" in
      pose proof (IH rightRest rightResult H) as Hfunctional;
      clear H;
      destruct Hfunctional as [Hrest Hresult];
      subst rightRest;
      inversion Hresult; subst; clear Hresult
  end.

Theorem oracle_derivation_functional :
  forall oracle rules goal input rest1 result1,
    OracleDerives oracle rules goal input rest1 result1 ->
    forall rest2 result2,
      OracleDerives oracle rules goal input rest2 result2 ->
      rest1 = rest2 /\ result1 = result2.
Proof.
  intros oracle rules goal input rest1 result1 Hleft.
  induction Hleft; intros rest2 result2 Hright;
    inversion Hright; subst;
    synchronize_some_results;
    try congruence;
    consume_functional_ih;
    split; reflexivity.
Qed.

Definition OracleResolvedExpression
  (oracle : DerivationOracle)
  (rules : list GrammarRule)
  (path : SyntaxPath)
  (expression : EbnfExpression)
  (input rest : list ConcreteToken)
  (tree : ParseTree) : Prop :=
  OracleDerives oracle rules
    (GoalExpression path expression)
    input rest (ResultTree tree).

Theorem oracle_resolved_expression_erases :
  forall oracle rules path expression input rest tree,
    OracleResolvedExpression oracle rules path expression input rest tree ->
    Derives rules path expression input rest tree.
Proof.
  intros oracle rules path expression input rest tree Hresolved.
  exact (oracle_derivation_erases
    oracle rules (GoalExpression path expression)
    input rest (ResultTree tree) Hresolved).
Qed.

Definition OracleResolvedPhase1CompleteDerivation
  (oracle : DerivationOracle)
  (tokens : list ConcreteToken)
  (tree : ParseTree) : Prop :=
  OracleResolvedExpression oracle
    phase1_surface_rules
    []
    (ENonterminal phase1_surface_start)
    tokens [] tree.

Theorem oracle_resolved_phase1_erases :
  forall oracle tokens tree,
    OracleResolvedPhase1CompleteDerivation oracle tokens tree ->
    Phase1CompleteDerivation tokens tree.
Proof.
  intros oracle tokens tree Hresolved.
  exact (oracle_resolved_expression_erases
    oracle phase1_surface_rules []
    (ENonterminal phase1_surface_start)
    tokens [] tree Hresolved).
Qed.

Theorem same_oracle_has_one_complete_parse :
  forall oracle tokens firstTree secondTree,
    OracleResolvedPhase1CompleteDerivation oracle tokens firstTree ->
    OracleResolvedPhase1CompleteDerivation oracle tokens secondTree ->
    firstTree = secondTree.
Proof.
  intros oracle tokens firstTree secondTree Hfirst Hsecond.
  unfold OracleResolvedPhase1CompleteDerivation in *.
  pose proof (oracle_derivation_functional
    oracle
    phase1_surface_rules
    (GoalExpression [] (ENonterminal phase1_surface_start))
    tokens [] (ResultTree firstTree)
    Hfirst
    [] (ResultTree secondTree)
    Hsecond) as Hfunctional.
  destruct Hfunctional as [_ Htrees].
  injection Htrees.
  trivial.
Qed.
