From Stdlib Require Import Bool.Bool Lists.List Strings.String.

From Phil.Surface Require Import Grammar GrammarDerivation.

Import ListNotations.
Open Scope string_scope.

(*
  Second preparatory tranche for PHIL-SURFACE-DETERM-001.

  GrammarDerivation.v defines the implementation-independent nondeterministic
  derivation relation for the exact generated Grammar-v1 EBNF.  This file adds
  an explicit path- and input-indexed decision oracle.  The oracle resolves
  only genuine EBNF choice points: alternative branch, optional presence, and
  repetition continuation.  Sequence boundaries and nonterminal bodies remain
  consequences of the grammar and recursive derivation itself.

  The important theorem in this tranche is oracle_derivation_functional: once
  those choices are fixed, a derivation from one exact goal and input has one
  exact remainder and structural result.  The final determinacy tranche must
  still prove that the exact 15 reviewed Grammar-v1 overlap sites induce one
  admissible oracle for every complete ordinary EBNF derivation.
*)

Record DerivationOracle : Type := mkDerivationOracle {
  oracleAlternative : SyntaxPath -> list ConcreteToken -> option nat;
  oracleOptional : SyntaxPath -> list ConcreteToken -> bool;
  oracleRepetition : SyntaxPath -> list ConcreteToken -> bool
}.

Inductive OracleGoal : Type :=
| GoalExpression : SyntaxPath -> EbnfExpression -> OracleGoal
| GoalSequence : SyntaxPath -> nat -> list EbnfExpression -> OracleGoal
| GoalRepetition : SyntaxPath -> EbnfExpression -> OracleGoal.

Inductive OracleResult : Type :=
| ResultTree : ParseTree -> OracleResult
| ResultTrees : list ParseTree -> OracleResult.

Inductive OracleDerives
  (oracle : DerivationOracle)
  (rules : list GrammarRule)
  : OracleGoal ->
    list ConcreteToken -> list ConcreteToken -> OracleResult -> Prop :=
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
      oracleAlternative oracle path input = Some index ->
      nth_error items index = Some item ->
      OracleDerives oracle rules
        (GoalExpression (descend path (AtAlternative index)) item)
        input rest (ResultTree tree) ->
      OracleDerives oracle rules
        (GoalExpression path (EAlternative items))
        input rest (ResultTree (PTAlternative index tree))
| oracle_optional_none :
    forall path body input,
      oracleOptional oracle path input = false ->
      OracleDerives oracle rules
        (GoalExpression path (EOptional body))
        input input (ResultTree PTOptionalNone)
| oracle_optional_some :
    forall path body input rest tree,
      oracleOptional oracle path input = true ->
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
      oracleRepetition oracle path input = false ->
      OracleDerives oracle rules
        (GoalRepetition path body)
        input input (ResultTrees [])
| oracle_repetition_step :
    forall path body input middle rest tree trees,
      oracleRepetition oracle path input = true ->
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
  (goal : OracleGoal)
  (input rest : list ConcreteToken)
  (result : OracleResult) : Prop :=
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
      let Heq := fresh "Heq" in
      assert (Heq : left = right) by congruence;
      subst right
  end.

Ltac consume_functional_ih :=
  repeat match goal with
  | IH : forall nextRest nextResult,
      OracleDerives ?oracle ?rules ?goal ?input nextRest nextResult ->
      ?leftRest = nextRest /\ ?leftResult = nextResult,
    H : OracleDerives oracle rules goal input ?rightRest ?rightResult |- _ =>
      let Hfunctional := fresh "Hfunctional" in
      pose proof (IH rightRest rightResult H) as Hfunctional;
      clear H;
      destruct Hfunctional;
      subst
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
    split; congruence.
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
    oracle rules
    (GoalExpression path expression)
    input rest (ResultTree tree)
    Hresolved).
Qed.

Theorem oracle_resolved_expression_functional :
  forall oracle rules path expression input rest1 tree1 rest2 tree2,
    OracleResolvedExpression oracle rules path expression input rest1 tree1 ->
    OracleResolvedExpression oracle rules path expression input rest2 tree2 ->
    rest1 = rest2 /\ tree1 = tree2.
Proof.
  intros oracle rules path expression input rest1 tree1 rest2 tree2 Hleft Hright.
  destruct (oracle_derivation_functional
    oracle rules
    (GoalExpression path expression)
    input rest1 (ResultTree tree1)
    Hleft rest2 (ResultTree tree2) Hright) as [Hrest Hresult].
  split.
  - exact Hrest.
  - injection Hresult. intros Htree. exact Htree.
Qed.

Definition OracleResolvedPhase1Complete
  (oracle : DerivationOracle)
  (tokens : list ConcreteToken)
  (tree : ParseTree) : Prop :=
  OracleResolvedExpression
    oracle
    phase1_surface_rules
    []
    (ENonterminal phase1_surface_start)
    tokens [] tree.

Theorem oracle_resolved_phase1_complete_erases :
  forall oracle tokens tree,
    OracleResolvedPhase1Complete oracle tokens tree ->
    Phase1CompleteDerivation tokens tree.
Proof.
  intros oracle tokens tree Hresolved.
  exact (oracle_resolved_expression_erases
    oracle phase1_surface_rules []
    (ENonterminal phase1_surface_start)
    tokens [] tree Hresolved).
Qed.

Theorem oracle_resolved_phase1_complete_is_unique :
  forall oracle tokens leftTree rightTree,
    OracleResolvedPhase1Complete oracle tokens leftTree ->
    OracleResolvedPhase1Complete oracle tokens rightTree ->
    leftTree = rightTree.
Proof.
  intros oracle tokens leftTree rightTree Hleft Hright.
  destruct (oracle_resolved_expression_functional
    oracle phase1_surface_rules []
    (ENonterminal phase1_surface_start)
    tokens [] leftTree [] rightTree Hleft Hright) as [_ Htree].
  exact Htree.
Qed.
