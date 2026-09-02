From Stdlib Require Import Arith.PeanoNat Lists.List Strings.String.

From Phil.Surface Require Import Grammar.

Import ListNotations.
Open Scope string_scope.

(*
  Preparatory semantics for PHIL-SURFACE-DETERM-001.

  Grammar.v is generated deterministically from grammar/phase1-surface.ebnf.
  This file gives that typed EBNF an implementation-independent derivation
  relation.  It deliberately does not encode Haskell parser branch order.

  A derivation consumes a prefix of a concrete token stream and returns the
  unconsumed suffix plus a structural parse tree.  Repetition steps must make
  progress; the exact Phase 1 grammar audit separately checks that no repeated
  body is nullable.

  SyntaxPath records stable structural decision sites.  The successor proof
  tranche will use those paths to state a deterministic choice oracle, prove
  oracle-resolved derivations functional, and finally discharge the exact 15
  reviewed overlap sites without changing the normative EBNF.
*)

Inductive ConcreteToken : Type :=
| TLiteral : string -> ConcreteToken
| TLexical : string -> string -> ConcreteToken.

Inductive SyntaxPathStep : Type :=
| AtNonterminal : string -> SyntaxPathStep
| AtSequence : nat -> SyntaxPathStep
| AtAlternative : nat -> SyntaxPathStep
| AtOptionalBody : SyntaxPathStep
| AtRepetitionBody : SyntaxPathStep.

Definition SyntaxPath : Type := list SyntaxPathStep.

Definition descend (path : SyntaxPath) (step : SyntaxPathStep) : SyntaxPath :=
  List.app path [step].

Fixpoint lookupRule
  (name : string)
  (rules : list GrammarRule) : option EbnfExpression :=
  match rules with
  | [] => None
  | (candidate, body) :: rest =>
      if String.eqb name candidate
      then Some body
      else lookupRule name rest
  end.

Inductive ParseTree : Type :=
| PTLiteral : string -> ParseTree
| PTLexical : string -> string -> ParseTree
| PTNonterminal : string -> ParseTree -> ParseTree
| PTSequence : list ParseTree -> ParseTree
| PTAlternative : nat -> ParseTree -> ParseTree
| PTOptionalNone : ParseTree
| PTOptionalSome : ParseTree -> ParseTree
| PTRepetition : list ParseTree -> ParseTree.

Inductive Derives (rules : list GrammarRule)
  : SyntaxPath -> EbnfExpression ->
    list ConcreteToken -> list ConcreteToken -> ParseTree -> Prop :=
| derives_literal :
    forall path literal tail,
      Derives rules path (ELiteral literal)
        (TLiteral literal :: tail) tail
        (PTLiteral literal)
| derives_lexical :
    forall path class lexeme tail,
      Derives rules path (ELexicalClass class)
        (TLexical class lexeme :: tail) tail
        (PTLexical class lexeme)
| derives_nonterminal :
    forall path name body input rest tree,
      lookupRule name rules = Some body ->
      Derives rules (descend path (AtNonterminal name))
        body input rest tree ->
      Derives rules path (ENonterminal name)
        input rest (PTNonterminal name tree)
| derives_sequence :
    forall path items input rest trees,
      DerivesSequence rules path 0 items input rest trees ->
      Derives rules path (ESequence items)
        input rest (PTSequence trees)
| derives_alternative :
    forall path items index item input rest tree,
      nth_error items index = Some item ->
      Derives rules (descend path (AtAlternative index))
        item input rest tree ->
      Derives rules path (EAlternative items)
        input rest (PTAlternative index tree)
| derives_optional_none :
    forall path body input,
      Derives rules path (EOptional body)
        input input PTOptionalNone
| derives_optional_some :
    forall path body input rest tree,
      Derives rules (descend path AtOptionalBody)
        body input rest tree ->
      Derives rules path (EOptional body)
        input rest (PTOptionalSome tree)
| derives_repetition :
    forall path body input rest trees,
      DerivesRepetition rules path body input rest trees ->
      Derives rules path (ERepetition body)
        input rest (PTRepetition trees)

with DerivesSequence (rules : list GrammarRule)
  : SyntaxPath -> nat -> list EbnfExpression ->
    list ConcreteToken -> list ConcreteToken -> list ParseTree -> Prop :=
| derives_sequence_nil :
    forall path index input,
      DerivesSequence rules path index [] input input []
| derives_sequence_cons :
    forall path index item items input middle rest tree trees,
      Derives rules (descend path (AtSequence index))
        item input middle tree ->
      DerivesSequence rules path (S index)
        items middle rest trees ->
      DerivesSequence rules path index
        (item :: items) input rest (tree :: trees)

with DerivesRepetition (rules : list GrammarRule)
  : SyntaxPath -> EbnfExpression ->
    list ConcreteToken -> list ConcreteToken -> list ParseTree -> Prop :=
| derives_repetition_stop :
    forall path body input,
      DerivesRepetition rules path body input input []
| derives_repetition_step :
    forall path body input middle rest tree trees,
      Derives rules (descend path AtRepetitionBody)
        body input middle tree ->
      input <> middle ->
      DerivesRepetition rules path body middle rest trees ->
      DerivesRepetition rules path body input rest (tree :: trees).

Scheme Derives_ind' := Induction for Derives Sort Prop
with DerivesSequence_ind' := Induction for DerivesSequence Sort Prop
with DerivesRepetition_ind' := Induction for DerivesRepetition Sort Prop.

Combined Scheme Derivation_mutind
  from Derives_ind', DerivesSequence_ind', DerivesRepetition_ind'.

Definition CompleteDerivation
  (rules : list GrammarRule)
  (start : string)
  (tokens : list ConcreteToken)
  (tree : ParseTree) : Prop :=
  Derives rules [] (ENonterminal start) tokens [] tree.

Definition Phase1CompleteDerivation
  (tokens : list ConcreteToken)
  (tree : ParseTree) : Prop :=
  CompleteDerivation
    phase1_surface_rules
    phase1_surface_start
    tokens tree.

Theorem literal_derivation_is_exact :
  forall rules path literal input rest tree,
    Derives rules path (ELiteral literal) input rest tree ->
    exists tail,
      input = TLiteral literal :: tail /\
      rest = tail /\
      tree = PTLiteral literal.
Proof.
  intros rules path literal input rest tree Hderive.
  inversion Hderive; subst.
  eexists.
  repeat split; reflexivity.
Qed.

Theorem lexical_derivation_is_exact :
  forall rules path class input rest tree,
    Derives rules path (ELexicalClass class) input rest tree ->
    exists lexeme tail,
      input = TLexical class lexeme :: tail /\
      rest = tail /\
      tree = PTLexical class lexeme.
Proof.
  intros rules path class input rest tree Hderive.
  inversion Hderive; subst.
  eexists.
  eexists.
  repeat split; reflexivity.
Qed.

Theorem alternative_derivation_names_exact_branch :
  forall rules path items input rest tree,
    Derives rules path (EAlternative items) input rest tree ->
    exists index item branchTree,
      nth_error items index = Some item /\
      tree = PTAlternative index branchTree /\
      Derives rules (descend path (AtAlternative index))
        item input rest branchTree.
Proof.
  intros rules path items input rest tree Hderive.
  inversion Hderive; subst.
  do 3 eexists.
  repeat split; eauto.
Qed.

Theorem optional_derivation_exposes_presence :
  forall rules path body input rest tree,
    Derives rules path (EOptional body) input rest tree ->
    (rest = input /\ tree = PTOptionalNone) \/
    (exists bodyTree,
      tree = PTOptionalSome bodyTree /\
      Derives rules (descend path AtOptionalBody)
        body input rest bodyTree).
Proof.
  intros rules path body input rest tree Hderive.
  inversion Hderive; subst.
  - left. split; reflexivity.
  - right. eexists. split; eauto.
Qed.

Theorem repetition_step_makes_progress :
  forall rules path body input middle rest tree trees,
    Derives rules (descend path AtRepetitionBody)
      body input middle tree ->
    input <> middle ->
    DerivesRepetition rules path body middle rest trees ->
    input <> middle.
Proof.
  intros.
  assumption.
Qed.

Theorem phase1_complete_derivation_consumes_entire_token_stream :
  forall tokens tree,
    Phase1CompleteDerivation tokens tree ->
    Derives phase1_surface_rules []
      (ENonterminal phase1_surface_start)
      tokens [] tree.
Proof.
  intros tokens tree Hcomplete.
  exact Hcomplete.
Qed.