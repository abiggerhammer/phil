From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Export GrammarDerivation.
From Phil.Surface Require Import
  GrammarAstExpressionOuterSpine
  GrammarAstExpressionOuterTotality
  GrammarAstParenthesizedExpressionSpine
  GrammarAstParenthesizedExpressionSpineTotality
  GrammarAstTupleExpressionSpine
  GrammarAstTupleExpressionSpineTotality.

Import ListNotations.
Open Scope string_scope.

(* PHIL-SURFACE-GRAMMAR-CORR-001: derive the recursive grouping normalizer's
   structural preconditions from the canonical grammar. This predicate does
   not assume successful recursive normalization. Every ordinary tree child
   is checked, including children of the explicitly retained boundaries. *)

Definition phase1_surface_grouping_shallow_valid
  (name : string) (tree : ParseTree) : Prop :=
  if String.eqb name "expression" then
    exists expression,
      phase1_surface_normalize_expression_outer_spine tree = Some expression
  else if String.eqb name "parenthesized_expression" then
    exists grouped,
      phase1_surface_normalize_parenthesized_expression_spine tree = Some grouped
  else if String.eqb name "tuple_expression" then
    exists tuple,
      phase1_surface_normalize_tuple_expression_spine tree = Some tuple
  else True.

(* The proof below uses grammar derivation induction; it does not need the
   automatically generated elimination scheme for this nested predicate. *)
Unset Elimination Schemes.
Inductive Phase1SurfaceGroupingWellFormed : ParseTree -> Prop :=
| grouping_wf_literal : forall literal,
    Phase1SurfaceGroupingWellFormed (PTLiteral literal)
| grouping_wf_lexical : forall class lexeme,
    Phase1SurfaceGroupingWellFormed (PTLexical class lexeme)
| grouping_wf_nonterminal : forall name body,
    Phase1SurfaceGroupingWellFormed body ->
    phase1_surface_grouping_shallow_valid name (PTNonterminal name body) ->
    Phase1SurfaceGroupingWellFormed (PTNonterminal name body)
| grouping_wf_sequence : forall items,
    Forall Phase1SurfaceGroupingWellFormed items ->
    Phase1SurfaceGroupingWellFormed (PTSequence items)
| grouping_wf_alternative : forall index body,
    Phase1SurfaceGroupingWellFormed body ->
    Phase1SurfaceGroupingWellFormed (PTAlternative index body)
| grouping_wf_optional_none :
    Phase1SurfaceGroupingWellFormed PTOptionalNone
| grouping_wf_optional_some : forall body,
    Phase1SurfaceGroupingWellFormed body ->
    Phase1SurfaceGroupingWellFormed (PTOptionalSome body)
| grouping_wf_repetition : forall items,
    Forall Phase1SurfaceGroupingWellFormed items ->
    Phase1SurfaceGroupingWellFormed (PTRepetition items).
Set Elimination Schemes.

Lemma phase1_surface_grouping_shallow_valid_from_derivation :
  forall name path input rest tree,
    Derives phase1_surface_rules path (ENonterminal name) input rest tree ->
    phase1_surface_grouping_shallow_valid name tree.
Proof.
  intros name path input rest tree Hderive.
  unfold phase1_surface_grouping_shallow_valid.
  destruct (String.eqb name "expression") eqn:Hexpression.
  - apply String.eqb_eq in Hexpression. subst name.
    destruct
      (phase1_surface_normalize_expression_outer_spine_total_from_derivation
        path input rest tree Hderive) as [value [Hvalue _]].
    exists value. exact Hvalue.
  - destruct (String.eqb name "parenthesized_expression") eqn:Hparenthesized.
    + apply String.eqb_eq in Hparenthesized. subst name.
      destruct
        (phase1_surface_normalize_parenthesized_expression_spine_total_from_derivation
          path input rest tree Hderive) as [value [Hvalue _]].
      exists value. exact Hvalue.
    + destruct (String.eqb name "tuple_expression") eqn:Htuple.
      * apply String.eqb_eq in Htuple. subst name.
        destruct
          (phase1_surface_normalize_tuple_expression_spine_total_from_derivation
            path input rest tree Hderive) as [value [Hvalue _]].
        exists value. exact Hvalue.
      * exact I.
Qed.

Theorem phase1_surface_grouping_well_formed_from_derivation_mutual :
  (forall path expression input rest tree,
    Derives phase1_surface_rules path expression input rest tree ->
    Phase1SurfaceGroupingWellFormed tree) /\
  (forall path index expressions input rest trees,
    DerivesSequence phase1_surface_rules path index expressions input rest trees ->
    Forall Phase1SurfaceGroupingWellFormed trees) /\
  (forall path expression input rest trees,
    DerivesRepetition phase1_surface_rules path expression input rest trees ->
    Forall Phase1SurfaceGroupingWellFormed trees).
Proof.
  apply Derivation_mutind.
  - intros. constructor.
  - intros. constructor.
  - intros path name body input rest tree Hlookup Hderive IH.
    constructor.
    + exact IH.
    + eapply phase1_surface_grouping_shallow_valid_from_derivation.
      econstructor; eassumption.
  - intros. constructor. assumption.
  - intros. constructor. assumption.
  - intros. constructor.
  - intros. constructor. assumption.
  - intros. constructor. assumption.
  - intros. constructor.
  - intros. constructor; assumption.
  - intros. constructor.
  - intros. constructor; assumption.
Qed.

Theorem phase1_surface_grouping_well_formed_from_derivation :
  forall path expression input rest tree,
    Derives phase1_surface_rules path expression input rest tree ->
    Phase1SurfaceGroupingWellFormed tree.
Proof.
  exact (proj1 phase1_surface_grouping_well_formed_from_derivation_mutual).
Qed.

Theorem phase1_surface_grouping_well_formed_from_derivation_sequence :
  forall path index expressions input rest trees,
    DerivesSequence phase1_surface_rules path index expressions input rest trees ->
    Forall Phase1SurfaceGroupingWellFormed trees.
Proof.
  exact (proj1 (proj2
    phase1_surface_grouping_well_formed_from_derivation_mutual)).
Qed.

Theorem phase1_surface_grouping_well_formed_from_derivation_repetition :
  forall path expression input rest trees,
    DerivesRepetition phase1_surface_rules path expression input rest trees ->
    Forall Phase1SurfaceGroupingWellFormed trees.
Proof.
  exact (proj2 (proj2
    phase1_surface_grouping_well_formed_from_derivation_mutual)).
Qed.
