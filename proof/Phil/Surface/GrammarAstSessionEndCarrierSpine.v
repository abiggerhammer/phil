From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionMutualRecursiveClosureSpine
  GrammarAstSourceHeader.

Import ListNotations.
Open Scope string_scope.

(*
  Refine the terminal `end identifier` payload independently of the already-
  closed transfer/choice recursion.  This small carrier gives the terminal
  outcome a semantic string value while retaining exact parse-tree recovery.
*)

Record Phase1SurfaceEndSessionSpine : Type := {
  phase1_end_session_outcome : string
}.

Definition phase1_surface_end_session_spine_tree
  (session : Phase1SurfaceEndSessionSpine) : ParseTree :=
  PTSequence
    [ PTLiteral "end";
      phase1_surface_identifier_tree (phase1_end_session_outcome session)
    ].

Definition phase1_surface_normalize_end_session_spine
  (tree : ParseTree) : option Phase1SurfaceEndSessionSpine :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact2 items with
      | Some (keyword_tree, outcome_tree) =>
          match phase1_surface_expect_literal "end" keyword_tree,
                phase1_surface_normalize_identifier outcome_tree with
          | Some tt, Some outcome =>
              Some {| phase1_end_session_outcome := outcome |}
          | _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_end_session_spine_round_trip :
  forall tree session,
    phase1_surface_normalize_end_session_spine tree = Some session ->
    phase1_surface_end_session_spine_tree session = tree.
Proof.
  intros tree session Hnormalize.
  unfold phase1_surface_normalize_end_session_spine in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items)
    as [[keyword_tree outcome_tree] |] eqn:Hitems;
    try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "end" keyword_tree)
    as [[] |] eqn:Hkeyword; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_identifier outcome_tree)
    as [outcome |] eqn:Houtcome; try discriminate Hnormalize.
  inversion Hnormalize; subst session.
  unfold phase1_surface_end_session_spine_tree.
  rewrite (phase1_surface_expect_sequence_round_trip tree items Hsequence).
  rewrite (phase1_surface_exact2_round_trip
    items keyword_tree outcome_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip
    "end" keyword_tree Hkeyword).
  rewrite (phase1_surface_normalize_identifier_round_trip
    outcome_tree outcome Houtcome).
  reflexivity.
Qed.

Definition phase1_surface_end_session_expression_for_totality : EbnfExpression :=
  ESequence [ ELiteral "end"; ENonterminal "identifier" ].
