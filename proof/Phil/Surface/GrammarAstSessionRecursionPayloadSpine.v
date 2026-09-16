From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionEndRecursiveCarrierSpine
  GrammarAstSourceHeader.

Import ListNotations.
Open Scope string_scope.

(*
  Refine the two remaining nonreference-session payload shells without yet
  making a semantic claim about recursion-variable scope.

    recursive identifier = session_expression
    continue identifier

  The recursive body remains at the already-certified full session-expression
  parse-tree boundary.  A successor can replace that exact body with the
  end-refined recursive carrier and then close transitive recursive binders.
*)

Record Phase1SurfaceRecursiveSessionPayloadSpine : Type := {
  phase1_recursive_session_name : string;
  phase1_recursive_session_body_tree : ParseTree
}.

Record Phase1SurfaceContinueSessionPayloadSpine : Type := {
  phase1_continue_session_name : string
}.

Definition phase1_surface_recursive_session_payload_spine_tree
  (session : Phase1SurfaceRecursiveSessionPayloadSpine) : ParseTree :=
  PTSequence
    [ PTLiteral "recursive";
      phase1_surface_identifier_tree (phase1_recursive_session_name session);
      PTLiteral "=";
      phase1_recursive_session_body_tree session
    ].

Definition phase1_surface_continue_session_payload_spine_tree
  (session : Phase1SurfaceContinueSessionPayloadSpine) : ParseTree :=
  PTSequence
    [ PTLiteral "continue";
      phase1_surface_identifier_tree (phase1_continue_session_name session)
    ].

Definition phase1_surface_normalize_recursive_session_payload_spine
  (tree : ParseTree) : option Phase1SurfaceRecursiveSessionPayloadSpine :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact4 items with
      | Some (keyword_tree, name_tree, equals_tree, body_tree) =>
          match phase1_surface_expect_literal "recursive" keyword_tree,
                phase1_surface_normalize_identifier name_tree,
                phase1_surface_expect_literal "=" equals_tree,
                phase1_surface_expect_nonterminal "session_expression" body_tree
          with
          | Some tt, Some name, Some tt, Some _ =>
              Some
                {| phase1_recursive_session_name := name;
                   phase1_recursive_session_body_tree := body_tree |}
          | _, _, _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Definition phase1_surface_normalize_continue_session_payload_spine
  (tree : ParseTree) : option Phase1SurfaceContinueSessionPayloadSpine :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact2 items with
      | Some (keyword_tree, name_tree) =>
          match phase1_surface_expect_literal "continue" keyword_tree,
                phase1_surface_normalize_identifier name_tree
          with
          | Some tt, Some name =>
              Some {| phase1_continue_session_name := name |}
          | _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_recursive_session_payload_spine_round_trip :
  forall tree session,
    phase1_surface_normalize_recursive_session_payload_spine tree =
      Some session ->
    phase1_surface_recursive_session_payload_spine_tree session = tree.
Proof.
  intros tree session Hnormalize.
  unfold phase1_surface_normalize_recursive_session_payload_spine in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact4 items)
    as [[[[keyword_tree name_tree] equals_tree] body_tree] |]
    eqn:Hitems; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "recursive" keyword_tree)
    as [[] |] eqn:Hkeyword; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_identifier name_tree)
    as [name |] eqn:Hname; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "=" equals_tree)
    as [[] |] eqn:Hequals; try discriminate Hnormalize.
  destruct (phase1_surface_expect_nonterminal "session_expression" body_tree)
    as [body |] eqn:Hbody; try discriminate Hnormalize.
  inversion Hnormalize; subst session.
  unfold phase1_surface_recursive_session_payload_spine_tree.
  rewrite (phase1_surface_expect_sequence_round_trip tree items Hsequence).
  rewrite (phase1_surface_exact4_round_trip
    items keyword_tree name_tree equals_tree body_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip
    "recursive" keyword_tree Hkeyword).
  rewrite (phase1_surface_normalize_identifier_round_trip
    name_tree name Hname).
  rewrite (phase1_surface_expect_literal_round_trip
    "=" equals_tree Hequals).
  reflexivity.
Qed.

Theorem phase1_surface_normalize_continue_session_payload_spine_round_trip :
  forall tree session,
    phase1_surface_normalize_continue_session_payload_spine tree =
      Some session ->
    phase1_surface_continue_session_payload_spine_tree session = tree.
Proof.
  intros tree session Hnormalize.
  unfold phase1_surface_normalize_continue_session_payload_spine in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items)
    as [[keyword_tree name_tree] |] eqn:Hitems;
    try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "continue" keyword_tree)
    as [[] |] eqn:Hkeyword; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_identifier name_tree)
    as [name |] eqn:Hname; try discriminate Hnormalize.
  inversion Hnormalize; subst session.
  unfold phase1_surface_continue_session_payload_spine_tree.
  rewrite (phase1_surface_expect_sequence_round_trip tree items Hsequence).
  rewrite (phase1_surface_exact2_round_trip
    items keyword_tree name_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip
    "continue" keyword_tree Hkeyword).
  rewrite (phase1_surface_normalize_identifier_round_trip
    name_tree name Hname).
  reflexivity.
Qed.

Definition phase1_surface_recursive_session_expression_for_totality
  : EbnfExpression :=
  ESequence
    [ ELiteral "recursive";
      ENonterminal "identifier";
      ELiteral "=";
      ENonterminal "session_expression"
    ].

Definition phase1_surface_continue_session_expression_for_totality
  : EbnfExpression :=
  ESequence
    [ ELiteral "continue";
      ENonterminal "identifier"
    ].
