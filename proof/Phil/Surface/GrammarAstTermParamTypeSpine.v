From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSourceHeader
  GrammarAstStaticTypeArgumentCarrierSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Reusable term-parameter correspondence for PHIL-SURFACE-GRAMMAR-CORR-001.

  term_param is a closed three-item shell.  Rather than retaining its nested
  type_expression as an opaque certified tree, this carrier reuses the most
  refined type-expression correspondence currently available, including
  named static references and type-valued static arguments.
*)

Record Phase1SurfaceTermParamTypeSpine : Type := {
  phase1_term_param_type_spine_name : string;
  phase1_term_param_type_spine_type : Phase1SurfaceStaticTypeArgumentsTypeSpine
}.

Definition phase1_surface_term_param_type_spine_tree
  (parameter : Phase1SurfaceTermParamTypeSpine) : ParseTree :=
  PTNonterminal "term_param"
    (PTSequence
      [ phase1_surface_identifier_tree
          (phase1_term_param_type_spine_name parameter);
        PTLiteral ":";
        phase1_surface_static_type_arguments_type_spine_tree
          (phase1_term_param_type_spine_type parameter)
      ]).

Definition phase1_surface_normalize_term_param_type_spine
  (tree : ParseTree) : option Phase1SurfaceTermParamTypeSpine :=
  match phase1_surface_expect_nonterminal "term_param" tree with
  | Some body =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact3 items with
          | Some (name_tree, colon_tree, type_tree) =>
              match phase1_surface_normalize_identifier name_tree,
                    phase1_surface_expect_literal ":" colon_tree,
                    phase1_surface_normalize_static_type_arguments_type_tree
                      type_tree
              with
              | Some name, Some tt, Some type_value =>
                  Some
                    {| phase1_term_param_type_spine_name := name;
                       phase1_term_param_type_spine_type := type_value |}
              | _, _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_term_param_type_spine_round_trip :
  forall tree parameter,
    phase1_surface_normalize_term_param_type_spine tree = Some parameter ->
    phase1_surface_term_param_type_spine_tree parameter = tree.
Proof.
  intros tree parameter Hnormalize.
  unfold phase1_surface_normalize_term_param_type_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "term_param" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_sequence body)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact3 items)
    as [[[name_tree colon_tree] type_tree] |] eqn:Hitems;
    try discriminate Hnormalize.
  destruct (phase1_surface_normalize_identifier name_tree)
    as [name |] eqn:Hname; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal ":" colon_tree)
    as [[] |] eqn:Hcolon; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_static_type_arguments_type_tree type_tree)
    as [type_value |] eqn:Htype; try discriminate Hnormalize.
  inversion Hnormalize; subst parameter.
  unfold phase1_surface_term_param_type_spine_tree.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    "term_param" tree body Hnode).
  rewrite (phase1_surface_expect_sequence_round_trip body items Hsequence).
  rewrite (phase1_surface_exact3_round_trip
    items name_tree colon_tree type_tree Hitems).
  rewrite (phase1_surface_normalize_identifier_round_trip
    name_tree name Hname).
  rewrite (phase1_surface_expect_literal_round_trip ":" colon_tree Hcolon).
  rewrite
    (phase1_surface_normalize_static_type_arguments_type_tree_round_trip
      type_tree type_value Htype).
  reflexivity.
Qed.
