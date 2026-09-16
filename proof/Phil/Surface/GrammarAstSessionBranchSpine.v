From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionChoiceSpine
  GrammarAstRefinementTupleTypePayloadSpine.

Import ListNotations.
Open Scope string_scope.

(*
  First individual session_branch payload layer for
  PHIL-SURFACE-GRAMMAR-CORR-001.

  The select/offer branch-list shell is now closed in both directions.  This
  slice opens each named session_branch just far enough to expose its fixed
  six-field grammar shell:

      identifier, [ branch_params ], [ using static_reference ],
      [ when proposition ], "=>", session_expression

  Every semantic child remains the exact certified ParseTree for dedicated
  successor refinement.
*)

Record Phase1SurfaceSessionBranchSpine : Type := {
  phase1_session_branch_label_tree : ParseTree;
  phase1_session_branch_params_tree : ParseTree;
  phase1_session_branch_boundary_tree : ParseTree;
  phase1_session_branch_guard_tree : ParseTree;
  phase1_session_branch_continuation_tree : ParseTree
}.

Definition phase1_surface_session_branch_spine_tree
  (branch : Phase1SurfaceSessionBranchSpine) : ParseTree :=
  PTNonterminal "session_branch"
    (PTSequence
      [ phase1_session_branch_label_tree branch;
        phase1_session_branch_params_tree branch;
        phase1_session_branch_boundary_tree branch;
        phase1_session_branch_guard_tree branch;
        PTLiteral "=>";
        phase1_session_branch_continuation_tree branch
      ]).

Definition phase1_surface_normalize_session_branch_spine
  (tree : ParseTree) : option Phase1SurfaceSessionBranchSpine :=
  match phase1_surface_expect_nonterminal "session_branch" tree with
  | Some body =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact6 items with
          | Some
              (label_tree, params_tree, boundary_tree, guard_tree,
               arrow_tree, continuation_tree) =>
              match
                phase1_surface_validate_named_node "identifier" label_tree,
                phase1_surface_expect_optional params_tree,
                phase1_surface_expect_optional boundary_tree,
                phase1_surface_expect_optional guard_tree,
                phase1_surface_expect_literal "=>" arrow_tree,
                phase1_surface_validate_named_node
                  "session_expression" continuation_tree
              with
              | Some tt, Some _, Some _, Some _, Some tt, Some tt =>
                  Some
                    {| phase1_session_branch_label_tree := label_tree;
                       phase1_session_branch_params_tree := params_tree;
                       phase1_session_branch_boundary_tree := boundary_tree;
                       phase1_session_branch_guard_tree := guard_tree;
                       phase1_session_branch_continuation_tree :=
                         continuation_tree |}
              | _, _, _, _, _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_session_branch_spine_round_trip :
  forall tree branch,
    phase1_surface_normalize_session_branch_spine tree = Some branch ->
    phase1_surface_session_branch_spine_tree branch = tree.
Proof.
  intros tree branch Hnormalize.
  unfold phase1_surface_normalize_session_branch_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "session_branch" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_sequence body)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact6 items)
    as [[[[[[label_tree params_tree] boundary_tree] guard_tree]
           arrow_tree] continuation_tree] |]
      eqn:Hitems; try discriminate Hnormalize.
  destruct (phase1_surface_validate_named_node "identifier" label_tree)
    as [[] |] eqn:Hlabel; try discriminate Hnormalize.
  destruct (phase1_surface_expect_optional params_tree)
    as [params |] eqn:Hparams; try discriminate Hnormalize.
  destruct (phase1_surface_expect_optional boundary_tree)
    as [boundary |] eqn:Hboundary; try discriminate Hnormalize.
  destruct (phase1_surface_expect_optional guard_tree)
    as [guard |] eqn:Hguard; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "=>" arrow_tree)
    as [[] |] eqn:Harrow; try discriminate Hnormalize.
  destruct
    (phase1_surface_validate_named_node
      "session_expression" continuation_tree)
    as [[] |] eqn:Hcontinuation; try discriminate Hnormalize.
  inversion Hnormalize; subst branch.
  unfold phase1_surface_session_branch_spine_tree.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    "session_branch" tree body Hnode).
  rewrite (phase1_surface_expect_sequence_round_trip body items Hsequence).
  rewrite (phase1_surface_exact6_round_trip
    items label_tree params_tree boundary_tree guard_tree arrow_tree
    continuation_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip "=>" arrow_tree Harrow).
  reflexivity.
Qed.
