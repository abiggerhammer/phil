From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstTopLevelSpine.

Import ListNotations.
Open Scope string_scope.

(*
  First recursive session-expression correspondence layer for
  PHIL-SURFACE-GRAMMAR-CORR-001.

  This layer normalizes the closed outer session_expression choice and the
  closed seven-way nonreference_session_expression choice while deliberately
  retaining each selected payload subtree for its own successor refinement.
*)

Inductive Phase1SurfaceNonreferenceSessionTag : Type :=
| Phase1SendSession
| Phase1ReceiveSession
| Phase1SelectSession
| Phase1OfferSession
| Phase1EndSession
| Phase1RecursiveSession
| Phase1ContinueSession.

Definition phase1_surface_nonreference_session_tag_index
  (tag : Phase1SurfaceNonreferenceSessionTag) : nat :=
  match tag with
  | Phase1SendSession => 0
  | Phase1ReceiveSession => 1
  | Phase1SelectSession => 2
  | Phase1OfferSession => 3
  | Phase1EndSession => 4
  | Phase1RecursiveSession => 5
  | Phase1ContinueSession => 6
  end.

Definition phase1_surface_nonreference_session_tag_of_index
  (index : nat) : option Phase1SurfaceNonreferenceSessionTag :=
  match index with
  | 0 => Some Phase1SendSession
  | 1 => Some Phase1ReceiveSession
  | 2 => Some Phase1SelectSession
  | 3 => Some Phase1OfferSession
  | 4 => Some Phase1EndSession
  | 5 => Some Phase1RecursiveSession
  | 6 => Some Phase1ContinueSession
  | _ => None
  end.

Lemma phase1_surface_nonreference_session_tag_of_index_sound :
  forall index tag,
    phase1_surface_nonreference_session_tag_of_index index = Some tag ->
    index = phase1_surface_nonreference_session_tag_index tag.
Proof.
  intros index tag Htag.
  destruct index as [|index]; cbn in Htag.
  - inversion Htag; reflexivity.
  - destruct index as [|index]; cbn in Htag.
    + inversion Htag; reflexivity.
    + destruct index as [|index]; cbn in Htag.
      * inversion Htag; reflexivity.
      * destruct index as [|index]; cbn in Htag.
        -- inversion Htag; reflexivity.
        -- destruct index as [|index]; cbn in Htag.
           ++ inversion Htag; reflexivity.
           ++ destruct index as [|index]; cbn in Htag.
              ** inversion Htag; reflexivity.
              ** destruct index as [|index]; cbn in Htag.
                 --- inversion Htag; reflexivity.
                 --- discriminate Htag.
Qed.

Record Phase1SurfaceNonreferenceSessionSpine : Type := {
  phase1_nonreference_session_spine_tag : Phase1SurfaceNonreferenceSessionTag;
  phase1_nonreference_session_spine_selected_tree : ParseTree
}.

Definition phase1_surface_nonreference_session_spine_tree
  (session : Phase1SurfaceNonreferenceSessionSpine) : ParseTree :=
  PTNonterminal "nonreference_session_expression"
    (PTAlternative
      (phase1_surface_nonreference_session_tag_index
        (phase1_nonreference_session_spine_tag session))
      (phase1_nonreference_session_spine_selected_tree session)).

Definition phase1_surface_normalize_nonreference_session_spine
  (tree : ParseTree) : option Phase1SurfaceNonreferenceSessionSpine :=
  match phase1_surface_expect_nonterminal
          "nonreference_session_expression" tree with
  | Some body =>
      match phase1_surface_expect_alternative body with
      | Some (index, selected) =>
          match phase1_surface_nonreference_session_tag_of_index index with
          | Some tag =>
              Some
                {| phase1_nonreference_session_spine_tag := tag;
                   phase1_nonreference_session_spine_selected_tree := selected |}
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_nonreference_session_spine_round_trip :
  forall tree session,
    phase1_surface_normalize_nonreference_session_spine tree = Some session ->
    phase1_surface_nonreference_session_spine_tree session = tree.
Proof.
  intros tree session Hnormalize.
  unfold phase1_surface_normalize_nonreference_session_spine in Hnormalize.
  destruct
    (phase1_surface_expect_nonterminal "nonreference_session_expression" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_alternative body)
    as [[index selected] |] eqn:Halternative; try discriminate Hnormalize.
  destruct (phase1_surface_nonreference_session_tag_of_index index)
    as [tag |] eqn:Htag; try discriminate Hnormalize.
  inversion Hnormalize; subst session.
  unfold phase1_surface_nonreference_session_spine_tree.
  cbn.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    "nonreference_session_expression" tree body Hnode).
  rewrite (phase1_surface_expect_alternative_round_trip
    body index selected Halternative).
  rewrite <- (phase1_surface_nonreference_session_tag_of_index_sound
    index tag Htag).
  reflexivity.
Qed.

Inductive Phase1SurfaceSessionSpine : Type :=
| Phase1NonreferenceSessionSpine
    (session : Phase1SurfaceNonreferenceSessionSpine)
| Phase1StaticReferenceSessionSpine
    (reference_tree : ParseTree).

Definition phase1_surface_session_spine_tree
  (session : Phase1SurfaceSessionSpine) : ParseTree :=
  match session with
  | Phase1NonreferenceSessionSpine nonreference =>
      PTNonterminal "session_expression"
        (PTAlternative 0
          (phase1_surface_nonreference_session_spine_tree nonreference))
  | Phase1StaticReferenceSessionSpine reference_tree =>
      PTNonterminal "session_expression"
        (PTAlternative 1 reference_tree)
  end.

Definition phase1_surface_normalize_session_spine
  (tree : ParseTree) : option Phase1SurfaceSessionSpine :=
  match phase1_surface_expect_nonterminal "session_expression" tree with
  | Some body =>
      match phase1_surface_expect_alternative body with
      | Some (0, selected) =>
          match phase1_surface_normalize_nonreference_session_spine selected with
          | Some nonreference =>
              Some (Phase1NonreferenceSessionSpine nonreference)
          | None => None
          end
      | Some (1, selected) =>
          Some (Phase1StaticReferenceSessionSpine selected)
      | _ => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_session_spine_round_trip :
  forall tree session,
    phase1_surface_normalize_session_spine tree = Some session ->
    phase1_surface_session_spine_tree session = tree.
Proof.
  intros tree session Hnormalize.
  unfold phase1_surface_normalize_session_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "session_expression" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_alternative body)
    as [[index selected] |] eqn:Halternative; try discriminate Hnormalize.
  destruct index as [|index].
  - destruct (phase1_surface_normalize_nonreference_session_spine selected)
      as [nonreference |] eqn:Hnonreference; try discriminate Hnormalize.
    inversion Hnormalize; subst session.
    unfold phase1_surface_session_spine_tree.
    rewrite (phase1_surface_expect_nonterminal_round_trip
      "session_expression" tree body Hnode).
    rewrite (phase1_surface_expect_alternative_round_trip
      body 0 selected Halternative).
    rewrite (phase1_surface_normalize_nonreference_session_spine_round_trip
      selected nonreference Hnonreference).
    reflexivity.
  - destruct index as [|index].
    + inversion Hnormalize; subst session.
      unfold phase1_surface_session_spine_tree.
      rewrite (phase1_surface_expect_nonterminal_round_trip
        "session_expression" tree body Hnode).
      rewrite (phase1_surface_expect_alternative_round_trip
        body 1 selected Halternative).
      reflexivity.
    + discriminate Hnormalize.
Qed.
