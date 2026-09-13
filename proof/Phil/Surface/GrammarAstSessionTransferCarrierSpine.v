From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionTransferPayloadSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Lift the send/receive-refined nonreference session carrier through the
  enclosing two-way session_expression choice.  The static-reference branch
  remains exact for its own recursive correspondence layer.
*)

Inductive Phase1SurfaceTransferRefinedSessionSpine : Type :=
| Phase1TransferRefinedNonreferenceSession
    (session : Phase1SurfaceTransferRefinedNonreferenceSessionSpine)
| Phase1TransferRefinedStaticReferenceSession
    (reference_tree : ParseTree).

Definition phase1_surface_transfer_refined_session_spine_tree
  (session : Phase1SurfaceTransferRefinedSessionSpine) : ParseTree :=
  match session with
  | Phase1TransferRefinedNonreferenceSession nonreference =>
      PTNonterminal "session_expression"
        (PTAlternative 0
          (phase1_surface_transfer_refined_nonreference_session_spine_tree
            nonreference))
  | Phase1TransferRefinedStaticReferenceSession reference_tree =>
      PTNonterminal "session_expression"
        (PTAlternative 1 reference_tree)
  end.

Definition phase1_surface_normalize_transfer_refined_session_spine
  (session : Phase1SurfaceSessionSpine)
  : option Phase1SurfaceTransferRefinedSessionSpine :=
  match session with
  | Phase1NonreferenceSessionSpine nonreference =>
      match
        phase1_surface_normalize_transfer_refined_nonreference_session_spine
          nonreference
      with
      | Some refined =>
          Some (Phase1TransferRefinedNonreferenceSession refined)
      | None => None
      end
  | Phase1StaticReferenceSessionSpine reference_tree =>
      Some (Phase1TransferRefinedStaticReferenceSession reference_tree)
  end.

Theorem phase1_surface_normalize_transfer_refined_session_spine_round_trip :
  forall session refined,
    phase1_surface_normalize_transfer_refined_session_spine session =
      Some refined ->
    phase1_surface_transfer_refined_session_spine_tree refined =
      phase1_surface_session_spine_tree session.
Proof.
  intros [nonreference | reference_tree] refined Hnormalize.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_transfer_refined_nonreference_session_spine
        nonreference)
      as [actual |] eqn:Hnonreference; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_transfer_refined_nonreference_session_spine_round_trip
        nonreference actual Hnonreference).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Definition phase1_surface_normalize_transfer_refined_session_tree
  (tree : ParseTree) : option Phase1SurfaceTransferRefinedSessionSpine :=
  match phase1_surface_normalize_session_spine tree with
  | Some session =>
      phase1_surface_normalize_transfer_refined_session_spine session
  | None => None
  end.

Theorem phase1_surface_normalize_transfer_refined_session_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_transfer_refined_session_tree tree = Some refined ->
    phase1_surface_transfer_refined_session_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_transfer_refined_session_tree in Hnormalize.
  destruct (phase1_surface_normalize_session_spine tree)
    as [session |] eqn:Hsession; try discriminate Hnormalize.
  transitivity (phase1_surface_session_spine_tree session).
  - eapply phase1_surface_normalize_transfer_refined_session_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_session_spine_round_trip.
    exact Hsession.
Qed.
