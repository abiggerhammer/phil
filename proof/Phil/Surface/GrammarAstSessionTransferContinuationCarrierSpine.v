From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionTransferGuardCarrierSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Refine the immediate `then session_expression` continuation carried by
  send/receive sessions.  This slice deliberately normalizes one continuation
  layer through the already-closed guard-refined full session carrier.  The
  resulting nested carrier is lossless while leaving transitive recursive
  closure for a dedicated successor.
*)

Record Phase1SurfaceContinuationRefinedSessionTransferSpine : Type := {
  phase1_continuation_refined_transfer_direction :
    Phase1SurfaceSessionTransferDirection;
  phase1_continuation_refined_transfer_parameter : Phase1SurfaceTermParamTypeSpine;
  phase1_continuation_refined_transfer_boundary :
    option Phase1SurfaceStaticTypeArgumentsReferenceSpine;
  phase1_continuation_refined_transfer_guard : option Phase1SurfacePropositionSpine;
  phase1_continuation_refined_transfer_continuation :
    Phase1SurfaceGuardRefinedBoundaryTypedTransferSessionSpine
}.

Definition phase1_surface_continuation_refined_session_transfer_spine_tree
  (transfer : Phase1SurfaceContinuationRefinedSessionTransferSpine)
  : ParseTree :=
  PTSequence
    [ PTLiteral
        (phase1_surface_session_transfer_keyword
          (phase1_continuation_refined_transfer_direction transfer));
      PTLiteral "(";
      phase1_surface_term_param_type_spine_tree
        (phase1_continuation_refined_transfer_parameter transfer);
      PTLiteral ")";
      phase1_surface_boundary_refined_annotation_tree
        (phase1_continuation_refined_transfer_boundary transfer);
      phase1_surface_guard_refined_annotation_tree
        (phase1_continuation_refined_transfer_guard transfer);
      PTLiteral "then";
      phase1_surface_guard_refined_boundary_typed_transfer_session_spine_tree
        (phase1_continuation_refined_transfer_continuation transfer)
    ].

Definition phase1_surface_normalize_continuation_refined_session_transfer_spine
  (transfer : Phase1SurfaceGuardRefinedBoundaryTypedSessionTransferSpine)
  : option Phase1SurfaceContinuationRefinedSessionTransferSpine :=
  match
    phase1_surface_normalize_guard_refined_boundary_typed_transfer_session_tree
      (phase1_guard_refined_transfer_continuation_tree transfer)
  with
  | Some continuation =>
      Some
        {| phase1_continuation_refined_transfer_direction :=
             phase1_guard_refined_transfer_direction transfer;
           phase1_continuation_refined_transfer_parameter :=
             phase1_guard_refined_transfer_parameter transfer;
           phase1_continuation_refined_transfer_boundary :=
             phase1_guard_refined_transfer_boundary transfer;
           phase1_continuation_refined_transfer_guard :=
             phase1_guard_refined_transfer_guard transfer;
           phase1_continuation_refined_transfer_continuation := continuation |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_continuation_refined_session_transfer_spine_round_trip :
  forall transfer refined,
    phase1_surface_normalize_continuation_refined_session_transfer_spine transfer =
      Some refined ->
    phase1_surface_continuation_refined_session_transfer_spine_tree refined =
      phase1_surface_guard_refined_boundary_typed_session_transfer_spine_tree
        transfer.
Proof.
  intros [direction parameter boundary guard continuation_tree]
    refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_guard_refined_boundary_typed_transfer_session_tree
      continuation_tree)
    as [continuation |] eqn:Hcontinuation; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_guard_refined_boundary_typed_transfer_session_tree_round_trip
      continuation_tree continuation Hcontinuation).
  reflexivity.
Qed.

Inductive Phase1SurfaceContinuationRefinedTransferNonreferenceSessionSpine
  : Type :=
| Phase1ContinuationRefinedTransferSession
    (transfer : Phase1SurfaceContinuationRefinedSessionTransferSpine)
| Phase1ContinuationRefinedOpaqueSelectSession (selected_tree : ParseTree)
| Phase1ContinuationRefinedOpaqueOfferSession (selected_tree : ParseTree)
| Phase1ContinuationRefinedOpaqueEndSession (selected_tree : ParseTree)
| Phase1ContinuationRefinedOpaqueRecursiveSession (selected_tree : ParseTree)
| Phase1ContinuationRefinedOpaqueContinueSession (selected_tree : ParseTree).

Definition
  phase1_surface_continuation_refined_transfer_nonreference_session_spine_tree
  (session : Phase1SurfaceContinuationRefinedTransferNonreferenceSessionSpine)
  : ParseTree :=
  match session with
  | Phase1ContinuationRefinedTransferSession transfer =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative
          (phase1_surface_session_transfer_index
            (phase1_continuation_refined_transfer_direction transfer))
          (phase1_surface_continuation_refined_session_transfer_spine_tree
            transfer))
  | Phase1ContinuationRefinedOpaqueSelectSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 2 selected_tree)
  | Phase1ContinuationRefinedOpaqueOfferSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 3 selected_tree)
  | Phase1ContinuationRefinedOpaqueEndSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 4 selected_tree)
  | Phase1ContinuationRefinedOpaqueRecursiveSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 5 selected_tree)
  | Phase1ContinuationRefinedOpaqueContinueSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 6 selected_tree)
  end.

Definition
  phase1_surface_normalize_continuation_refined_transfer_nonreference_session_spine
  (session : Phase1SurfaceGuardRefinedBoundaryTypedTransferNonreferenceSessionSpine)
  : option Phase1SurfaceContinuationRefinedTransferNonreferenceSessionSpine :=
  match session with
  | Phase1GuardRefinedBoundaryTypedTransferSession transfer =>
      match
        phase1_surface_normalize_continuation_refined_session_transfer_spine
          transfer
      with
      | Some refined => Some (Phase1ContinuationRefinedTransferSession refined)
      | None => None
      end
  | Phase1GuardRefinedBoundaryTypedOpaqueSelectSession selected_tree =>
      Some (Phase1ContinuationRefinedOpaqueSelectSession selected_tree)
  | Phase1GuardRefinedBoundaryTypedOpaqueOfferSession selected_tree =>
      Some (Phase1ContinuationRefinedOpaqueOfferSession selected_tree)
  | Phase1GuardRefinedBoundaryTypedOpaqueEndSession selected_tree =>
      Some (Phase1ContinuationRefinedOpaqueEndSession selected_tree)
  | Phase1GuardRefinedBoundaryTypedOpaqueRecursiveSession selected_tree =>
      Some (Phase1ContinuationRefinedOpaqueRecursiveSession selected_tree)
  | Phase1GuardRefinedBoundaryTypedOpaqueContinueSession selected_tree =>
      Some (Phase1ContinuationRefinedOpaqueContinueSession selected_tree)
  end.

Theorem
  phase1_surface_normalize_continuation_refined_transfer_nonreference_session_spine_round_trip :
  forall session refined,
    phase1_surface_normalize_continuation_refined_transfer_nonreference_session_spine
      session = Some refined ->
    phase1_surface_continuation_refined_transfer_nonreference_session_spine_tree
      refined =
    phase1_surface_guard_refined_boundary_typed_transfer_nonreference_session_spine_tree
      session.
Proof.
  intros [transfer | selected | selected | selected | selected | selected]
    refined Hnormalize.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_continuation_refined_session_transfer_spine
        transfer)
      as [actual |] eqn:Htransfer; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_continuation_refined_session_transfer_spine_round_trip
        transfer actual Htransfer).
    reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
Qed.

Definition
  phase1_surface_normalize_continuation_refined_transfer_nonreference_session_tree
  (tree : ParseTree)
  : option Phase1SurfaceContinuationRefinedTransferNonreferenceSessionSpine :=
  match
    phase1_surface_normalize_guard_refined_boundary_typed_transfer_nonreference_session_tree
      tree
  with
  | Some session =>
      phase1_surface_normalize_continuation_refined_transfer_nonreference_session_spine
        session
  | None => None
  end.

Theorem
  phase1_surface_normalize_continuation_refined_transfer_nonreference_session_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_continuation_refined_transfer_nonreference_session_tree
      tree = Some refined ->
    phase1_surface_continuation_refined_transfer_nonreference_session_spine_tree
      refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold
    phase1_surface_normalize_continuation_refined_transfer_nonreference_session_tree
    in Hnormalize.
  destruct
    (phase1_surface_normalize_guard_refined_boundary_typed_transfer_nonreference_session_tree
      tree)
    as [session |] eqn:Hsession; try discriminate Hnormalize.
  transitivity
    (phase1_surface_guard_refined_boundary_typed_transfer_nonreference_session_spine_tree
      session).
  - eapply
      phase1_surface_normalize_continuation_refined_transfer_nonreference_session_spine_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_guard_refined_boundary_typed_transfer_nonreference_session_tree_round_trip.
    exact Hsession.
Qed.

Inductive Phase1SurfaceContinuationRefinedTransferSessionSpine : Type :=
| Phase1ContinuationRefinedTransferNonreferenceSession
    (session : Phase1SurfaceContinuationRefinedTransferNonreferenceSessionSpine)
| Phase1ContinuationRefinedTransferStaticReferenceSession
    (reference_tree : ParseTree).

Definition phase1_surface_continuation_refined_transfer_session_spine_tree
  (session : Phase1SurfaceContinuationRefinedTransferSessionSpine)
  : ParseTree :=
  match session with
  | Phase1ContinuationRefinedTransferNonreferenceSession nonreference =>
      PTNonterminal "session_expression"
        (PTAlternative 0
          (phase1_surface_continuation_refined_transfer_nonreference_session_spine_tree
            nonreference))
  | Phase1ContinuationRefinedTransferStaticReferenceSession reference_tree =>
      PTNonterminal "session_expression"
        (PTAlternative 1 reference_tree)
  end.

Definition phase1_surface_normalize_continuation_refined_transfer_session_spine
  (session : Phase1SurfaceGuardRefinedBoundaryTypedTransferSessionSpine)
  : option Phase1SurfaceContinuationRefinedTransferSessionSpine :=
  match session with
  | Phase1GuardRefinedBoundaryTypedTransferNonreferenceSession nonreference =>
      match
        phase1_surface_normalize_continuation_refined_transfer_nonreference_session_spine
          nonreference
      with
      | Some refined =>
          Some (Phase1ContinuationRefinedTransferNonreferenceSession refined)
      | None => None
      end
  | Phase1GuardRefinedBoundaryTypedTransferStaticReferenceSession reference_tree =>
      Some (Phase1ContinuationRefinedTransferStaticReferenceSession reference_tree)
  end.

Theorem
  phase1_surface_normalize_continuation_refined_transfer_session_spine_round_trip :
  forall session refined,
    phase1_surface_normalize_continuation_refined_transfer_session_spine session =
      Some refined ->
    phase1_surface_continuation_refined_transfer_session_spine_tree refined =
      phase1_surface_guard_refined_boundary_typed_transfer_session_spine_tree
        session.
Proof.
  intros [nonreference | reference_tree] refined Hnormalize.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_continuation_refined_transfer_nonreference_session_spine
        nonreference)
      as [actual |] eqn:Hnonreference; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_continuation_refined_transfer_nonreference_session_spine_round_trip
        nonreference actual Hnonreference).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Definition phase1_surface_normalize_continuation_refined_transfer_session_tree
  (tree : ParseTree)
  : option Phase1SurfaceContinuationRefinedTransferSessionSpine :=
  match phase1_surface_normalize_guard_refined_boundary_typed_transfer_session_tree tree with
  | Some session =>
      phase1_surface_normalize_continuation_refined_transfer_session_spine session
  | None => None
  end.

Theorem
  phase1_surface_normalize_continuation_refined_transfer_session_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_continuation_refined_transfer_session_tree tree =
      Some refined ->
    phase1_surface_continuation_refined_transfer_session_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_continuation_refined_transfer_session_tree
    in Hnormalize.
  destruct
    (phase1_surface_normalize_guard_refined_boundary_typed_transfer_session_tree tree)
    as [session |] eqn:Hsession; try discriminate Hnormalize.
  transitivity
    (phase1_surface_guard_refined_boundary_typed_transfer_session_spine_tree session).
  - eapply
      phase1_surface_normalize_continuation_refined_transfer_session_spine_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_guard_refined_boundary_typed_transfer_session_tree_round_trip.
    exact Hsession.
Qed.
