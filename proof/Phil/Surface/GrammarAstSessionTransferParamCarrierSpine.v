From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstTermParamTypeSpine
  GrammarAstSessionTransferCarrierSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Lift the reusable term_param refinement through send/receive transfers and
  the already-established nonreference/session-expression carrier layers.
  Boundary references, guards, recursive continuations, and non-transfer
  session payloads retain their current certified ParseTree boundaries.
*)

Record Phase1SurfaceTypedSessionTransferSpine : Type := {
  phase1_typed_session_transfer_direction :
    Phase1SurfaceSessionTransferDirection;
  phase1_typed_session_transfer_parameter : Phase1SurfaceTermParamTypeSpine;
  phase1_typed_session_transfer_boundary_tree : option ParseTree;
  phase1_typed_session_transfer_guard_tree : option ParseTree;
  phase1_typed_session_transfer_continuation_tree : ParseTree
}.

Definition phase1_surface_typed_session_transfer_spine_tree
  (transfer : Phase1SurfaceTypedSessionTransferSpine) : ParseTree :=
  PTSequence
    [ PTLiteral
        (phase1_surface_session_transfer_keyword
          (phase1_typed_session_transfer_direction transfer));
      PTLiteral "(";
      phase1_surface_term_param_type_spine_tree
        (phase1_typed_session_transfer_parameter transfer);
      PTLiteral ")";
      phase1_surface_optional_named_annotation_tree
        "using" (phase1_typed_session_transfer_boundary_tree transfer);
      phase1_surface_optional_named_annotation_tree
        "when" (phase1_typed_session_transfer_guard_tree transfer);
      PTLiteral "then";
      phase1_typed_session_transfer_continuation_tree transfer
    ].

Definition phase1_surface_normalize_typed_session_transfer_spine
  (transfer : Phase1SurfaceSessionTransferSpine)
  : option Phase1SurfaceTypedSessionTransferSpine :=
  match
    phase1_surface_normalize_term_param_type_spine
      (phase1_session_transfer_parameter_tree transfer)
  with
  | Some parameter =>
      Some
        {| phase1_typed_session_transfer_direction :=
             phase1_session_transfer_direction transfer;
           phase1_typed_session_transfer_parameter := parameter;
           phase1_typed_session_transfer_boundary_tree :=
             phase1_session_transfer_boundary_tree transfer;
           phase1_typed_session_transfer_guard_tree :=
             phase1_session_transfer_guard_tree transfer;
           phase1_typed_session_transfer_continuation_tree :=
             phase1_session_transfer_continuation_tree transfer |}
  | None => None
  end.

Theorem phase1_surface_normalize_typed_session_transfer_spine_round_trip :
  forall transfer refined,
    phase1_surface_normalize_typed_session_transfer_spine transfer =
      Some refined ->
    phase1_surface_typed_session_transfer_spine_tree refined =
      phase1_surface_session_transfer_spine_tree transfer.
Proof.
  intros [direction parameter_tree boundary guard continuation]
    refined Hnormalize.
  cbn in Hnormalize.
  destruct (phase1_surface_normalize_term_param_type_spine parameter_tree)
    as [parameter |] eqn:Hparameter; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_term_param_type_spine_round_trip
      parameter_tree parameter Hparameter).
  reflexivity.
Qed.

Inductive Phase1SurfaceTypedTransferNonreferenceSessionSpine : Type :=
| Phase1TypedTransferSession
    (transfer : Phase1SurfaceTypedSessionTransferSpine)
| Phase1TypedOpaqueSelectSession (selected_tree : ParseTree)
| Phase1TypedOpaqueOfferSession (selected_tree : ParseTree)
| Phase1TypedOpaqueEndSession (selected_tree : ParseTree)
| Phase1TypedOpaqueRecursiveSession (selected_tree : ParseTree)
| Phase1TypedOpaqueContinueSession (selected_tree : ParseTree).

Definition phase1_surface_typed_transfer_nonreference_session_spine_tree
  (session : Phase1SurfaceTypedTransferNonreferenceSessionSpine) : ParseTree :=
  match session with
  | Phase1TypedTransferSession transfer =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative
          (phase1_surface_session_transfer_index
            (phase1_typed_session_transfer_direction transfer))
          (phase1_surface_typed_session_transfer_spine_tree transfer))
  | Phase1TypedOpaqueSelectSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 2 selected_tree)
  | Phase1TypedOpaqueOfferSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 3 selected_tree)
  | Phase1TypedOpaqueEndSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 4 selected_tree)
  | Phase1TypedOpaqueRecursiveSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 5 selected_tree)
  | Phase1TypedOpaqueContinueSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 6 selected_tree)
  end.

Definition phase1_surface_normalize_typed_transfer_nonreference_session_spine
  (session : Phase1SurfaceTransferRefinedNonreferenceSessionSpine)
  : option Phase1SurfaceTypedTransferNonreferenceSessionSpine :=
  match session with
  | Phase1RefinedTransferSession transfer =>
      match phase1_surface_normalize_typed_session_transfer_spine transfer with
      | Some refined => Some (Phase1TypedTransferSession refined)
      | None => None
      end
  | Phase1OpaqueSelectSession selected_tree =>
      Some (Phase1TypedOpaqueSelectSession selected_tree)
  | Phase1OpaqueOfferSession selected_tree =>
      Some (Phase1TypedOpaqueOfferSession selected_tree)
  | Phase1OpaqueEndSession selected_tree =>
      Some (Phase1TypedOpaqueEndSession selected_tree)
  | Phase1OpaqueRecursiveSession selected_tree =>
      Some (Phase1TypedOpaqueRecursiveSession selected_tree)
  | Phase1OpaqueContinueSession selected_tree =>
      Some (Phase1TypedOpaqueContinueSession selected_tree)
  end.

Theorem
  phase1_surface_normalize_typed_transfer_nonreference_session_spine_round_trip :
  forall session refined,
    phase1_surface_normalize_typed_transfer_nonreference_session_spine session =
      Some refined ->
    phase1_surface_typed_transfer_nonreference_session_spine_tree refined =
      phase1_surface_transfer_refined_nonreference_session_spine_tree session.
Proof.
  intros [transfer | selected | selected | selected | selected | selected]
    refined Hnormalize.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_typed_session_transfer_spine transfer)
      as [actual |] eqn:Htransfer; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_typed_session_transfer_spine_round_trip
        transfer actual Htransfer).
    reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
Qed.

Definition phase1_surface_normalize_typed_transfer_nonreference_session_tree
  (tree : ParseTree)
  : option Phase1SurfaceTypedTransferNonreferenceSessionSpine :=
  match phase1_surface_normalize_transfer_refined_nonreference_session_tree tree with
  | Some session =>
      phase1_surface_normalize_typed_transfer_nonreference_session_spine session
  | None => None
  end.

Theorem
  phase1_surface_normalize_typed_transfer_nonreference_session_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_typed_transfer_nonreference_session_tree tree =
      Some refined ->
    phase1_surface_typed_transfer_nonreference_session_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_typed_transfer_nonreference_session_tree
    in Hnormalize.
  destruct (phase1_surface_normalize_transfer_refined_nonreference_session_tree tree)
    as [session |] eqn:Hsession; try discriminate Hnormalize.
  transitivity
    (phase1_surface_transfer_refined_nonreference_session_spine_tree session).
  - eapply
      phase1_surface_normalize_typed_transfer_nonreference_session_spine_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_transfer_refined_nonreference_session_tree_round_trip.
    exact Hsession.
Qed.

Inductive Phase1SurfaceTypedTransferSessionSpine : Type :=
| Phase1TypedTransferNonreferenceSession
    (session : Phase1SurfaceTypedTransferNonreferenceSessionSpine)
| Phase1TypedTransferStaticReferenceSession
    (reference_tree : ParseTree).

Definition phase1_surface_typed_transfer_session_spine_tree
  (session : Phase1SurfaceTypedTransferSessionSpine) : ParseTree :=
  match session with
  | Phase1TypedTransferNonreferenceSession nonreference =>
      PTNonterminal "session_expression"
        (PTAlternative 0
          (phase1_surface_typed_transfer_nonreference_session_spine_tree
            nonreference))
  | Phase1TypedTransferStaticReferenceSession reference_tree =>
      PTNonterminal "session_expression"
        (PTAlternative 1 reference_tree)
  end.

Definition phase1_surface_normalize_typed_transfer_session_spine
  (session : Phase1SurfaceTransferRefinedSessionSpine)
  : option Phase1SurfaceTypedTransferSessionSpine :=
  match session with
  | Phase1TransferRefinedNonreferenceSession nonreference =>
      match
        phase1_surface_normalize_typed_transfer_nonreference_session_spine
          nonreference
      with
      | Some refined => Some (Phase1TypedTransferNonreferenceSession refined)
      | None => None
      end
  | Phase1TransferRefinedStaticReferenceSession reference_tree =>
      Some (Phase1TypedTransferStaticReferenceSession reference_tree)
  end.

Theorem phase1_surface_normalize_typed_transfer_session_spine_round_trip :
  forall session refined,
    phase1_surface_normalize_typed_transfer_session_spine session = Some refined ->
    phase1_surface_typed_transfer_session_spine_tree refined =
      phase1_surface_transfer_refined_session_spine_tree session.
Proof.
  intros [nonreference | reference_tree] refined Hnormalize.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_typed_transfer_nonreference_session_spine
        nonreference)
      as [actual |] eqn:Hnonreference; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_typed_transfer_nonreference_session_spine_round_trip
        nonreference actual Hnonreference).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Definition phase1_surface_normalize_typed_transfer_session_tree
  (tree : ParseTree) : option Phase1SurfaceTypedTransferSessionSpine :=
  match phase1_surface_normalize_transfer_refined_session_tree tree with
  | Some session => phase1_surface_normalize_typed_transfer_session_spine session
  | None => None
  end.

Theorem phase1_surface_normalize_typed_transfer_session_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_typed_transfer_session_tree tree = Some refined ->
    phase1_surface_typed_transfer_session_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_typed_transfer_session_tree in Hnormalize.
  destruct (phase1_surface_normalize_transfer_refined_session_tree tree)
    as [session |] eqn:Hsession; try discriminate Hnormalize.
  transitivity (phase1_surface_transfer_refined_session_spine_tree session).
  - eapply phase1_surface_normalize_typed_transfer_session_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_transfer_refined_session_tree_round_trip.
    exact Hsession.
Qed.
