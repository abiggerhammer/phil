From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionTransferParamCarrierSpine
  GrammarAstStaticReferenceSpine
  GrammarAstStaticArgumentsSpine
  GrammarAstStaticTypeArgumentCarrierSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Refine the optional `using static_reference` boundary carried by send/receive
  sessions.  The boundary reference reuses the most-refined static-reference
  carrier currently available, including structured static arguments and
  type-valued static arguments.  Guards, continuations, and non-transfer
  session payloads remain at their existing certified ParseTree boundaries.
*)

Definition phase1_surface_normalize_static_type_arguments_reference_tree
  (tree : ParseTree) : option Phase1SurfaceStaticTypeArgumentsReferenceSpine :=
  match phase1_surface_normalize_static_reference_spine tree with
  | Some base =>
      match phase1_surface_normalize_static_arguments_reference_spine base with
      | Some middle =>
          phase1_surface_normalize_static_type_arguments_reference_spine middle
      | None => None
      end
  | None => None
  end.

Theorem
  phase1_surface_normalize_static_type_arguments_reference_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_static_type_arguments_reference_tree tree =
      Some refined ->
    phase1_surface_static_type_arguments_reference_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_static_type_arguments_reference_tree
    in Hnormalize.
  destruct (phase1_surface_normalize_static_reference_spine tree)
    as [base |] eqn:Hbase; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_static_arguments_reference_spine base)
    as [middle |] eqn:Hmiddle; try discriminate Hnormalize.
  transitivity (phase1_surface_static_arguments_reference_spine_tree middle).
  - eapply
      phase1_surface_normalize_static_type_arguments_reference_spine_round_trip.
    exact Hnormalize.
  - transitivity (phase1_surface_static_reference_spine_tree base).
    + eapply
        phase1_surface_normalize_static_arguments_reference_spine_round_trip.
      exact Hmiddle.
    + eapply phase1_surface_normalize_static_reference_spine_round_trip.
      exact Hbase.
Qed.

Definition phase1_surface_normalize_optional_boundary_reference
  (boundary : option ParseTree)
  : option (option Phase1SurfaceStaticTypeArgumentsReferenceSpine) :=
  match boundary with
  | None => Some None
  | Some boundary_tree =>
      match
        phase1_surface_normalize_static_type_arguments_reference_tree boundary_tree
      with
      | Some reference => Some (Some reference)
      | None => None
      end
  end.

Definition phase1_surface_boundary_refined_annotation_tree
  (boundary : option Phase1SurfaceStaticTypeArgumentsReferenceSpine) : ParseTree :=
  match boundary with
  | None => PTOptionalNone
  | Some reference =>
      PTOptionalSome
        (PTSequence
          [ PTLiteral "using";
            phase1_surface_static_type_arguments_reference_spine_tree reference
          ])
  end.

Theorem phase1_surface_normalize_optional_boundary_reference_round_trip :
  forall boundary refined,
    phase1_surface_normalize_optional_boundary_reference boundary = Some refined ->
    phase1_surface_boundary_refined_annotation_tree refined =
      phase1_surface_optional_named_annotation_tree "using" boundary.
Proof.
  intros [boundary_tree |] refined Hnormalize.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_static_type_arguments_reference_tree boundary_tree)
      as [reference |] eqn:Hreference; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_static_type_arguments_reference_tree_round_trip
        boundary_tree reference Hreference).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Record Phase1SurfaceBoundaryRefinedTypedSessionTransferSpine : Type := {
  phase1_boundary_refined_transfer_direction :
    Phase1SurfaceSessionTransferDirection;
  phase1_boundary_refined_transfer_parameter : Phase1SurfaceTermParamTypeSpine;
  phase1_boundary_refined_transfer_boundary :
    option Phase1SurfaceStaticTypeArgumentsReferenceSpine;
  phase1_boundary_refined_transfer_guard_tree : option ParseTree;
  phase1_boundary_refined_transfer_continuation_tree : ParseTree
}.

Definition phase1_surface_boundary_refined_typed_session_transfer_spine_tree
  (transfer : Phase1SurfaceBoundaryRefinedTypedSessionTransferSpine) : ParseTree :=
  PTSequence
    [ PTLiteral
        (phase1_surface_session_transfer_keyword
          (phase1_boundary_refined_transfer_direction transfer));
      PTLiteral "(";
      phase1_surface_term_param_type_spine_tree
        (phase1_boundary_refined_transfer_parameter transfer);
      PTLiteral ")";
      phase1_surface_boundary_refined_annotation_tree
        (phase1_boundary_refined_transfer_boundary transfer);
      phase1_surface_optional_named_annotation_tree
        "when" (phase1_boundary_refined_transfer_guard_tree transfer);
      PTLiteral "then";
      phase1_boundary_refined_transfer_continuation_tree transfer
    ].

Definition phase1_surface_normalize_boundary_refined_typed_session_transfer_spine
  (transfer : Phase1SurfaceTypedSessionTransferSpine)
  : option Phase1SurfaceBoundaryRefinedTypedSessionTransferSpine :=
  match
    phase1_surface_normalize_optional_boundary_reference
      (phase1_typed_session_transfer_boundary_tree transfer)
  with
  | Some boundary =>
      Some
        {| phase1_boundary_refined_transfer_direction :=
             phase1_typed_session_transfer_direction transfer;
           phase1_boundary_refined_transfer_parameter :=
             phase1_typed_session_transfer_parameter transfer;
           phase1_boundary_refined_transfer_boundary := boundary;
           phase1_boundary_refined_transfer_guard_tree :=
             phase1_typed_session_transfer_guard_tree transfer;
           phase1_boundary_refined_transfer_continuation_tree :=
             phase1_typed_session_transfer_continuation_tree transfer |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_boundary_refined_typed_session_transfer_spine_round_trip :
  forall transfer refined,
    phase1_surface_normalize_boundary_refined_typed_session_transfer_spine transfer =
      Some refined ->
    phase1_surface_boundary_refined_typed_session_transfer_spine_tree refined =
      phase1_surface_typed_session_transfer_spine_tree transfer.
Proof.
  intros [direction parameter boundary guard continuation] refined Hnormalize.
  cbn in Hnormalize.
  destruct (phase1_surface_normalize_optional_boundary_reference boundary)
    as [actual |] eqn:Hboundary; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_optional_boundary_reference_round_trip
      boundary actual Hboundary).
  reflexivity.
Qed.

Inductive Phase1SurfaceBoundaryRefinedTypedTransferNonreferenceSessionSpine : Type :=
| Phase1BoundaryRefinedTypedTransferSession
    (transfer : Phase1SurfaceBoundaryRefinedTypedSessionTransferSpine)
| Phase1BoundaryRefinedTypedOpaqueSelectSession (selected_tree : ParseTree)
| Phase1BoundaryRefinedTypedOpaqueOfferSession (selected_tree : ParseTree)
| Phase1BoundaryRefinedTypedOpaqueEndSession (selected_tree : ParseTree)
| Phase1BoundaryRefinedTypedOpaqueRecursiveSession (selected_tree : ParseTree)
| Phase1BoundaryRefinedTypedOpaqueContinueSession (selected_tree : ParseTree).

Definition
  phase1_surface_boundary_refined_typed_transfer_nonreference_session_spine_tree
  (session : Phase1SurfaceBoundaryRefinedTypedTransferNonreferenceSessionSpine)
  : ParseTree :=
  match session with
  | Phase1BoundaryRefinedTypedTransferSession transfer =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative
          (phase1_surface_session_transfer_index
            (phase1_boundary_refined_transfer_direction transfer))
          (phase1_surface_boundary_refined_typed_session_transfer_spine_tree
            transfer))
  | Phase1BoundaryRefinedTypedOpaqueSelectSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 2 selected_tree)
  | Phase1BoundaryRefinedTypedOpaqueOfferSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 3 selected_tree)
  | Phase1BoundaryRefinedTypedOpaqueEndSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 4 selected_tree)
  | Phase1BoundaryRefinedTypedOpaqueRecursiveSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 5 selected_tree)
  | Phase1BoundaryRefinedTypedOpaqueContinueSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 6 selected_tree)
  end.

Definition
  phase1_surface_normalize_boundary_refined_typed_transfer_nonreference_session_spine
  (session : Phase1SurfaceTypedTransferNonreferenceSessionSpine)
  : option Phase1SurfaceBoundaryRefinedTypedTransferNonreferenceSessionSpine :=
  match session with
  | Phase1TypedTransferSession transfer =>
      match
        phase1_surface_normalize_boundary_refined_typed_session_transfer_spine
          transfer
      with
      | Some refined =>
          Some (Phase1BoundaryRefinedTypedTransferSession refined)
      | None => None
      end
  | Phase1TypedOpaqueSelectSession selected_tree =>
      Some (Phase1BoundaryRefinedTypedOpaqueSelectSession selected_tree)
  | Phase1TypedOpaqueOfferSession selected_tree =>
      Some (Phase1BoundaryRefinedTypedOpaqueOfferSession selected_tree)
  | Phase1TypedOpaqueEndSession selected_tree =>
      Some (Phase1BoundaryRefinedTypedOpaqueEndSession selected_tree)
  | Phase1TypedOpaqueRecursiveSession selected_tree =>
      Some (Phase1BoundaryRefinedTypedOpaqueRecursiveSession selected_tree)
  | Phase1TypedOpaqueContinueSession selected_tree =>
      Some (Phase1BoundaryRefinedTypedOpaqueContinueSession selected_tree)
  end.

Theorem
  phase1_surface_normalize_boundary_refined_typed_transfer_nonreference_session_spine_round_trip :
  forall session refined,
    phase1_surface_normalize_boundary_refined_typed_transfer_nonreference_session_spine
      session = Some refined ->
    phase1_surface_boundary_refined_typed_transfer_nonreference_session_spine_tree
      refined =
    phase1_surface_typed_transfer_nonreference_session_spine_tree session.
Proof.
  intros [transfer | selected | selected | selected | selected | selected]
    refined Hnormalize.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_boundary_refined_typed_session_transfer_spine
        transfer)
      as [actual |] eqn:Htransfer; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_boundary_refined_typed_session_transfer_spine_round_trip
        transfer actual Htransfer).
    reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
Qed.

Definition
  phase1_surface_normalize_boundary_refined_typed_transfer_nonreference_session_tree
  (tree : ParseTree)
  : option Phase1SurfaceBoundaryRefinedTypedTransferNonreferenceSessionSpine :=
  match phase1_surface_normalize_typed_transfer_nonreference_session_tree tree with
  | Some session =>
      phase1_surface_normalize_boundary_refined_typed_transfer_nonreference_session_spine
        session
  | None => None
  end.

Theorem
  phase1_surface_normalize_boundary_refined_typed_transfer_nonreference_session_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_boundary_refined_typed_transfer_nonreference_session_tree
      tree = Some refined ->
    phase1_surface_boundary_refined_typed_transfer_nonreference_session_spine_tree
      refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold
    phase1_surface_normalize_boundary_refined_typed_transfer_nonreference_session_tree
    in Hnormalize.
  destruct (phase1_surface_normalize_typed_transfer_nonreference_session_tree tree)
    as [session |] eqn:Hsession; try discriminate Hnormalize.
  transitivity
    (phase1_surface_typed_transfer_nonreference_session_spine_tree session).
  - eapply
      phase1_surface_normalize_boundary_refined_typed_transfer_nonreference_session_spine_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_typed_transfer_nonreference_session_tree_round_trip.
    exact Hsession.
Qed.

Inductive Phase1SurfaceBoundaryRefinedTypedTransferSessionSpine : Type :=
| Phase1BoundaryRefinedTypedTransferNonreferenceSession
    (session : Phase1SurfaceBoundaryRefinedTypedTransferNonreferenceSessionSpine)
| Phase1BoundaryRefinedTypedTransferStaticReferenceSession
    (reference_tree : ParseTree).

Definition phase1_surface_boundary_refined_typed_transfer_session_spine_tree
  (session : Phase1SurfaceBoundaryRefinedTypedTransferSessionSpine) : ParseTree :=
  match session with
  | Phase1BoundaryRefinedTypedTransferNonreferenceSession nonreference =>
      PTNonterminal "session_expression"
        (PTAlternative 0
          (phase1_surface_boundary_refined_typed_transfer_nonreference_session_spine_tree
            nonreference))
  | Phase1BoundaryRefinedTypedTransferStaticReferenceSession reference_tree =>
      PTNonterminal "session_expression"
        (PTAlternative 1 reference_tree)
  end.

Definition phase1_surface_normalize_boundary_refined_typed_transfer_session_spine
  (session : Phase1SurfaceTypedTransferSessionSpine)
  : option Phase1SurfaceBoundaryRefinedTypedTransferSessionSpine :=
  match session with
  | Phase1TypedTransferNonreferenceSession nonreference =>
      match
        phase1_surface_normalize_boundary_refined_typed_transfer_nonreference_session_spine
          nonreference
      with
      | Some refined =>
          Some (Phase1BoundaryRefinedTypedTransferNonreferenceSession refined)
      | None => None
      end
  | Phase1TypedTransferStaticReferenceSession reference_tree =>
      Some (Phase1BoundaryRefinedTypedTransferStaticReferenceSession reference_tree)
  end.

Theorem
  phase1_surface_normalize_boundary_refined_typed_transfer_session_spine_round_trip :
  forall session refined,
    phase1_surface_normalize_boundary_refined_typed_transfer_session_spine session =
      Some refined ->
    phase1_surface_boundary_refined_typed_transfer_session_spine_tree refined =
      phase1_surface_typed_transfer_session_spine_tree session.
Proof.
  intros [nonreference | reference_tree] refined Hnormalize.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_boundary_refined_typed_transfer_nonreference_session_spine
        nonreference)
      as [actual |] eqn:Hnonreference; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_boundary_refined_typed_transfer_nonreference_session_spine_round_trip
        nonreference actual Hnonreference).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Definition phase1_surface_normalize_boundary_refined_typed_transfer_session_tree
  (tree : ParseTree)
  : option Phase1SurfaceBoundaryRefinedTypedTransferSessionSpine :=
  match phase1_surface_normalize_typed_transfer_session_tree tree with
  | Some session =>
      phase1_surface_normalize_boundary_refined_typed_transfer_session_spine
        session
  | None => None
  end.

Theorem
  phase1_surface_normalize_boundary_refined_typed_transfer_session_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_boundary_refined_typed_transfer_session_tree tree =
      Some refined ->
    phase1_surface_boundary_refined_typed_transfer_session_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_boundary_refined_typed_transfer_session_tree
    in Hnormalize.
  destruct (phase1_surface_normalize_typed_transfer_session_tree tree)
    as [session |] eqn:Hsession; try discriminate Hnormalize.
  transitivity (phase1_surface_typed_transfer_session_spine_tree session).
  - eapply
      phase1_surface_normalize_boundary_refined_typed_transfer_session_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_typed_transfer_session_tree_round_trip.
    exact Hsession.
Qed.
