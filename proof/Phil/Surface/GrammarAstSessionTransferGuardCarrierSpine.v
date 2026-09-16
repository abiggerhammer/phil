From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionTransferBoundaryCarrierSpine
  GrammarAstPropositionSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Refine the optional `when proposition` guard carried by send/receive
  sessions.  The proposition itself reuses the shared precedence carrier from
  #1013/#1015.  Recursive proposition payload interiors, continuation sessions,
  and non-transfer session payloads remain at their current certified
  boundaries.
*)

Definition phase1_surface_normalize_optional_guard_proposition
  (guard : option ParseTree) : option (option Phase1SurfacePropositionSpine) :=
  match guard with
  | None => Some None
  | Some guard_tree =>
      match phase1_surface_normalize_proposition_spine guard_tree with
      | Some proposition => Some (Some proposition)
      | None => None
      end
  end.

Definition phase1_surface_guard_refined_annotation_tree
  (guard : option Phase1SurfacePropositionSpine) : ParseTree :=
  match guard with
  | None => PTOptionalNone
  | Some proposition =>
      PTOptionalSome
        (PTSequence
          [ PTLiteral "when";
            phase1_surface_proposition_spine_tree proposition
          ])
  end.

Theorem phase1_surface_normalize_optional_guard_proposition_round_trip :
  forall guard refined,
    phase1_surface_normalize_optional_guard_proposition guard = Some refined ->
    phase1_surface_guard_refined_annotation_tree refined =
      phase1_surface_optional_named_annotation_tree "when" guard.
Proof.
  intros [guard_tree |] refined Hnormalize.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_proposition_spine guard_tree)
      as [proposition |] eqn:Hproposition; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite (phase1_surface_normalize_proposition_spine_round_trip
      guard_tree proposition Hproposition).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Record Phase1SurfaceGuardRefinedBoundaryTypedSessionTransferSpine : Type := {
  phase1_guard_refined_transfer_direction :
    Phase1SurfaceSessionTransferDirection;
  phase1_guard_refined_transfer_parameter : Phase1SurfaceTermParamTypeSpine;
  phase1_guard_refined_transfer_boundary :
    option Phase1SurfaceStaticTypeArgumentsReferenceSpine;
  phase1_guard_refined_transfer_guard : option Phase1SurfacePropositionSpine;
  phase1_guard_refined_transfer_continuation_tree : ParseTree
}.

Definition phase1_surface_guard_refined_boundary_typed_session_transfer_spine_tree
  (transfer : Phase1SurfaceGuardRefinedBoundaryTypedSessionTransferSpine)
  : ParseTree :=
  PTSequence
    [ PTLiteral
        (phase1_surface_session_transfer_keyword
          (phase1_guard_refined_transfer_direction transfer));
      PTLiteral "(";
      phase1_surface_term_param_type_spine_tree
        (phase1_guard_refined_transfer_parameter transfer);
      PTLiteral ")";
      phase1_surface_boundary_refined_annotation_tree
        (phase1_guard_refined_transfer_boundary transfer);
      phase1_surface_guard_refined_annotation_tree
        (phase1_guard_refined_transfer_guard transfer);
      PTLiteral "then";
      phase1_guard_refined_transfer_continuation_tree transfer
    ].

Definition phase1_surface_normalize_guard_refined_boundary_typed_session_transfer_spine
  (transfer : Phase1SurfaceBoundaryRefinedTypedSessionTransferSpine)
  : option Phase1SurfaceGuardRefinedBoundaryTypedSessionTransferSpine :=
  match
    phase1_surface_normalize_optional_guard_proposition
      (phase1_boundary_refined_transfer_guard_tree transfer)
  with
  | Some guard =>
      Some
        {| phase1_guard_refined_transfer_direction :=
             phase1_boundary_refined_transfer_direction transfer;
           phase1_guard_refined_transfer_parameter :=
             phase1_boundary_refined_transfer_parameter transfer;
           phase1_guard_refined_transfer_boundary :=
             phase1_boundary_refined_transfer_boundary transfer;
           phase1_guard_refined_transfer_guard := guard;
           phase1_guard_refined_transfer_continuation_tree :=
             phase1_boundary_refined_transfer_continuation_tree transfer |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_guard_refined_boundary_typed_session_transfer_spine_round_trip :
  forall transfer refined,
    phase1_surface_normalize_guard_refined_boundary_typed_session_transfer_spine
      transfer = Some refined ->
    phase1_surface_guard_refined_boundary_typed_session_transfer_spine_tree
      refined =
    phase1_surface_boundary_refined_typed_session_transfer_spine_tree transfer.
Proof.
  intros [direction parameter boundary guard continuation] refined Hnormalize.
  cbn in Hnormalize.
  destruct (phase1_surface_normalize_optional_guard_proposition guard)
    as [actual |] eqn:Hguard; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_optional_guard_proposition_round_trip
      guard actual Hguard).
  reflexivity.
Qed.

Inductive Phase1SurfaceGuardRefinedBoundaryTypedTransferNonreferenceSessionSpine
  : Type :=
| Phase1GuardRefinedBoundaryTypedTransferSession
    (transfer : Phase1SurfaceGuardRefinedBoundaryTypedSessionTransferSpine)
| Phase1GuardRefinedBoundaryTypedOpaqueSelectSession
    (selected_tree : ParseTree)
| Phase1GuardRefinedBoundaryTypedOpaqueOfferSession
    (selected_tree : ParseTree)
| Phase1GuardRefinedBoundaryTypedOpaqueEndSession
    (selected_tree : ParseTree)
| Phase1GuardRefinedBoundaryTypedOpaqueRecursiveSession
    (selected_tree : ParseTree)
| Phase1GuardRefinedBoundaryTypedOpaqueContinueSession
    (selected_tree : ParseTree).

Definition
  phase1_surface_guard_refined_boundary_typed_transfer_nonreference_session_spine_tree
  (session :
    Phase1SurfaceGuardRefinedBoundaryTypedTransferNonreferenceSessionSpine)
  : ParseTree :=
  match session with
  | Phase1GuardRefinedBoundaryTypedTransferSession transfer =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative
          (phase1_surface_session_transfer_index
            (phase1_guard_refined_transfer_direction transfer))
          (phase1_surface_guard_refined_boundary_typed_session_transfer_spine_tree
            transfer))
  | Phase1GuardRefinedBoundaryTypedOpaqueSelectSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 2 selected_tree)
  | Phase1GuardRefinedBoundaryTypedOpaqueOfferSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 3 selected_tree)
  | Phase1GuardRefinedBoundaryTypedOpaqueEndSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 4 selected_tree)
  | Phase1GuardRefinedBoundaryTypedOpaqueRecursiveSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 5 selected_tree)
  | Phase1GuardRefinedBoundaryTypedOpaqueContinueSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 6 selected_tree)
  end.

Definition
  phase1_surface_normalize_guard_refined_boundary_typed_transfer_nonreference_session_spine
  (session : Phase1SurfaceBoundaryRefinedTypedTransferNonreferenceSessionSpine)
  : option
      Phase1SurfaceGuardRefinedBoundaryTypedTransferNonreferenceSessionSpine :=
  match session with
  | Phase1BoundaryRefinedTypedTransferSession transfer =>
      match
        phase1_surface_normalize_guard_refined_boundary_typed_session_transfer_spine
          transfer
      with
      | Some refined =>
          Some (Phase1GuardRefinedBoundaryTypedTransferSession refined)
      | None => None
      end
  | Phase1BoundaryRefinedTypedOpaqueSelectSession selected_tree =>
      Some (Phase1GuardRefinedBoundaryTypedOpaqueSelectSession selected_tree)
  | Phase1BoundaryRefinedTypedOpaqueOfferSession selected_tree =>
      Some (Phase1GuardRefinedBoundaryTypedOpaqueOfferSession selected_tree)
  | Phase1BoundaryRefinedTypedOpaqueEndSession selected_tree =>
      Some (Phase1GuardRefinedBoundaryTypedOpaqueEndSession selected_tree)
  | Phase1BoundaryRefinedTypedOpaqueRecursiveSession selected_tree =>
      Some (Phase1GuardRefinedBoundaryTypedOpaqueRecursiveSession selected_tree)
  | Phase1BoundaryRefinedTypedOpaqueContinueSession selected_tree =>
      Some (Phase1GuardRefinedBoundaryTypedOpaqueContinueSession selected_tree)
  end.

Theorem
  phase1_surface_normalize_guard_refined_boundary_typed_transfer_nonreference_session_spine_round_trip :
  forall session refined,
    phase1_surface_normalize_guard_refined_boundary_typed_transfer_nonreference_session_spine
      session = Some refined ->
    phase1_surface_guard_refined_boundary_typed_transfer_nonreference_session_spine_tree
      refined =
    phase1_surface_boundary_refined_typed_transfer_nonreference_session_spine_tree
      session.
Proof.
  intros [transfer | selected | selected | selected | selected | selected]
    refined Hnormalize.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_guard_refined_boundary_typed_session_transfer_spine
        transfer)
      as [actual |] eqn:Htransfer; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_guard_refined_boundary_typed_session_transfer_spine_round_trip
        transfer actual Htransfer).
    reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
Qed.

Definition
  phase1_surface_normalize_guard_refined_boundary_typed_transfer_nonreference_session_tree
  (tree : ParseTree)
  : option
      Phase1SurfaceGuardRefinedBoundaryTypedTransferNonreferenceSessionSpine :=
  match
    phase1_surface_normalize_boundary_refined_typed_transfer_nonreference_session_tree
      tree
  with
  | Some session =>
      phase1_surface_normalize_guard_refined_boundary_typed_transfer_nonreference_session_spine
        session
  | None => None
  end.

Theorem
  phase1_surface_normalize_guard_refined_boundary_typed_transfer_nonreference_session_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_guard_refined_boundary_typed_transfer_nonreference_session_tree
      tree = Some refined ->
    phase1_surface_guard_refined_boundary_typed_transfer_nonreference_session_spine_tree
      refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold
    phase1_surface_normalize_guard_refined_boundary_typed_transfer_nonreference_session_tree
    in Hnormalize.
  destruct
    (phase1_surface_normalize_boundary_refined_typed_transfer_nonreference_session_tree
      tree)
    as [session |] eqn:Hsession; try discriminate Hnormalize.
  transitivity
    (phase1_surface_boundary_refined_typed_transfer_nonreference_session_spine_tree
      session).
  - eapply
      phase1_surface_normalize_guard_refined_boundary_typed_transfer_nonreference_session_spine_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_boundary_refined_typed_transfer_nonreference_session_tree_round_trip.
    exact Hsession.
Qed.

Inductive Phase1SurfaceGuardRefinedBoundaryTypedTransferSessionSpine : Type :=
| Phase1GuardRefinedBoundaryTypedTransferNonreferenceSession
    (session :
      Phase1SurfaceGuardRefinedBoundaryTypedTransferNonreferenceSessionSpine)
| Phase1GuardRefinedBoundaryTypedTransferStaticReferenceSession
    (reference_tree : ParseTree).

Definition phase1_surface_guard_refined_boundary_typed_transfer_session_spine_tree
  (session : Phase1SurfaceGuardRefinedBoundaryTypedTransferSessionSpine)
  : ParseTree :=
  match session with
  | Phase1GuardRefinedBoundaryTypedTransferNonreferenceSession nonreference =>
      PTNonterminal "session_expression"
        (PTAlternative 0
          (phase1_surface_guard_refined_boundary_typed_transfer_nonreference_session_spine_tree
            nonreference))
  | Phase1GuardRefinedBoundaryTypedTransferStaticReferenceSession reference_tree =>
      PTNonterminal "session_expression"
        (PTAlternative 1 reference_tree)
  end.

Definition phase1_surface_normalize_guard_refined_boundary_typed_transfer_session_spine
  (session : Phase1SurfaceBoundaryRefinedTypedTransferSessionSpine)
  : option Phase1SurfaceGuardRefinedBoundaryTypedTransferSessionSpine :=
  match session with
  | Phase1BoundaryRefinedTypedTransferNonreferenceSession nonreference =>
      match
        phase1_surface_normalize_guard_refined_boundary_typed_transfer_nonreference_session_spine
          nonreference
      with
      | Some refined =>
          Some
            (Phase1GuardRefinedBoundaryTypedTransferNonreferenceSession refined)
      | None => None
      end
  | Phase1BoundaryRefinedTypedTransferStaticReferenceSession reference_tree =>
      Some
        (Phase1GuardRefinedBoundaryTypedTransferStaticReferenceSession
          reference_tree)
  end.

Theorem
  phase1_surface_normalize_guard_refined_boundary_typed_transfer_session_spine_round_trip :
  forall session refined,
    phase1_surface_normalize_guard_refined_boundary_typed_transfer_session_spine
      session = Some refined ->
    phase1_surface_guard_refined_boundary_typed_transfer_session_spine_tree
      refined =
    phase1_surface_boundary_refined_typed_transfer_session_spine_tree session.
Proof.
  intros [nonreference | reference_tree] refined Hnormalize.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_guard_refined_boundary_typed_transfer_nonreference_session_spine
        nonreference)
      as [actual |] eqn:Hnonreference; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_guard_refined_boundary_typed_transfer_nonreference_session_spine_round_trip
        nonreference actual Hnonreference).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Definition phase1_surface_normalize_guard_refined_boundary_typed_transfer_session_tree
  (tree : ParseTree)
  : option Phase1SurfaceGuardRefinedBoundaryTypedTransferSessionSpine :=
  match phase1_surface_normalize_boundary_refined_typed_transfer_session_tree tree with
  | Some session =>
      phase1_surface_normalize_guard_refined_boundary_typed_transfer_session_spine
        session
  | None => None
  end.

Theorem
  phase1_surface_normalize_guard_refined_boundary_typed_transfer_session_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_guard_refined_boundary_typed_transfer_session_tree tree =
      Some refined ->
    phase1_surface_guard_refined_boundary_typed_transfer_session_spine_tree refined =
      tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_guard_refined_boundary_typed_transfer_session_tree
    in Hnormalize.
  destruct (phase1_surface_normalize_boundary_refined_typed_transfer_session_tree tree)
    as [session |] eqn:Hsession; try discriminate Hnormalize.
  transitivity
    (phase1_surface_boundary_refined_typed_transfer_session_spine_tree session).
  - eapply
      phase1_surface_normalize_guard_refined_boundary_typed_transfer_session_spine_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_boundary_refined_typed_transfer_session_tree_round_trip.
    exact Hsession.
Qed.
