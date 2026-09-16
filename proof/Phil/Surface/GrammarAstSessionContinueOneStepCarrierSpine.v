From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionEndRecursiveCarrierSpine
  GrammarAstSessionRecursionPayloadSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Refine the `continue identifier` payload at the current nonreference-session
  node without yet propagating that refinement through recursive children.

  Transfer continuations and select/offer branches remain values of the already
  closed end-refined recursive carrier.  The recursive payload remains an exact
  certified tree.  This is deliberately a one-step composition layer; a later
  slice can close transitive propagation explicitly.
*)

Inductive Phase1SurfaceContinueRefinedEndRecursiveNonreferenceSessionSpine : Type :=
| Phase1ContinueRefinedEndRecursiveTransferSession
    (direction : Phase1SurfaceSessionTransferDirection)
    (parameter : Phase1SurfaceTermParamTypeSpine)
    (boundary : option Phase1SurfaceStaticTypeArgumentsReferenceSpine)
    (guard : option Phase1SurfacePropositionSpine)
    (continuation : Phase1SurfaceEndRefinedRecursiveSessionSpine)
| Phase1ContinueRefinedEndRecursiveSelectSession
    (choice : Phase1SurfaceEndRefinedRecursiveSessionChoiceSpine)
| Phase1ContinueRefinedEndRecursiveOfferSession
    (choice : Phase1SurfaceEndRefinedRecursiveSessionChoiceSpine)
| Phase1ContinueRefinedEndRecursiveEndSession
    (terminal : Phase1SurfaceEndSessionSpine)
| Phase1ContinueRefinedEndRecursiveRecursiveSession
    (selected_tree : ParseTree)
| Phase1ContinueRefinedEndRecursiveContinueSession
    (payload : Phase1SurfaceContinueSessionPayloadSpine).

Inductive Phase1SurfaceContinueRefinedEndRecursiveSessionSpine : Type :=
| Phase1ContinueRefinedEndRecursiveNonreferenceSession
    (session : Phase1SurfaceContinueRefinedEndRecursiveNonreferenceSessionSpine)
| Phase1ContinueRefinedEndRecursiveStaticReferenceSession
    (reference_tree : ParseTree).

Definition
  phase1_surface_continue_refined_end_recursive_nonreference_session_spine_tree
  (session : Phase1SurfaceContinueRefinedEndRecursiveNonreferenceSessionSpine)
  : ParseTree :=
  match session with
  | Phase1ContinueRefinedEndRecursiveTransferSession
      direction parameter boundary guard continuation =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative
          (phase1_surface_session_transfer_index direction)
          (PTSequence
            [ PTLiteral (phase1_surface_session_transfer_keyword direction);
              PTLiteral "(";
              phase1_surface_term_param_type_spine_tree parameter;
              PTLiteral ")";
              phase1_surface_boundary_refined_annotation_tree boundary;
              phase1_surface_guard_refined_annotation_tree guard;
              PTLiteral "then";
              phase1_surface_end_refined_recursive_session_spine_tree continuation
            ]))
  | Phase1ContinueRefinedEndRecursiveSelectSession choice =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 2
          (phase1_surface_end_refined_recursive_session_choice_spine_tree choice))
  | Phase1ContinueRefinedEndRecursiveOfferSession choice =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 3
          (phase1_surface_end_refined_recursive_session_choice_spine_tree choice))
  | Phase1ContinueRefinedEndRecursiveEndSession terminal =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 4 (phase1_surface_end_session_spine_tree terminal))
  | Phase1ContinueRefinedEndRecursiveRecursiveSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 5 selected_tree)
  | Phase1ContinueRefinedEndRecursiveContinueSession payload =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 6
          (phase1_surface_continue_session_payload_spine_tree payload))
  end.

Definition phase1_surface_continue_refined_end_recursive_session_spine_tree
  (session : Phase1SurfaceContinueRefinedEndRecursiveSessionSpine) : ParseTree :=
  match session with
  | Phase1ContinueRefinedEndRecursiveNonreferenceSession nonreference =>
      PTNonterminal "session_expression"
        (PTAlternative 0
          (phase1_surface_continue_refined_end_recursive_nonreference_session_spine_tree
            nonreference))
  | Phase1ContinueRefinedEndRecursiveStaticReferenceSession reference_tree =>
      PTNonterminal "session_expression" (PTAlternative 1 reference_tree)
  end.

Definition
  phase1_surface_normalize_continue_refined_end_recursive_nonreference_session_spine
  (session : Phase1SurfaceEndRefinedRecursiveNonreferenceSessionSpine)
  : option Phase1SurfaceContinueRefinedEndRecursiveNonreferenceSessionSpine :=
  match session with
  | Phase1EndRefinedRecursiveTransferSession
      direction parameter boundary guard continuation =>
      Some
        (Phase1ContinueRefinedEndRecursiveTransferSession
          direction parameter boundary guard continuation)
  | Phase1EndRefinedRecursiveSelectSession choice =>
      Some (Phase1ContinueRefinedEndRecursiveSelectSession choice)
  | Phase1EndRefinedRecursiveOfferSession choice =>
      Some (Phase1ContinueRefinedEndRecursiveOfferSession choice)
  | Phase1EndRefinedRecursiveEndSession terminal =>
      Some (Phase1ContinueRefinedEndRecursiveEndSession terminal)
  | Phase1EndRefinedRecursiveRecursiveSession selected_tree =>
      Some (Phase1ContinueRefinedEndRecursiveRecursiveSession selected_tree)
  | Phase1EndRefinedRecursiveContinueSession selected_tree =>
      match phase1_surface_normalize_continue_session_payload_spine selected_tree with
      | Some payload =>
          Some (Phase1ContinueRefinedEndRecursiveContinueSession payload)
      | None => None
      end
  end.

Theorem
  phase1_surface_normalize_continue_refined_end_recursive_nonreference_session_spine_round_trip :
  forall session refined,
    phase1_surface_normalize_continue_refined_end_recursive_nonreference_session_spine
      session = Some refined ->
    phase1_surface_continue_refined_end_recursive_nonreference_session_spine_tree
      refined =
    phase1_surface_end_refined_recursive_nonreference_session_spine_tree session.
Proof.
  intros session refined Hnormalize.
  destruct session as
    [direction parameter boundary guard continuation
    |choice
    |choice
    |terminal
    |selected_tree
    |selected_tree].
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_continue_session_payload_spine selected_tree)
      as [payload |] eqn:Hpayload; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_continue_session_payload_spine_round_trip
        selected_tree payload Hpayload).
    reflexivity.
Qed.

Definition phase1_surface_normalize_continue_refined_end_recursive_session_spine
  (session : Phase1SurfaceEndRefinedRecursiveSessionSpine)
  : option Phase1SurfaceContinueRefinedEndRecursiveSessionSpine :=
  match session with
  | Phase1EndRefinedRecursiveNonreferenceSession nonreference =>
      match
        phase1_surface_normalize_continue_refined_end_recursive_nonreference_session_spine
          nonreference
      with
      | Some refined =>
          Some (Phase1ContinueRefinedEndRecursiveNonreferenceSession refined)
      | None => None
      end
  | Phase1EndRefinedRecursiveStaticReferenceSession reference_tree =>
      Some (Phase1ContinueRefinedEndRecursiveStaticReferenceSession reference_tree)
  end.

Theorem
  phase1_surface_normalize_continue_refined_end_recursive_session_spine_round_trip :
  forall session refined,
    phase1_surface_normalize_continue_refined_end_recursive_session_spine session =
      Some refined ->
    phase1_surface_continue_refined_end_recursive_session_spine_tree refined =
      phase1_surface_end_refined_recursive_session_spine_tree session.
Proof.
  intros [nonreference | reference_tree] refined Hnormalize.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_continue_refined_end_recursive_nonreference_session_spine
        nonreference)
      as [actual |] eqn:Hnonreference; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_continue_refined_end_recursive_nonreference_session_spine_round_trip
        nonreference actual Hnonreference).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.
