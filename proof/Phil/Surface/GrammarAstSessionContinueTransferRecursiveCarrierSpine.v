From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionEndRecursiveCarrierSpine
  GrammarAstSessionRecursionPayloadSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Propagate the now-closed `continue identifier` payload through send/receive
  continuation chains only.

  Select/offer choices remain values of the already-closed end-refined
  recursive choice carrier, so branch-continuation propagation is deliberately
  deferred.  The recursive payload likewise remains an exact certified tree.
*)

Inductive Phase1SurfaceContinueTransferRecursiveSessionSpine : Type :=
| Phase1ContinueTransferRecursiveNonreferenceSession
    (session : Phase1SurfaceContinueTransferRecursiveNonreferenceSessionSpine)
| Phase1ContinueTransferRecursiveStaticReferenceSession
    (reference_tree : ParseTree)

with Phase1SurfaceContinueTransferRecursiveNonreferenceSessionSpine : Type :=
| Phase1ContinueTransferRecursiveTransferSession
    (direction : Phase1SurfaceSessionTransferDirection)
    (parameter : Phase1SurfaceTermParamTypeSpine)
    (boundary : option Phase1SurfaceStaticTypeArgumentsReferenceSpine)
    (guard : option Phase1SurfacePropositionSpine)
    (continuation : Phase1SurfaceContinueTransferRecursiveSessionSpine)
| Phase1ContinueTransferRecursiveSelectSession
    (choice : Phase1SurfaceEndRefinedRecursiveSessionChoiceSpine)
| Phase1ContinueTransferRecursiveOfferSession
    (choice : Phase1SurfaceEndRefinedRecursiveSessionChoiceSpine)
| Phase1ContinueTransferRecursiveEndSession
    (terminal : Phase1SurfaceEndSessionSpine)
| Phase1ContinueTransferRecursiveRecursiveSession
    (selected_tree : ParseTree)
| Phase1ContinueTransferRecursiveContinueSession
    (payload : Phase1SurfaceContinueSessionPayloadSpine).

Fixpoint phase1_surface_continue_transfer_recursive_session_spine_tree
  (session : Phase1SurfaceContinueTransferRecursiveSessionSpine) : ParseTree :=
  match session with
  | Phase1ContinueTransferRecursiveNonreferenceSession nonreference =>
      PTNonterminal "session_expression"
        (PTAlternative 0
          (phase1_surface_continue_transfer_recursive_nonreference_session_spine_tree
            nonreference))
  | Phase1ContinueTransferRecursiveStaticReferenceSession reference_tree =>
      PTNonterminal "session_expression" (PTAlternative 1 reference_tree)
  end

with phase1_surface_continue_transfer_recursive_nonreference_session_spine_tree
  (session : Phase1SurfaceContinueTransferRecursiveNonreferenceSessionSpine)
  : ParseTree :=
  match session with
  | Phase1ContinueTransferRecursiveTransferSession
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
              phase1_surface_continue_transfer_recursive_session_spine_tree continuation
            ]))
  | Phase1ContinueTransferRecursiveSelectSession choice =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 2
          (phase1_surface_end_refined_recursive_session_choice_spine_tree choice))
  | Phase1ContinueTransferRecursiveOfferSession choice =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 3
          (phase1_surface_end_refined_recursive_session_choice_spine_tree choice))
  | Phase1ContinueTransferRecursiveEndSession terminal =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 4 (phase1_surface_end_session_spine_tree terminal))
  | Phase1ContinueTransferRecursiveRecursiveSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 5 selected_tree)
  | Phase1ContinueTransferRecursiveContinueSession payload =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 6
          (phase1_surface_continue_session_payload_spine_tree payload))
  end.

Fixpoint phase1_surface_normalize_continue_transfer_recursive_session_spine
  (session : Phase1SurfaceEndRefinedRecursiveSessionSpine)
  : option Phase1SurfaceContinueTransferRecursiveSessionSpine :=
  match session with
  | Phase1EndRefinedRecursiveNonreferenceSession nonreference =>
      match
        phase1_surface_normalize_continue_transfer_recursive_nonreference_session_spine
          nonreference
      with
      | Some refined =>
          Some (Phase1ContinueTransferRecursiveNonreferenceSession refined)
      | None => None
      end
  | Phase1EndRefinedRecursiveStaticReferenceSession reference_tree =>
      Some (Phase1ContinueTransferRecursiveStaticReferenceSession reference_tree)
  end

with phase1_surface_normalize_continue_transfer_recursive_nonreference_session_spine
  (session : Phase1SurfaceEndRefinedRecursiveNonreferenceSessionSpine)
  : option Phase1SurfaceContinueTransferRecursiveNonreferenceSessionSpine :=
  match session with
  | Phase1EndRefinedRecursiveTransferSession
      direction parameter boundary guard continuation =>
      match phase1_surface_normalize_continue_transfer_recursive_session_spine continuation with
      | Some refined_continuation =>
          Some
            (Phase1ContinueTransferRecursiveTransferSession
              direction parameter boundary guard refined_continuation)
      | None => None
      end
  | Phase1EndRefinedRecursiveSelectSession choice =>
      Some (Phase1ContinueTransferRecursiveSelectSession choice)
  | Phase1EndRefinedRecursiveOfferSession choice =>
      Some (Phase1ContinueTransferRecursiveOfferSession choice)
  | Phase1EndRefinedRecursiveEndSession terminal =>
      Some (Phase1ContinueTransferRecursiveEndSession terminal)
  | Phase1EndRefinedRecursiveRecursiveSession selected_tree =>
      Some (Phase1ContinueTransferRecursiveRecursiveSession selected_tree)
  | Phase1EndRefinedRecursiveContinueSession selected_tree =>
      match phase1_surface_normalize_continue_session_payload_spine selected_tree with
      | Some payload =>
          Some (Phase1ContinueTransferRecursiveContinueSession payload)
      | None => None
      end
  end.

Theorem
  phase1_surface_normalize_continue_transfer_recursive_session_spine_round_trip :
  forall session refined,
    phase1_surface_normalize_continue_transfer_recursive_session_spine session =
      Some refined ->
    phase1_surface_continue_transfer_recursive_session_spine_tree refined =
      phase1_surface_end_refined_recursive_session_spine_tree session.
Proof.
  fix IH 1.
  intros session refined Hnormalize.
  destruct session as [nonreference | reference_tree].
  - destruct nonreference as
      [direction parameter boundary guard continuation
      |choice
      |choice
      |terminal
      |selected_tree
      |selected_tree].
    + cbn in Hnormalize.
      destruct
        (phase1_surface_normalize_continue_transfer_recursive_session_spine continuation)
        as [refined_continuation |] eqn:Hcontinuation;
        try discriminate Hnormalize.
      inversion Hnormalize; subst refined.
      cbn.
      rewrite (IH continuation refined_continuation Hcontinuation).
      reflexivity.
    + inversion Hnormalize; subst refined. reflexivity.
    + inversion Hnormalize; subst refined. reflexivity.
    + inversion Hnormalize; subst refined. reflexivity.
    + inversion Hnormalize; subst refined. reflexivity.
    + cbn in Hnormalize.
      destruct (phase1_surface_normalize_continue_session_payload_spine selected_tree)
        as [payload |] eqn:Hpayload; try discriminate Hnormalize.
      inversion Hnormalize; subst refined.
      cbn.
      rewrite
        (phase1_surface_normalize_continue_session_payload_spine_round_trip
          selected_tree payload Hpayload).
      reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.
