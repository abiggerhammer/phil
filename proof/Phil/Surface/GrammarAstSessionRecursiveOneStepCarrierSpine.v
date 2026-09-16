From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionContinueMutualRecursiveClosureSpine
  GrammarAstSessionRecursionPayloadSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Refine `recursive identifier = session_expression` at the current
  nonreference-session node without yet traversing the recursive body.

  Transfer and choice continuations remain values of the already-closed
  continue-refined mutual recursive carrier.  The recursive body itself remains
  an exact certified `session_expression` tree inside
  Phase1SurfaceRecursiveSessionPayloadSpine.  This is deliberately a one-step
  composition layer; recursive-body traversal remains a successor.
*)

Inductive Phase1SurfaceRecursiveOneStepNonreferenceSessionSpine : Type :=
| Phase1RecursiveOneStepTransferSession
    (direction : Phase1SurfaceSessionTransferDirection)
    (parameter : Phase1SurfaceTermParamTypeSpine)
    (boundary : option Phase1SurfaceStaticTypeArgumentsReferenceSpine)
    (guard : option Phase1SurfacePropositionSpine)
    (continuation : Phase1SurfaceContinueMutualRecursiveSessionSpine)
| Phase1RecursiveOneStepSelectSession
    (choice : Phase1SurfaceContinueMutualRecursiveSessionChoiceSpine)
| Phase1RecursiveOneStepOfferSession
    (choice : Phase1SurfaceContinueMutualRecursiveSessionChoiceSpine)
| Phase1RecursiveOneStepEndSession
    (terminal : Phase1SurfaceEndSessionSpine)
| Phase1RecursiveOneStepRecursiveSession
    (payload : Phase1SurfaceRecursiveSessionPayloadSpine)
| Phase1RecursiveOneStepContinueSession
    (payload : Phase1SurfaceContinueSessionPayloadSpine).

Inductive Phase1SurfaceRecursiveOneStepSessionSpine : Type :=
| Phase1RecursiveOneStepNonreferenceSession
    (session : Phase1SurfaceRecursiveOneStepNonreferenceSessionSpine)
| Phase1RecursiveOneStepStaticReferenceSession
    (reference_tree : ParseTree).

Definition phase1_surface_recursive_one_step_nonreference_session_spine_tree
  (session : Phase1SurfaceRecursiveOneStepNonreferenceSessionSpine) : ParseTree :=
  match session with
  | Phase1RecursiveOneStepTransferSession
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
              phase1_surface_continue_mutual_recursive_session_spine_tree continuation
            ]))
  | Phase1RecursiveOneStepSelectSession choice =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 2
          (phase1_surface_continue_mutual_recursive_session_choice_spine_tree choice))
  | Phase1RecursiveOneStepOfferSession choice =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 3
          (phase1_surface_continue_mutual_recursive_session_choice_spine_tree choice))
  | Phase1RecursiveOneStepEndSession terminal =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 4 (phase1_surface_end_session_spine_tree terminal))
  | Phase1RecursiveOneStepRecursiveSession payload =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 5
          (phase1_surface_recursive_session_payload_spine_tree payload))
  | Phase1RecursiveOneStepContinueSession payload =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 6
          (phase1_surface_continue_session_payload_spine_tree payload))
  end.

Definition phase1_surface_recursive_one_step_session_spine_tree
  (session : Phase1SurfaceRecursiveOneStepSessionSpine) : ParseTree :=
  match session with
  | Phase1RecursiveOneStepNonreferenceSession nonreference =>
      PTNonterminal "session_expression"
        (PTAlternative 0
          (phase1_surface_recursive_one_step_nonreference_session_spine_tree
            nonreference))
  | Phase1RecursiveOneStepStaticReferenceSession reference_tree =>
      PTNonterminal "session_expression" (PTAlternative 1 reference_tree)
  end.

Definition phase1_surface_normalize_recursive_one_step_nonreference_session_spine
  (session : Phase1SurfaceContinueMutualRecursiveNonreferenceSessionSpine)
  : option Phase1SurfaceRecursiveOneStepNonreferenceSessionSpine :=
  match session with
  | Phase1ContinueMutualRecursiveTransferSession
      direction parameter boundary guard continuation =>
      Some
        (Phase1RecursiveOneStepTransferSession
          direction parameter boundary guard continuation)
  | Phase1ContinueMutualRecursiveSelectSession choice =>
      Some (Phase1RecursiveOneStepSelectSession choice)
  | Phase1ContinueMutualRecursiveOfferSession choice =>
      Some (Phase1RecursiveOneStepOfferSession choice)
  | Phase1ContinueMutualRecursiveEndSession terminal =>
      Some (Phase1RecursiveOneStepEndSession terminal)
  | Phase1ContinueMutualRecursiveRecursiveSession selected_tree =>
      match phase1_surface_normalize_recursive_session_payload_spine selected_tree with
      | Some payload => Some (Phase1RecursiveOneStepRecursiveSession payload)
      | None => None
      end
  | Phase1ContinueMutualRecursiveContinueSession payload =>
      Some (Phase1RecursiveOneStepContinueSession payload)
  end.

Theorem
  phase1_surface_normalize_recursive_one_step_nonreference_session_spine_round_trip :
  forall session refined,
    phase1_surface_normalize_recursive_one_step_nonreference_session_spine session =
      Some refined ->
    phase1_surface_recursive_one_step_nonreference_session_spine_tree refined =
      phase1_surface_continue_mutual_recursive_nonreference_session_spine_tree session.
Proof.
  intros session refined Hnormalize.
  destruct session as
    [direction parameter boundary guard continuation
    |choice
    |choice
    |terminal
    |selected_tree
    |payload].
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_recursive_session_payload_spine selected_tree)
      as [recursive_payload |] eqn:Hpayload; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_recursive_session_payload_spine_round_trip
        selected_tree recursive_payload Hpayload).
    reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
Qed.

Definition phase1_surface_normalize_recursive_one_step_session_spine
  (session : Phase1SurfaceContinueMutualRecursiveSessionSpine)
  : option Phase1SurfaceRecursiveOneStepSessionSpine :=
  match session with
  | Phase1ContinueMutualRecursiveNonreferenceSession nonreference =>
      match
        phase1_surface_normalize_recursive_one_step_nonreference_session_spine
          nonreference
      with
      | Some refined => Some (Phase1RecursiveOneStepNonreferenceSession refined)
      | None => None
      end
  | Phase1ContinueMutualRecursiveStaticReferenceSession reference_tree =>
      Some (Phase1RecursiveOneStepStaticReferenceSession reference_tree)
  end.

Theorem phase1_surface_normalize_recursive_one_step_session_spine_round_trip :
  forall session refined,
    phase1_surface_normalize_recursive_one_step_session_spine session =
      Some refined ->
    phase1_surface_recursive_one_step_session_spine_tree refined =
      phase1_surface_continue_mutual_recursive_session_spine_tree session.
Proof.
  intros [nonreference | reference_tree] refined Hnormalize.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_recursive_one_step_nonreference_session_spine
        nonreference)
      as [actual |] eqn:Hnonreference; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_recursive_one_step_nonreference_session_spine_round_trip
        nonreference actual Hnonreference).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.
