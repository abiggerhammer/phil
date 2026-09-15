From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionBranchContinuationCarrierSpine
  GrammarAstSessionTransferRecursiveClosureSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Lift the now-closed select/offer branch carrier into the recursively closed
  send/receive session carrier.

  This is deliberately a one-step composition layer: branch continuations keep
  the established Phase1SurfaceRecursiveTransferSessionSpine value from #1060,
  while an enclosing select/offer payload is no longer opaque.  A successor can
  close the mutual transfer/choice recursion explicitly rather than hiding that
  change inside this carrier.
*)

Inductive Phase1SurfaceChoiceRefinedRecursiveNonreferenceSessionSpine : Type :=
| Phase1ChoiceRefinedRecursiveTransferSession
    (direction : Phase1SurfaceSessionTransferDirection)
    (parameter : Phase1SurfaceTermParamTypeSpine)
    (boundary : option Phase1SurfaceStaticTypeArgumentsReferenceSpine)
    (guard : option Phase1SurfacePropositionSpine)
    (continuation : Phase1SurfaceRecursiveTransferSessionSpine)
| Phase1ChoiceRefinedRecursiveSelectSession
    (choice : Phase1SurfaceContinuationRefinedSessionChoiceSpine)
| Phase1ChoiceRefinedRecursiveOfferSession
    (choice : Phase1SurfaceContinuationRefinedSessionChoiceSpine)
| Phase1ChoiceRefinedRecursiveEndSession
    (selected_tree : ParseTree)
| Phase1ChoiceRefinedRecursiveRecursiveSession
    (selected_tree : ParseTree)
| Phase1ChoiceRefinedRecursiveContinueSession
    (selected_tree : ParseTree).

Inductive Phase1SurfaceChoiceRefinedRecursiveSessionSpine : Type :=
| Phase1ChoiceRefinedRecursiveNonreferenceSession
    (session : Phase1SurfaceChoiceRefinedRecursiveNonreferenceSessionSpine)
| Phase1ChoiceRefinedRecursiveStaticReferenceSession
    (reference_tree : ParseTree).

Definition
  phase1_surface_choice_refined_recursive_nonreference_session_spine_tree
  (session : Phase1SurfaceChoiceRefinedRecursiveNonreferenceSessionSpine)
  : ParseTree :=
  match session with
  | Phase1ChoiceRefinedRecursiveTransferSession
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
              phase1_surface_recursive_transfer_session_spine_tree continuation
            ]))
  | Phase1ChoiceRefinedRecursiveSelectSession choice =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 2
          (phase1_surface_continuation_refined_session_choice_spine_tree choice))
  | Phase1ChoiceRefinedRecursiveOfferSession choice =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 3
          (phase1_surface_continuation_refined_session_choice_spine_tree choice))
  | Phase1ChoiceRefinedRecursiveEndSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 4 selected_tree)
  | Phase1ChoiceRefinedRecursiveRecursiveSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 5 selected_tree)
  | Phase1ChoiceRefinedRecursiveContinueSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 6 selected_tree)
  end.

Definition phase1_surface_choice_refined_recursive_session_spine_tree
  (session : Phase1SurfaceChoiceRefinedRecursiveSessionSpine) : ParseTree :=
  match session with
  | Phase1ChoiceRefinedRecursiveNonreferenceSession nonreference =>
      PTNonterminal "session_expression"
        (PTAlternative 0
          (phase1_surface_choice_refined_recursive_nonreference_session_spine_tree
            nonreference))
  | Phase1ChoiceRefinedRecursiveStaticReferenceSession reference_tree =>
      PTNonterminal "session_expression"
        (PTAlternative 1 reference_tree)
  end.

Definition
  phase1_surface_normalize_choice_refined_recursive_nonreference_session_spine_fuel
  (fuel : nat)
  (session : Phase1SurfaceRecursiveTransferNonreferenceSessionSpine)
  : option Phase1SurfaceChoiceRefinedRecursiveNonreferenceSessionSpine :=
  match session with
  | Phase1RecursiveTransferPayloadSession
      direction parameter boundary guard continuation =>
      Some
        (Phase1ChoiceRefinedRecursiveTransferSession
          direction parameter boundary guard continuation)
  | Phase1RecursiveTransferOpaqueSelectSession selected_tree =>
      match
        phase1_surface_normalize_continuation_refined_session_choice_tree_fuel
          fuel Phase1SessionSelect selected_tree
      with
      | Some choice =>
          Some (Phase1ChoiceRefinedRecursiveSelectSession choice)
      | None => None
      end
  | Phase1RecursiveTransferOpaqueOfferSession selected_tree =>
      match
        phase1_surface_normalize_continuation_refined_session_choice_tree_fuel
          fuel Phase1SessionOffer selected_tree
      with
      | Some choice =>
          Some (Phase1ChoiceRefinedRecursiveOfferSession choice)
      | None => None
      end
  | Phase1RecursiveTransferOpaqueEndSession selected_tree =>
      Some (Phase1ChoiceRefinedRecursiveEndSession selected_tree)
  | Phase1RecursiveTransferOpaqueRecursiveSession selected_tree =>
      Some (Phase1ChoiceRefinedRecursiveRecursiveSession selected_tree)
  | Phase1RecursiveTransferOpaqueContinueSession selected_tree =>
      Some (Phase1ChoiceRefinedRecursiveContinueSession selected_tree)
  end.

Theorem
  phase1_surface_normalize_choice_refined_recursive_nonreference_session_spine_fuel_round_trip :
  forall fuel session refined,
    phase1_surface_normalize_choice_refined_recursive_nonreference_session_spine_fuel
      fuel session = Some refined ->
    phase1_surface_choice_refined_recursive_nonreference_session_spine_tree
      refined =
    phase1_surface_recursive_transfer_nonreference_session_spine_tree session.
Proof.
  intros fuel session refined Hnormalize.
  destruct session as
    [direction parameter boundary guard continuation
    |selected_tree
    |selected_tree
    |selected_tree
    |selected_tree
    |selected_tree].
  - inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_continuation_refined_session_choice_tree_fuel
        fuel Phase1SessionSelect selected_tree)
      as [choice |] eqn:Hchoice; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_continuation_refined_session_choice_tree_fuel_round_trip
        fuel Phase1SessionSelect selected_tree choice Hchoice).
    reflexivity.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_continuation_refined_session_choice_tree_fuel
        fuel Phase1SessionOffer selected_tree)
      as [choice |] eqn:Hchoice; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_continuation_refined_session_choice_tree_fuel_round_trip
        fuel Phase1SessionOffer selected_tree choice Hchoice).
    reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
Qed.

Definition phase1_surface_normalize_choice_refined_recursive_session_spine_fuel
  (fuel : nat)
  (session : Phase1SurfaceRecursiveTransferSessionSpine)
  : option Phase1SurfaceChoiceRefinedRecursiveSessionSpine :=
  match session with
  | Phase1RecursiveTransferNonreferenceSession nonreference =>
      match
        phase1_surface_normalize_choice_refined_recursive_nonreference_session_spine_fuel
          fuel nonreference
      with
      | Some refined =>
          Some (Phase1ChoiceRefinedRecursiveNonreferenceSession refined)
      | None => None
      end
  | Phase1RecursiveTransferStaticReferenceSession reference_tree =>
      Some (Phase1ChoiceRefinedRecursiveStaticReferenceSession reference_tree)
  end.

Theorem
  phase1_surface_normalize_choice_refined_recursive_session_spine_fuel_round_trip :
  forall fuel session refined,
    phase1_surface_normalize_choice_refined_recursive_session_spine_fuel
      fuel session = Some refined ->
    phase1_surface_choice_refined_recursive_session_spine_tree refined =
      phase1_surface_recursive_transfer_session_spine_tree session.
Proof.
  intros fuel [nonreference | reference_tree] refined Hnormalize.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_choice_refined_recursive_nonreference_session_spine_fuel
        fuel nonreference)
      as [actual |] eqn:Hnonreference; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_choice_refined_recursive_nonreference_session_spine_fuel_round_trip
        fuel nonreference actual Hnonreference).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Definition phase1_surface_normalize_choice_refined_recursive_session_tree_fuel
  (fuel : nat)
  (tree : ParseTree)
  : option Phase1SurfaceChoiceRefinedRecursiveSessionSpine :=
  match phase1_surface_normalize_recursive_transfer_session_tree_fuel fuel tree with
  | Some session =>
      phase1_surface_normalize_choice_refined_recursive_session_spine_fuel
        fuel session
  | None => None
  end.

Theorem
  phase1_surface_normalize_choice_refined_recursive_session_tree_fuel_round_trip :
  forall fuel tree refined,
    phase1_surface_normalize_choice_refined_recursive_session_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_choice_refined_recursive_session_spine_tree refined = tree.
Proof.
  intros fuel tree refined Hnormalize.
  unfold phase1_surface_normalize_choice_refined_recursive_session_tree_fuel
    in Hnormalize.
  destruct
    (phase1_surface_normalize_recursive_transfer_session_tree_fuel fuel tree)
    as [session |] eqn:Hsession; try discriminate Hnormalize.
  transitivity (phase1_surface_recursive_transfer_session_spine_tree session).
  - eapply
      phase1_surface_normalize_choice_refined_recursive_session_spine_fuel_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_recursive_transfer_session_tree_fuel_round_trip.
    exact Hsession.
Qed.
