From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionTransferContinuationCarrierSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Transitive send/receive continuation carrier for
  PHIL-SURFACE-GRAMMAR-CORR-001.

  The one-step continuation carrier from #1023 normalizes exactly one
  `then session_expression` child.  This layer closes that continuation chain
  transitively with explicit fuel.  Fuel decreases only when following a
  send/receive continuation; non-transfer session alternatives remain at their
  current exact certified boundaries.
*)

Inductive Phase1SurfaceRecursiveTransferSessionSpine : Type :=
| Phase1RecursiveTransferNonreferenceSession
    (session : Phase1SurfaceRecursiveTransferNonreferenceSessionSpine)
| Phase1RecursiveTransferStaticReferenceSession
    (reference_tree : ParseTree)

with Phase1SurfaceRecursiveTransferNonreferenceSessionSpine : Type :=
| Phase1RecursiveTransferPayloadSession
    (direction : Phase1SurfaceSessionTransferDirection)
    (parameter : Phase1SurfaceTermParamTypeSpine)
    (boundary : option Phase1SurfaceStaticTypeArgumentsReferenceSpine)
    (guard : option Phase1SurfacePropositionSpine)
    (continuation : Phase1SurfaceRecursiveTransferSessionSpine)
| Phase1RecursiveTransferOpaqueSelectSession
    (selected_tree : ParseTree)
| Phase1RecursiveTransferOpaqueOfferSession
    (selected_tree : ParseTree)
| Phase1RecursiveTransferOpaqueEndSession
    (selected_tree : ParseTree)
| Phase1RecursiveTransferOpaqueRecursiveSession
    (selected_tree : ParseTree)
| Phase1RecursiveTransferOpaqueContinueSession
    (selected_tree : ParseTree).

Fixpoint phase1_surface_recursive_transfer_session_spine_tree
  (session : Phase1SurfaceRecursiveTransferSessionSpine) : ParseTree :=
  match session with
  | Phase1RecursiveTransferNonreferenceSession nonreference =>
      PTNonterminal "session_expression"
        (PTAlternative 0
          (phase1_surface_recursive_transfer_nonreference_session_spine_tree
            nonreference))
  | Phase1RecursiveTransferStaticReferenceSession reference_tree =>
      PTNonterminal "session_expression"
        (PTAlternative 1 reference_tree)
  end

with phase1_surface_recursive_transfer_nonreference_session_spine_tree
  (session : Phase1SurfaceRecursiveTransferNonreferenceSessionSpine)
  : ParseTree :=
  match session with
  | Phase1RecursiveTransferPayloadSession
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
  | Phase1RecursiveTransferOpaqueSelectSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 2 selected_tree)
  | Phase1RecursiveTransferOpaqueOfferSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 3 selected_tree)
  | Phase1RecursiveTransferOpaqueEndSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 4 selected_tree)
  | Phase1RecursiveTransferOpaqueRecursiveSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 5 selected_tree)
  | Phase1RecursiveTransferOpaqueContinueSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 6 selected_tree)
  end.

Fixpoint phase1_surface_normalize_recursive_transfer_session_spine_fuel
  (fuel : nat)
  (session : Phase1SurfaceGuardRefinedBoundaryTypedTransferSessionSpine)
  : option Phase1SurfaceRecursiveTransferSessionSpine :=
  match fuel with
  | 0 => None
  | S remaining =>
      match
        phase1_surface_normalize_continuation_refined_transfer_session_spine
          session
      with
      | Some step =>
          match step with
          | Phase1ContinuationRefinedTransferStaticReferenceSession
              reference_tree =>
              Some
                (Phase1RecursiveTransferStaticReferenceSession reference_tree)
          | Phase1ContinuationRefinedTransferNonreferenceSession nonreference =>
              match nonreference with
              | Phase1ContinuationRefinedTransferSession transfer =>
                  match
                    phase1_surface_normalize_recursive_transfer_session_spine_fuel
                      remaining
                      (phase1_continuation_refined_transfer_continuation transfer)
                  with
                  | Some continuation =>
                      Some
                        (Phase1RecursiveTransferNonreferenceSession
                          (Phase1RecursiveTransferPayloadSession
                            (phase1_continuation_refined_transfer_direction transfer)
                            (phase1_continuation_refined_transfer_parameter transfer)
                            (phase1_continuation_refined_transfer_boundary transfer)
                            (phase1_continuation_refined_transfer_guard transfer)
                            continuation))
                  | None => None
                  end
              | Phase1ContinuationRefinedOpaqueSelectSession selected_tree =>
                  Some
                    (Phase1RecursiveTransferNonreferenceSession
                      (Phase1RecursiveTransferOpaqueSelectSession selected_tree))
              | Phase1ContinuationRefinedOpaqueOfferSession selected_tree =>
                  Some
                    (Phase1RecursiveTransferNonreferenceSession
                      (Phase1RecursiveTransferOpaqueOfferSession selected_tree))
              | Phase1ContinuationRefinedOpaqueEndSession selected_tree =>
                  Some
                    (Phase1RecursiveTransferNonreferenceSession
                      (Phase1RecursiveTransferOpaqueEndSession selected_tree))
              | Phase1ContinuationRefinedOpaqueRecursiveSession selected_tree =>
                  Some
                    (Phase1RecursiveTransferNonreferenceSession
                      (Phase1RecursiveTransferOpaqueRecursiveSession selected_tree))
              | Phase1ContinuationRefinedOpaqueContinueSession selected_tree =>
                  Some
                    (Phase1RecursiveTransferNonreferenceSession
                      (Phase1RecursiveTransferOpaqueContinueSession selected_tree))
              end
          end
      | None => None
      end
  end.

Definition phase1_surface_normalize_recursive_transfer_session_tree_fuel
  (fuel : nat)
  (tree : ParseTree) : option Phase1SurfaceRecursiveTransferSessionSpine :=
  match
    phase1_surface_normalize_guard_refined_boundary_typed_transfer_session_tree
      tree
  with
  | Some session =>
      phase1_surface_normalize_recursive_transfer_session_spine_fuel fuel session
  | None => None
  end.

Theorem
  phase1_surface_normalize_recursive_transfer_session_spine_fuel_round_trip :
  forall fuel session refined,
    phase1_surface_normalize_recursive_transfer_session_spine_fuel
      fuel session = Some refined ->
    phase1_surface_recursive_transfer_session_spine_tree refined =
      phase1_surface_guard_refined_boundary_typed_transfer_session_spine_tree
        session.
Proof.
  induction fuel as [|fuel IH]; intros session refined Hnormalize.
  - discriminate Hnormalize.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_continuation_refined_transfer_session_spine
        session)
      as [step |] eqn:Hstep; try discriminate Hnormalize.
    pose proof
      (phase1_surface_normalize_continuation_refined_transfer_session_spine_round_trip
        session step Hstep) as Hstep_tree.
    destruct step as [nonreference | reference_tree].
    + destruct nonreference as
        [transfer | selected | selected | selected | selected | selected].
      * destruct
          (phase1_surface_normalize_recursive_transfer_session_spine_fuel
            fuel
            (phase1_continuation_refined_transfer_continuation transfer))
          as [continuation |] eqn:Hcontinuation;
          try discriminate Hnormalize.
        inversion Hnormalize; subst refined.
        transitivity
          (phase1_surface_continuation_refined_transfer_session_spine_tree
            (Phase1ContinuationRefinedTransferNonreferenceSession
              (Phase1ContinuationRefinedTransferSession transfer))).
        -- cbn.
           rewrite
             (IH
               (phase1_continuation_refined_transfer_continuation transfer)
               continuation Hcontinuation).
           reflexivity.
        -- exact Hstep_tree.
      * inversion Hnormalize; subst refined.
        transitivity
          (phase1_surface_continuation_refined_transfer_session_spine_tree
            (Phase1ContinuationRefinedTransferNonreferenceSession
              (Phase1ContinuationRefinedOpaqueSelectSession selected))).
        -- reflexivity.
        -- exact Hstep_tree.
      * inversion Hnormalize; subst refined.
        transitivity
          (phase1_surface_continuation_refined_transfer_session_spine_tree
            (Phase1ContinuationRefinedTransferNonreferenceSession
              (Phase1ContinuationRefinedOpaqueOfferSession selected))).
        -- reflexivity.
        -- exact Hstep_tree.
      * inversion Hnormalize; subst refined.
        transitivity
          (phase1_surface_continuation_refined_transfer_session_spine_tree
            (Phase1ContinuationRefinedTransferNonreferenceSession
              (Phase1ContinuationRefinedOpaqueEndSession selected))).
        -- reflexivity.
        -- exact Hstep_tree.
      * inversion Hnormalize; subst refined.
        transitivity
          (phase1_surface_continuation_refined_transfer_session_spine_tree
            (Phase1ContinuationRefinedTransferNonreferenceSession
              (Phase1ContinuationRefinedOpaqueRecursiveSession selected))).
        -- reflexivity.
        -- exact Hstep_tree.
      * inversion Hnormalize; subst refined.
        transitivity
          (phase1_surface_continuation_refined_transfer_session_spine_tree
            (Phase1ContinuationRefinedTransferNonreferenceSession
              (Phase1ContinuationRefinedOpaqueContinueSession selected))).
        -- reflexivity.
        -- exact Hstep_tree.
    + inversion Hnormalize; subst refined.
      transitivity
        (phase1_surface_continuation_refined_transfer_session_spine_tree
          (Phase1ContinuationRefinedTransferStaticReferenceSession
            reference_tree)).
      * reflexivity.
      * exact Hstep_tree.
Qed.

Theorem
  phase1_surface_normalize_recursive_transfer_session_tree_fuel_round_trip :
  forall fuel tree refined,
    phase1_surface_normalize_recursive_transfer_session_tree_fuel fuel tree =
      Some refined ->
    phase1_surface_recursive_transfer_session_spine_tree refined = tree.
Proof.
  intros fuel tree refined Hnormalize.
  unfold phase1_surface_normalize_recursive_transfer_session_tree_fuel
    in Hnormalize.
  destruct
    (phase1_surface_normalize_guard_refined_boundary_typed_transfer_session_tree
      tree)
    as [session |] eqn:Hsession; try discriminate Hnormalize.
  transitivity
    (phase1_surface_guard_refined_boundary_typed_transfer_session_spine_tree
      session).
  - eapply
      phase1_surface_normalize_recursive_transfer_session_spine_fuel_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_guard_refined_boundary_typed_transfer_session_tree_round_trip.
    exact Hsession.
Qed.
