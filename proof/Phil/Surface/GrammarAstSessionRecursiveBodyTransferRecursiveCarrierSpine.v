From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionRecursiveOneStepCarrierSpine
  GrammarAstSessionRecursiveBodyOneStepCarrierSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Propagate one-level recursive-body refinement through send/receive
  continuation chains only.

  Each transfer continuation first crosses the already-closed shallow
  recursive-shell/body layer, then recurses through this carrier. Select/offer
  choices remain values of the continue-mutual recursive choice carrier, so
  branch-continuation propagation is deliberately deferred.

  Recursive payload bodies remain one-level values of the continue-mutual
  carrier. Nested recursive shells inside those bodies therefore remain at the
  existing opaque recursive-payload boundary. Binder scope/resolution is not
  claimed here.
*)

Inductive Phase1SurfaceRecursiveBodyTransferRecursiveSessionSpine : Type :=
| Phase1RecursiveBodyTransferRecursiveNonreferenceSession
    (session : Phase1SurfaceRecursiveBodyTransferRecursiveNonreferenceSessionSpine)
| Phase1RecursiveBodyTransferRecursiveStaticReferenceSession
    (reference_tree : ParseTree)

with Phase1SurfaceRecursiveBodyTransferRecursiveNonreferenceSessionSpine : Type :=
| Phase1RecursiveBodyTransferRecursiveTransferSession
    (direction : Phase1SurfaceSessionTransferDirection)
    (parameter : Phase1SurfaceTermParamTypeSpine)
    (boundary : option Phase1SurfaceStaticTypeArgumentsReferenceSpine)
    (guard : option Phase1SurfacePropositionSpine)
    (continuation : Phase1SurfaceRecursiveBodyTransferRecursiveSessionSpine)
| Phase1RecursiveBodyTransferRecursiveSelectSession
    (choice : Phase1SurfaceContinueMutualRecursiveSessionChoiceSpine)
| Phase1RecursiveBodyTransferRecursiveOfferSession
    (choice : Phase1SurfaceContinueMutualRecursiveSessionChoiceSpine)
| Phase1RecursiveBodyTransferRecursiveEndSession
    (terminal : Phase1SurfaceEndSessionSpine)
| Phase1RecursiveBodyTransferRecursiveRecursiveSession
    (payload : Phase1SurfaceRecursiveBodyOneStepPayloadSpine)
| Phase1RecursiveBodyTransferRecursiveContinueSession
    (payload : Phase1SurfaceContinueSessionPayloadSpine).

Fixpoint phase1_surface_recursive_body_transfer_recursive_session_spine_tree
  (session : Phase1SurfaceRecursiveBodyTransferRecursiveSessionSpine)
  : ParseTree :=
  match session with
  | Phase1RecursiveBodyTransferRecursiveNonreferenceSession nonreference =>
      PTNonterminal "session_expression"
        (PTAlternative 0
          (phase1_surface_recursive_body_transfer_recursive_nonreference_session_spine_tree
            nonreference))
  | Phase1RecursiveBodyTransferRecursiveStaticReferenceSession reference_tree =>
      PTNonterminal "session_expression" (PTAlternative 1 reference_tree)
  end

with phase1_surface_recursive_body_transfer_recursive_nonreference_session_spine_tree
  (session : Phase1SurfaceRecursiveBodyTransferRecursiveNonreferenceSessionSpine)
  : ParseTree :=
  match session with
  | Phase1RecursiveBodyTransferRecursiveTransferSession
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
              phase1_surface_recursive_body_transfer_recursive_session_spine_tree
                continuation
            ]))
  | Phase1RecursiveBodyTransferRecursiveSelectSession choice =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 2
          (phase1_surface_continue_mutual_recursive_session_choice_spine_tree
            choice))
  | Phase1RecursiveBodyTransferRecursiveOfferSession choice =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 3
          (phase1_surface_continue_mutual_recursive_session_choice_spine_tree
            choice))
  | Phase1RecursiveBodyTransferRecursiveEndSession terminal =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 4 (phase1_surface_end_session_spine_tree terminal))
  | Phase1RecursiveBodyTransferRecursiveRecursiveSession payload =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 5
          (phase1_surface_recursive_body_one_step_payload_spine_tree payload))
  | Phase1RecursiveBodyTransferRecursiveContinueSession payload =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 6
          (phase1_surface_continue_session_payload_spine_tree payload))
  end.

Fixpoint
  phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels
  (body_source_fuel body_closure_fuel transfer_fuel : nat)
  (session : Phase1SurfaceRecursiveBodyOneStepSessionSpine)
  : option Phase1SurfaceRecursiveBodyTransferRecursiveSessionSpine :=
  match transfer_fuel with
  | 0 => None
  | S remaining =>
      let normalize_continuation :=
        fun continuation : Phase1SurfaceContinueMutualRecursiveSessionSpine =>
          match
            phase1_surface_normalize_recursive_one_step_session_spine
              continuation
          with
          | Some shell =>
              match
                phase1_surface_normalize_recursive_body_one_step_session_spine_fuels
                  body_source_fuel body_closure_fuel shell
              with
              | Some body_step =>
                  phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels
                    body_source_fuel body_closure_fuel remaining body_step
              | None => None
              end
          | None => None
          end in
      match session with
      | Phase1RecursiveBodyOneStepStaticReferenceSession reference_tree =>
          Some
            (Phase1RecursiveBodyTransferRecursiveStaticReferenceSession
              reference_tree)
      | Phase1RecursiveBodyOneStepNonreferenceSession nonreference =>
          match nonreference with
          | Phase1RecursiveBodyOneStepTransferSession
              direction parameter boundary guard continuation =>
              match normalize_continuation continuation with
              | Some refined_continuation =>
                  Some
                    (Phase1RecursiveBodyTransferRecursiveNonreferenceSession
                      (Phase1RecursiveBodyTransferRecursiveTransferSession
                        direction parameter boundary guard refined_continuation))
              | None => None
              end
          | Phase1RecursiveBodyOneStepSelectSession choice =>
              Some
                (Phase1RecursiveBodyTransferRecursiveNonreferenceSession
                  (Phase1RecursiveBodyTransferRecursiveSelectSession choice))
          | Phase1RecursiveBodyOneStepOfferSession choice =>
              Some
                (Phase1RecursiveBodyTransferRecursiveNonreferenceSession
                  (Phase1RecursiveBodyTransferRecursiveOfferSession choice))
          | Phase1RecursiveBodyOneStepEndSession terminal =>
              Some
                (Phase1RecursiveBodyTransferRecursiveNonreferenceSession
                  (Phase1RecursiveBodyTransferRecursiveEndSession terminal))
          | Phase1RecursiveBodyOneStepRecursiveSession payload =>
              Some
                (Phase1RecursiveBodyTransferRecursiveNonreferenceSession
                  (Phase1RecursiveBodyTransferRecursiveRecursiveSession payload))
          | Phase1RecursiveBodyOneStepContinueSession payload =>
              Some
                (Phase1RecursiveBodyTransferRecursiveNonreferenceSession
                  (Phase1RecursiveBodyTransferRecursiveContinueSession payload))
          end
      end
  end.

Theorem
  phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels_round_trip :
  forall body_source_fuel body_closure_fuel transfer_fuel session refined,
    phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels
      body_source_fuel body_closure_fuel transfer_fuel session = Some refined ->
    phase1_surface_recursive_body_transfer_recursive_session_spine_tree refined =
      phase1_surface_recursive_body_one_step_session_spine_tree session.
Proof.
  induction transfer_fuel as [|remaining IH];
    intros session refined Hnormalize.
  - discriminate Hnormalize.
  - cbn in Hnormalize.
    assert (Hcontinuation :
      forall continuation converted,
        (match
          phase1_surface_normalize_recursive_one_step_session_spine continuation
        with
        | Some shell =>
            match
              phase1_surface_normalize_recursive_body_one_step_session_spine_fuels
                body_source_fuel body_closure_fuel shell
            with
            | Some body_step =>
                phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels
                  body_source_fuel body_closure_fuel remaining body_step
            | None => None
            end
        | None => None
        end) = Some converted ->
        phase1_surface_recursive_body_transfer_recursive_session_spine_tree
          converted =
        phase1_surface_continue_mutual_recursive_session_spine_tree continuation).
    {
      intros continuation converted Hconverted.
      destruct
        (phase1_surface_normalize_recursive_one_step_session_spine continuation)
        as [shell |] eqn:Hshell; try discriminate Hconverted.
      destruct
        (phase1_surface_normalize_recursive_body_one_step_session_spine_fuels
          body_source_fuel body_closure_fuel shell)
        as [body_step |] eqn:Hbody; try discriminate Hconverted.
      transitivity
        (phase1_surface_recursive_body_one_step_session_spine_tree body_step).
      - eapply IH.
        exact Hconverted.
      - transitivity
          (phase1_surface_recursive_one_step_session_spine_tree shell).
        + eapply
            phase1_surface_normalize_recursive_body_one_step_session_spine_fuels_round_trip.
          exact Hbody.
        + eapply phase1_surface_normalize_recursive_one_step_session_spine_round_trip.
          exact Hshell.
    }
    destruct session as [nonreference | reference_tree].
    + destruct nonreference as
        [direction parameter boundary guard continuation
        |choice
        |choice
        |terminal
        |payload
        |payload].
      * destruct
          (match
            phase1_surface_normalize_recursive_one_step_session_spine continuation
          with
          | Some shell =>
              match
                phase1_surface_normalize_recursive_body_one_step_session_spine_fuels
                  body_source_fuel body_closure_fuel shell
              with
              | Some body_step =>
                  phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels
                    body_source_fuel body_closure_fuel remaining body_step
              | None => None
              end
          | None => None
          end)
          as [converted |] eqn:Hconverted; try discriminate Hnormalize.
        inversion Hnormalize; subst refined.
        cbn.
        rewrite (Hcontinuation continuation converted Hconverted).
        reflexivity.
      * inversion Hnormalize; subst refined. reflexivity.
      * inversion Hnormalize; subst refined. reflexivity.
      * inversion Hnormalize; subst refined. reflexivity.
      * inversion Hnormalize; subst refined. reflexivity.
      * inversion Hnormalize; subst refined. reflexivity.
    + inversion Hnormalize; subst refined.
      reflexivity.
Qed.
