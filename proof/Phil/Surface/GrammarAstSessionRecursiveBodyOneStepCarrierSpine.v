From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionRecursiveOneStepCarrierSpine
  GrammarAstSessionContinueMutualRecursiveTreeAdapter.

Import ListNotations.
Open Scope string_scope.

(*
  Enter a structured `recursive identifier = session_expression` payload body
  exactly one level.

  The recursive shell is already structured by the predecessor carrier.  This
  layer replaces only its exact body ParseTree with the already-closed
  continue-mutual recursive session carrier.  Any nested `recursive` shell
  inside that body remains at the continue-mutual carrier's existing opaque
  recursive-payload boundary.  Binder scope/resolution is deliberately not
  claimed here.
*)

Record Phase1SurfaceRecursiveBodyOneStepPayloadSpine : Type := {
  phase1_recursive_body_one_step_name : string;
  phase1_recursive_body_one_step_body :
    Phase1SurfaceContinueMutualRecursiveSessionSpine
}.

Inductive Phase1SurfaceRecursiveBodyOneStepNonreferenceSessionSpine : Type :=
| Phase1RecursiveBodyOneStepTransferSession
    (direction : Phase1SurfaceSessionTransferDirection)
    (parameter : Phase1SurfaceTermParamTypeSpine)
    (boundary : option Phase1SurfaceStaticTypeArgumentsReferenceSpine)
    (guard : option Phase1SurfacePropositionSpine)
    (continuation : Phase1SurfaceContinueMutualRecursiveSessionSpine)
| Phase1RecursiveBodyOneStepSelectSession
    (choice : Phase1SurfaceContinueMutualRecursiveSessionChoiceSpine)
| Phase1RecursiveBodyOneStepOfferSession
    (choice : Phase1SurfaceContinueMutualRecursiveSessionChoiceSpine)
| Phase1RecursiveBodyOneStepEndSession
    (terminal : Phase1SurfaceEndSessionSpine)
| Phase1RecursiveBodyOneStepRecursiveSession
    (payload : Phase1SurfaceRecursiveBodyOneStepPayloadSpine)
| Phase1RecursiveBodyOneStepContinueSession
    (payload : Phase1SurfaceContinueSessionPayloadSpine).

Inductive Phase1SurfaceRecursiveBodyOneStepSessionSpine : Type :=
| Phase1RecursiveBodyOneStepNonreferenceSession
    (session : Phase1SurfaceRecursiveBodyOneStepNonreferenceSessionSpine)
| Phase1RecursiveBodyOneStepStaticReferenceSession
    (reference_tree : ParseTree).

Definition phase1_surface_recursive_body_one_step_payload_spine_tree
  (payload : Phase1SurfaceRecursiveBodyOneStepPayloadSpine) : ParseTree :=
  PTSequence
    [ PTLiteral "recursive";
      phase1_surface_identifier_tree
        (phase1_recursive_body_one_step_name payload);
      PTLiteral "=";
      phase1_surface_continue_mutual_recursive_session_spine_tree
        (phase1_recursive_body_one_step_body payload)
    ].

Definition
  phase1_surface_recursive_body_one_step_nonreference_session_spine_tree
  (session : Phase1SurfaceRecursiveBodyOneStepNonreferenceSessionSpine)
  : ParseTree :=
  match session with
  | Phase1RecursiveBodyOneStepTransferSession
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
              phase1_surface_continue_mutual_recursive_session_spine_tree
                continuation
            ]))
  | Phase1RecursiveBodyOneStepSelectSession choice =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 2
          (phase1_surface_continue_mutual_recursive_session_choice_spine_tree
            choice))
  | Phase1RecursiveBodyOneStepOfferSession choice =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 3
          (phase1_surface_continue_mutual_recursive_session_choice_spine_tree
            choice))
  | Phase1RecursiveBodyOneStepEndSession terminal =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 4 (phase1_surface_end_session_spine_tree terminal))
  | Phase1RecursiveBodyOneStepRecursiveSession payload =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 5
          (phase1_surface_recursive_body_one_step_payload_spine_tree payload))
  | Phase1RecursiveBodyOneStepContinueSession payload =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 6
          (phase1_surface_continue_session_payload_spine_tree payload))
  end.

Definition phase1_surface_recursive_body_one_step_session_spine_tree
  (session : Phase1SurfaceRecursiveBodyOneStepSessionSpine) : ParseTree :=
  match session with
  | Phase1RecursiveBodyOneStepNonreferenceSession nonreference =>
      PTNonterminal "session_expression"
        (PTAlternative 0
          (phase1_surface_recursive_body_one_step_nonreference_session_spine_tree
            nonreference))
  | Phase1RecursiveBodyOneStepStaticReferenceSession reference_tree =>
      PTNonterminal "session_expression" (PTAlternative 1 reference_tree)
  end.

Definition
  phase1_surface_normalize_recursive_body_one_step_nonreference_session_spine_fuels
  (source_fuel closure_fuel : nat)
  (session : Phase1SurfaceRecursiveOneStepNonreferenceSessionSpine)
  : option Phase1SurfaceRecursiveBodyOneStepNonreferenceSessionSpine :=
  match session with
  | Phase1RecursiveOneStepTransferSession
      direction parameter boundary guard continuation =>
      Some
        (Phase1RecursiveBodyOneStepTransferSession
          direction parameter boundary guard continuation)
  | Phase1RecursiveOneStepSelectSession choice =>
      Some (Phase1RecursiveBodyOneStepSelectSession choice)
  | Phase1RecursiveOneStepOfferSession choice =>
      Some (Phase1RecursiveBodyOneStepOfferSession choice)
  | Phase1RecursiveOneStepEndSession terminal =>
      Some (Phase1RecursiveBodyOneStepEndSession terminal)
  | Phase1RecursiveOneStepRecursiveSession payload =>
      match
        phase1_surface_normalize_continue_mutual_recursive_session_tree_fuels
          source_fuel closure_fuel
          (phase1_recursive_session_body_tree payload)
      with
      | Some body =>
          Some
            (Phase1RecursiveBodyOneStepRecursiveSession
              {| phase1_recursive_body_one_step_name :=
                   phase1_recursive_session_name payload;
                 phase1_recursive_body_one_step_body := body |})
      | None => None
      end
  | Phase1RecursiveOneStepContinueSession payload =>
      Some (Phase1RecursiveBodyOneStepContinueSession payload)
  end.

Theorem
  phase1_surface_normalize_recursive_body_one_step_nonreference_session_spine_fuels_round_trip :
  forall source_fuel closure_fuel session refined,
    phase1_surface_normalize_recursive_body_one_step_nonreference_session_spine_fuels
      source_fuel closure_fuel session = Some refined ->
    phase1_surface_recursive_body_one_step_nonreference_session_spine_tree
      refined =
    phase1_surface_recursive_one_step_nonreference_session_spine_tree session.
Proof.
  intros source_fuel closure_fuel session refined Hnormalize.
  destruct session as
    [direction parameter boundary guard continuation
    |choice
    |choice
    |terminal
    |recursive_payload
    |payload].
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - destruct recursive_payload as [name body_tree].
    cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_continue_mutual_recursive_session_tree_fuels
        source_fuel closure_fuel body_tree)
      as [body |] eqn:Hbody; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_continue_mutual_recursive_session_tree_fuels_round_trip
        source_fuel closure_fuel body_tree body Hbody).
    reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
Qed.

Definition phase1_surface_normalize_recursive_body_one_step_session_spine_fuels
  (source_fuel closure_fuel : nat)
  (session : Phase1SurfaceRecursiveOneStepSessionSpine)
  : option Phase1SurfaceRecursiveBodyOneStepSessionSpine :=
  match session with
  | Phase1RecursiveOneStepNonreferenceSession nonreference =>
      match
        phase1_surface_normalize_recursive_body_one_step_nonreference_session_spine_fuels
          source_fuel closure_fuel nonreference
      with
      | Some refined =>
          Some (Phase1RecursiveBodyOneStepNonreferenceSession refined)
      | None => None
      end
  | Phase1RecursiveOneStepStaticReferenceSession reference_tree =>
      Some (Phase1RecursiveBodyOneStepStaticReferenceSession reference_tree)
  end.

Theorem
  phase1_surface_normalize_recursive_body_one_step_session_spine_fuels_round_trip :
  forall source_fuel closure_fuel session refined,
    phase1_surface_normalize_recursive_body_one_step_session_spine_fuels
      source_fuel closure_fuel session = Some refined ->
    phase1_surface_recursive_body_one_step_session_spine_tree refined =
      phase1_surface_recursive_one_step_session_spine_tree session.
Proof.
  intros source_fuel closure_fuel [nonreference | reference_tree]
    refined Hnormalize.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_recursive_body_one_step_nonreference_session_spine_fuels
        source_fuel closure_fuel nonreference)
      as [actual |] eqn:Hnonreference; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_recursive_body_one_step_nonreference_session_spine_fuels_round_trip
        source_fuel closure_fuel nonreference actual Hnonreference).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.
