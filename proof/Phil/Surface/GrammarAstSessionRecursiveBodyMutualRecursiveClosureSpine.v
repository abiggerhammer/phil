From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionRecursiveBodyChoiceOneStepCarrierSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Close transfer and select/offer continuation recursion for the session family
  whose recursive payload bodies have already been refined one level.

  The predecessor carrier opens one select/offer layer over the transfer-
  recursive body carrier.  This family makes both transfer continuations and
  branch continuations point back to the same full-session carrier.

  Recursive payload bodies themselves remain one-level values of the
  continue-mutual carrier; nested recursive shells inside those bodies are not
  traversed here.  Binder scope/resolution is not claimed here.
*)

Inductive Phase1SurfaceRecursiveBodyMutualRecursiveSessionSpine : Type :=
| Phase1RecursiveBodyMutualRecursiveNonreferenceSession
    (session : Phase1SurfaceRecursiveBodyMutualRecursiveNonreferenceSessionSpine)
| Phase1RecursiveBodyMutualRecursiveStaticReferenceSession
    (reference_tree : ParseTree)

with Phase1SurfaceRecursiveBodyMutualRecursiveNonreferenceSessionSpine : Type :=
| Phase1RecursiveBodyMutualRecursiveTransferSession
    (direction : Phase1SurfaceSessionTransferDirection)
    (parameter : Phase1SurfaceTermParamTypeSpine)
    (boundary : option Phase1SurfaceStaticTypeArgumentsReferenceSpine)
    (guard : option Phase1SurfacePropositionSpine)
    (continuation : Phase1SurfaceRecursiveBodyMutualRecursiveSessionSpine)
| Phase1RecursiveBodyMutualRecursiveSelectSession
    (choice : Phase1SurfaceRecursiveBodyMutualRecursiveSessionChoiceSpine)
| Phase1RecursiveBodyMutualRecursiveOfferSession
    (choice : Phase1SurfaceRecursiveBodyMutualRecursiveSessionChoiceSpine)
| Phase1RecursiveBodyMutualRecursiveEndSession
    (terminal : Phase1SurfaceEndSessionSpine)
| Phase1RecursiveBodyMutualRecursiveRecursiveSession
    (payload : Phase1SurfaceRecursiveBodyOneStepPayloadSpine)
| Phase1RecursiveBodyMutualRecursiveContinueSession
    (payload : Phase1SurfaceContinueSessionPayloadSpine)

with Phase1SurfaceRecursiveBodyMutualRecursiveSessionChoiceSpine : Type :=
| Phase1RecursiveBodyMutualRecursiveChoice
    (direction : Phase1SurfaceSessionChoiceDirection)
    (first_branch : Phase1SurfaceRecursiveBodyMutualRecursiveSessionBranchSpine)
    (rest_branches : Phase1SurfaceRecursiveBodyMutualRecursiveSessionBranchTailSpine)

with Phase1SurfaceRecursiveBodyMutualRecursiveSessionBranchSpine : Type :=
| Phase1RecursiveBodyMutualRecursiveBranch
    (label : string)
    (params : option (list Phase1SurfaceTermParamTypeSpine))
    (boundary : option Phase1SurfaceStaticTypeArgumentsReferenceSpine)
    (guard : option Phase1SurfacePropositionSpine)
    (continuation : Phase1SurfaceRecursiveBodyMutualRecursiveSessionSpine)

with Phase1SurfaceRecursiveBodyMutualRecursiveSessionBranchTailSpine : Type :=
| Phase1RecursiveBodyMutualRecursiveBranchTailNil
| Phase1RecursiveBodyMutualRecursiveBranchTailCons
    (branch : Phase1SurfaceRecursiveBodyMutualRecursiveSessionBranchSpine)
    (rest : Phase1SurfaceRecursiveBodyMutualRecursiveSessionBranchTailSpine).

Fixpoint phase1_surface_recursive_body_mutual_recursive_session_spine_tree
  (session : Phase1SurfaceRecursiveBodyMutualRecursiveSessionSpine) : ParseTree :=
  match session with
  | Phase1RecursiveBodyMutualRecursiveNonreferenceSession nonreference =>
      PTNonterminal "session_expression"
        (PTAlternative 0
          (phase1_surface_recursive_body_mutual_recursive_nonreference_session_spine_tree
            nonreference))
  | Phase1RecursiveBodyMutualRecursiveStaticReferenceSession reference_tree =>
      PTNonterminal "session_expression" (PTAlternative 1 reference_tree)
  end

with phase1_surface_recursive_body_mutual_recursive_nonreference_session_spine_tree
  (session : Phase1SurfaceRecursiveBodyMutualRecursiveNonreferenceSessionSpine)
  : ParseTree :=
  match session with
  | Phase1RecursiveBodyMutualRecursiveTransferSession
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
              phase1_surface_recursive_body_mutual_recursive_session_spine_tree
                continuation
            ]))
  | Phase1RecursiveBodyMutualRecursiveSelectSession choice =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 2
          (phase1_surface_recursive_body_mutual_recursive_session_choice_spine_tree
            choice))
  | Phase1RecursiveBodyMutualRecursiveOfferSession choice =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 3
          (phase1_surface_recursive_body_mutual_recursive_session_choice_spine_tree
            choice))
  | Phase1RecursiveBodyMutualRecursiveEndSession terminal =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 4 (phase1_surface_end_session_spine_tree terminal))
  | Phase1RecursiveBodyMutualRecursiveRecursiveSession payload =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 5
          (phase1_surface_recursive_body_one_step_payload_spine_tree payload))
  | Phase1RecursiveBodyMutualRecursiveContinueSession payload =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 6
          (phase1_surface_continue_session_payload_spine_tree payload))
  end

with phase1_surface_recursive_body_mutual_recursive_session_choice_spine_tree
  (choice : Phase1SurfaceRecursiveBodyMutualRecursiveSessionChoiceSpine)
  : ParseTree :=
  match choice with
  | Phase1RecursiveBodyMutualRecursiveChoice direction first_branch rest_branches =>
      PTSequence
        [ PTLiteral (phase1_surface_session_choice_keyword direction);
          PTLiteral "{";
          phase1_surface_recursive_body_mutual_recursive_session_branch_spine_tree
            first_branch;
          PTRepetition
            (phase1_surface_recursive_body_mutual_recursive_session_branch_tail_spine_trees
              rest_branches);
          PTLiteral "}"
        ]
  end

with phase1_surface_recursive_body_mutual_recursive_session_branch_spine_tree
  (branch : Phase1SurfaceRecursiveBodyMutualRecursiveSessionBranchSpine)
  : ParseTree :=
  match branch with
  | Phase1RecursiveBodyMutualRecursiveBranch
      label params boundary guard continuation =>
      PTNonterminal "session_branch"
        (PTSequence
          [ phase1_surface_identifier_tree label;
            phase1_surface_session_branch_params_tree params;
            phase1_surface_boundary_refined_annotation_tree boundary;
            phase1_surface_guard_refined_annotation_tree guard;
            PTLiteral "=>";
            phase1_surface_recursive_body_mutual_recursive_session_spine_tree
              continuation
          ])
  end

with phase1_surface_recursive_body_mutual_recursive_session_branch_tail_spine_trees
  (branches : Phase1SurfaceRecursiveBodyMutualRecursiveSessionBranchTailSpine)
  : list ParseTree :=
  match branches with
  | Phase1RecursiveBodyMutualRecursiveBranchTailNil => []
  | Phase1RecursiveBodyMutualRecursiveBranchTailCons branch rest =>
      phase1_surface_session_branch_suffix_tree
        (phase1_surface_recursive_body_mutual_recursive_session_branch_spine_tree
          branch)
      :: phase1_surface_recursive_body_mutual_recursive_session_branch_tail_spine_trees
           rest
  end.

Definition phase1_surface_normalize_recursive_body_mutual_recursive_session_branch_with
  (normalize_continuation :
    Phase1SurfaceRecursiveBodyTransferRecursiveSessionSpine ->
      option Phase1SurfaceRecursiveBodyMutualRecursiveSessionSpine)
  (branch : Phase1SurfaceRecursiveBodyChoiceOneStepSessionBranchSpine)
  : option Phase1SurfaceRecursiveBodyMutualRecursiveSessionBranchSpine :=
  match normalize_continuation
    (phase1_recursive_body_choice_branch_continuation branch) with
  | Some refined_continuation =>
      Some
        (Phase1RecursiveBodyMutualRecursiveBranch
          (phase1_recursive_body_choice_branch_label branch)
          (phase1_recursive_body_choice_branch_params branch)
          (phase1_recursive_body_choice_branch_boundary branch)
          (phase1_recursive_body_choice_branch_guard branch)
          refined_continuation)
  | None => None
  end.

Fixpoint
  phase1_surface_normalize_recursive_body_mutual_recursive_session_branch_tail_with
  (normalize_continuation :
    Phase1SurfaceRecursiveBodyTransferRecursiveSessionSpine ->
      option Phase1SurfaceRecursiveBodyMutualRecursiveSessionSpine)
  (branches : Phase1SurfaceRecursiveBodyChoiceOneStepSessionBranchTailSpine)
  : option Phase1SurfaceRecursiveBodyMutualRecursiveSessionBranchTailSpine :=
  match branches with
  | Phase1RecursiveBodyChoiceOneStepBranchTailNil =>
      Some Phase1RecursiveBodyMutualRecursiveBranchTailNil
  | Phase1RecursiveBodyChoiceOneStepBranchTailCons branch rest =>
      match
        phase1_surface_normalize_recursive_body_mutual_recursive_session_branch_with
          normalize_continuation branch,
        phase1_surface_normalize_recursive_body_mutual_recursive_session_branch_tail_with
          normalize_continuation rest
      with
      | Some refined_branch, Some refined_rest =>
          Some
            (Phase1RecursiveBodyMutualRecursiveBranchTailCons
              refined_branch refined_rest)
      | _, _ => None
      end
  end.

Definition phase1_surface_normalize_recursive_body_mutual_recursive_session_choice_with
  (normalize_continuation :
    Phase1SurfaceRecursiveBodyTransferRecursiveSessionSpine ->
      option Phase1SurfaceRecursiveBodyMutualRecursiveSessionSpine)
  (choice : Phase1SurfaceRecursiveBodyChoiceOneStepSessionChoiceSpine)
  : option Phase1SurfaceRecursiveBodyMutualRecursiveSessionChoiceSpine :=
  match
    phase1_surface_normalize_recursive_body_mutual_recursive_session_branch_with
      normalize_continuation
      (phase1_recursive_body_choice_first_branch choice),
    phase1_surface_normalize_recursive_body_mutual_recursive_session_branch_tail_with
      normalize_continuation
      (phase1_recursive_body_choice_rest_branches choice)
  with
  | Some refined_first, Some refined_rest =>
      Some
        (Phase1RecursiveBodyMutualRecursiveChoice
          (phase1_recursive_body_choice_direction choice)
          refined_first refined_rest)
  | _, _ => None
  end.

Fixpoint phase1_surface_normalize_recursive_body_mutual_recursive_session_spine_fuel
  (body_source_fuel body_closure_fuel transfer_fuel mutual_fuel : nat)
  (session : Phase1SurfaceRecursiveBodyChoiceOneStepSessionSpine)
  : option Phase1SurfaceRecursiveBodyMutualRecursiveSessionSpine :=
  match mutual_fuel with
  | 0 => None
  | S remaining =>
      let normalize_continuation :=
        fun continuation : Phase1SurfaceRecursiveBodyTransferRecursiveSessionSpine =>
          match
            phase1_surface_normalize_recursive_body_choice_one_step_session_spine_fuels
              body_source_fuel body_closure_fuel transfer_fuel continuation
          with
          | Some step =>
              phase1_surface_normalize_recursive_body_mutual_recursive_session_spine_fuel
                body_source_fuel body_closure_fuel transfer_fuel remaining step
          | None => None
          end in
      match session with
      | Phase1RecursiveBodyChoiceOneStepStaticReferenceSession reference_tree =>
          Some
            (Phase1RecursiveBodyMutualRecursiveStaticReferenceSession reference_tree)
      | Phase1RecursiveBodyChoiceOneStepNonreferenceSession nonreference =>
          match nonreference with
          | Phase1RecursiveBodyChoiceOneStepTransferSession
              direction parameter boundary guard continuation =>
              match normalize_continuation continuation with
              | Some refined_continuation =>
                  Some
                    (Phase1RecursiveBodyMutualRecursiveNonreferenceSession
                      (Phase1RecursiveBodyMutualRecursiveTransferSession
                        direction parameter boundary guard refined_continuation))
              | None => None
              end
          | Phase1RecursiveBodyChoiceOneStepSelectSession choice =>
              match
                phase1_surface_normalize_recursive_body_mutual_recursive_session_choice_with
                  normalize_continuation choice
              with
              | Some refined_choice =>
                  Some
                    (Phase1RecursiveBodyMutualRecursiveNonreferenceSession
                      (Phase1RecursiveBodyMutualRecursiveSelectSession refined_choice))
              | None => None
              end
          | Phase1RecursiveBodyChoiceOneStepOfferSession choice =>
              match
                phase1_surface_normalize_recursive_body_mutual_recursive_session_choice_with
                  normalize_continuation choice
              with
              | Some refined_choice =>
                  Some
                    (Phase1RecursiveBodyMutualRecursiveNonreferenceSession
                      (Phase1RecursiveBodyMutualRecursiveOfferSession refined_choice))
              | None => None
              end
          | Phase1RecursiveBodyChoiceOneStepEndSession terminal =>
              Some
                (Phase1RecursiveBodyMutualRecursiveNonreferenceSession
                  (Phase1RecursiveBodyMutualRecursiveEndSession terminal))
          | Phase1RecursiveBodyChoiceOneStepRecursiveSession payload =>
              Some
                (Phase1RecursiveBodyMutualRecursiveNonreferenceSession
                  (Phase1RecursiveBodyMutualRecursiveRecursiveSession payload))
          | Phase1RecursiveBodyChoiceOneStepContinueSession payload =>
              Some
                (Phase1RecursiveBodyMutualRecursiveNonreferenceSession
                  (Phase1RecursiveBodyMutualRecursiveContinueSession payload))
          end
      end
  end.

Lemma
  phase1_surface_normalize_recursive_body_mutual_recursive_session_branch_with_round_trip :
  forall normalize_continuation branch refined,
    (forall continuation converted,
      normalize_continuation continuation = Some converted ->
      phase1_surface_recursive_body_mutual_recursive_session_spine_tree converted =
        phase1_surface_recursive_body_transfer_recursive_session_spine_tree
          continuation) ->
    phase1_surface_normalize_recursive_body_mutual_recursive_session_branch_with
      normalize_continuation branch = Some refined ->
    phase1_surface_recursive_body_mutual_recursive_session_branch_spine_tree
      refined =
    phase1_surface_recursive_body_choice_one_step_session_branch_spine_tree branch.
Proof.
  intros normalize_continuation branch refined Hcontinuation Hnormalize.
  unfold
    phase1_surface_normalize_recursive_body_mutual_recursive_session_branch_with
    in Hnormalize.
  destruct
    (normalize_continuation
      (phase1_recursive_body_choice_branch_continuation branch))
    as [converted |] eqn:Hconverted; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  unfold phase1_surface_recursive_body_choice_one_step_session_branch_spine_tree.
  cbn.
  rewrite
    (Hcontinuation
      (phase1_recursive_body_choice_branch_continuation branch)
      converted Hconverted).
  reflexivity.
Qed.

Lemma
  phase1_surface_normalize_recursive_body_mutual_recursive_session_branch_tail_with_round_trip :
  forall normalize_continuation branches refined,
    (forall continuation converted,
      normalize_continuation continuation = Some converted ->
      phase1_surface_recursive_body_mutual_recursive_session_spine_tree converted =
        phase1_surface_recursive_body_transfer_recursive_session_spine_tree
          continuation) ->
    phase1_surface_normalize_recursive_body_mutual_recursive_session_branch_tail_with
      normalize_continuation branches = Some refined ->
    phase1_surface_recursive_body_mutual_recursive_session_branch_tail_spine_trees
      refined =
    phase1_surface_recursive_body_choice_one_step_session_branch_tail_spine_trees
      branches.
Proof.
  intros normalize_continuation branches.
  induction branches as [|branch rest IH];
    intros refined Hcontinuation Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_recursive_body_mutual_recursive_session_branch_with
        normalize_continuation branch)
      as [refined_branch |] eqn:Hbranch; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_recursive_body_mutual_recursive_session_branch_tail_with
        normalize_continuation rest)
      as [refined_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_recursive_body_mutual_recursive_session_branch_with_round_trip
        normalize_continuation branch refined_branch Hcontinuation Hbranch).
    rewrite (IH refined_rest Hcontinuation Hrest).
    reflexivity.
Qed.

Lemma
  phase1_surface_normalize_recursive_body_mutual_recursive_session_choice_with_round_trip :
  forall normalize_continuation choice refined,
    (forall continuation converted,
      normalize_continuation continuation = Some converted ->
      phase1_surface_recursive_body_mutual_recursive_session_spine_tree converted =
        phase1_surface_recursive_body_transfer_recursive_session_spine_tree
          continuation) ->
    phase1_surface_normalize_recursive_body_mutual_recursive_session_choice_with
      normalize_continuation choice = Some refined ->
    phase1_surface_recursive_body_mutual_recursive_session_choice_spine_tree refined =
      phase1_surface_recursive_body_choice_one_step_session_choice_spine_tree choice.
Proof.
  intros normalize_continuation choice refined Hcontinuation Hnormalize.
  unfold
    phase1_surface_normalize_recursive_body_mutual_recursive_session_choice_with
    in Hnormalize.
  destruct
    (phase1_surface_normalize_recursive_body_mutual_recursive_session_branch_with
      normalize_continuation
      (phase1_recursive_body_choice_first_branch choice))
    as [refined_first |] eqn:Hfirst; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_recursive_body_mutual_recursive_session_branch_tail_with
      normalize_continuation
      (phase1_recursive_body_choice_rest_branches choice))
    as [refined_rest |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_recursive_body_mutual_recursive_session_branch_with_round_trip
      normalize_continuation
      (phase1_recursive_body_choice_first_branch choice)
      refined_first Hcontinuation Hfirst).
  rewrite
    (phase1_surface_normalize_recursive_body_mutual_recursive_session_branch_tail_with_round_trip
      normalize_continuation
      (phase1_recursive_body_choice_rest_branches choice)
      refined_rest Hcontinuation Hrest).
  reflexivity.
Qed.

Theorem
  phase1_surface_normalize_recursive_body_mutual_recursive_session_spine_fuel_round_trip :
  forall body_source_fuel body_closure_fuel transfer_fuel mutual_fuel
    session refined,
    phase1_surface_normalize_recursive_body_mutual_recursive_session_spine_fuel
      body_source_fuel body_closure_fuel transfer_fuel mutual_fuel session =
      Some refined ->
    phase1_surface_recursive_body_mutual_recursive_session_spine_tree refined =
      phase1_surface_recursive_body_choice_one_step_session_spine_tree session.
Proof.
  intros body_source_fuel body_closure_fuel transfer_fuel mutual_fuel.
  induction mutual_fuel as [|remaining IH]; intros session refined Hnormalize.
  - discriminate Hnormalize.
  - cbn in Hnormalize.
    assert (Hcontinuation :
      forall continuation converted,
        (match
          phase1_surface_normalize_recursive_body_choice_one_step_session_spine_fuels
            body_source_fuel body_closure_fuel transfer_fuel continuation
        with
        | Some step =>
            phase1_surface_normalize_recursive_body_mutual_recursive_session_spine_fuel
              body_source_fuel body_closure_fuel transfer_fuel remaining step
        | None => None
        end) = Some converted ->
        phase1_surface_recursive_body_mutual_recursive_session_spine_tree
          converted =
        phase1_surface_recursive_body_transfer_recursive_session_spine_tree
          continuation).
    {
      intros continuation converted Hconverted.
      destruct
        (phase1_surface_normalize_recursive_body_choice_one_step_session_spine_fuels
          body_source_fuel body_closure_fuel transfer_fuel continuation)
        as [step |] eqn:Hstep; try discriminate Hconverted.
      transitivity
        (phase1_surface_recursive_body_choice_one_step_session_spine_tree step).
      - eapply IH.
        exact Hconverted.
      - eapply
          phase1_surface_normalize_recursive_body_choice_one_step_session_spine_fuels_round_trip.
        exact Hstep.
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
            phase1_surface_normalize_recursive_body_choice_one_step_session_spine_fuels
              body_source_fuel body_closure_fuel transfer_fuel continuation
          with
          | Some step =>
              phase1_surface_normalize_recursive_body_mutual_recursive_session_spine_fuel
                body_source_fuel body_closure_fuel transfer_fuel remaining step
          | None => None
          end)
          as [converted |] eqn:Hconverted; try discriminate Hnormalize.
        inversion Hnormalize; subst refined.
        cbn.
        rewrite (Hcontinuation continuation converted Hconverted).
        reflexivity.
      * destruct
          (phase1_surface_normalize_recursive_body_mutual_recursive_session_choice_with
            (fun continuation =>
              match
                phase1_surface_normalize_recursive_body_choice_one_step_session_spine_fuels
                  body_source_fuel body_closure_fuel transfer_fuel continuation
              with
              | Some step =>
                  phase1_surface_normalize_recursive_body_mutual_recursive_session_spine_fuel
                    body_source_fuel body_closure_fuel transfer_fuel remaining step
              | None => None
              end)
            choice)
          as [converted |] eqn:Hchoice; try discriminate Hnormalize.
        inversion Hnormalize; subst refined.
        cbn.
        rewrite
          (phase1_surface_normalize_recursive_body_mutual_recursive_session_choice_with_round_trip
            (fun continuation =>
              match
                phase1_surface_normalize_recursive_body_choice_one_step_session_spine_fuels
                  body_source_fuel body_closure_fuel transfer_fuel continuation
              with
              | Some step =>
                  phase1_surface_normalize_recursive_body_mutual_recursive_session_spine_fuel
                    body_source_fuel body_closure_fuel transfer_fuel remaining step
              | None => None
              end)
            choice converted Hcontinuation Hchoice).
        reflexivity.
      * destruct
          (phase1_surface_normalize_recursive_body_mutual_recursive_session_choice_with
            (fun continuation =>
              match
                phase1_surface_normalize_recursive_body_choice_one_step_session_spine_fuels
                  body_source_fuel body_closure_fuel transfer_fuel continuation
              with
              | Some step =>
                  phase1_surface_normalize_recursive_body_mutual_recursive_session_spine_fuel
                    body_source_fuel body_closure_fuel transfer_fuel remaining step
              | None => None
              end)
            choice)
          as [converted |] eqn:Hchoice; try discriminate Hnormalize.
        inversion Hnormalize; subst refined.
        cbn.
        rewrite
          (phase1_surface_normalize_recursive_body_mutual_recursive_session_choice_with_round_trip
            (fun continuation =>
              match
                phase1_surface_normalize_recursive_body_choice_one_step_session_spine_fuels
                  body_source_fuel body_closure_fuel transfer_fuel continuation
              with
              | Some step =>
                  phase1_surface_normalize_recursive_body_mutual_recursive_session_spine_fuel
                    body_source_fuel body_closure_fuel transfer_fuel remaining step
              | None => None
              end)
            choice converted Hcontinuation Hchoice).
        reflexivity.
      * inversion Hnormalize; subst refined. reflexivity.
      * inversion Hnormalize; subst refined. reflexivity.
      * inversion Hnormalize; subst refined. reflexivity.
    + inversion Hnormalize; subst refined.
      reflexivity.
Qed.
