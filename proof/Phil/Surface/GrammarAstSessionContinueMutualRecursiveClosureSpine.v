From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionContinueChoiceOneStepCarrierSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Close transfer and select/offer continuation recursion for the session family
  in which `end` and `continue` payloads are already structured.

  The predecessor carrier refines one select/offer layer over the transfer-
  recursive continue carrier. This family makes both transfer continuations and
  branch continuations point back to the same full-session carrier. The
  `recursive identifier = session_expression` payload remains at its exact
  certified ParseTree boundary for a successor refinement.
*)

Inductive Phase1SurfaceContinueMutualRecursiveSessionSpine : Type :=
| Phase1ContinueMutualRecursiveNonreferenceSession
    (session : Phase1SurfaceContinueMutualRecursiveNonreferenceSessionSpine)
| Phase1ContinueMutualRecursiveStaticReferenceSession
    (reference_tree : ParseTree)

with Phase1SurfaceContinueMutualRecursiveNonreferenceSessionSpine : Type :=
| Phase1ContinueMutualRecursiveTransferSession
    (direction : Phase1SurfaceSessionTransferDirection)
    (parameter : Phase1SurfaceTermParamTypeSpine)
    (boundary : option Phase1SurfaceStaticTypeArgumentsReferenceSpine)
    (guard : option Phase1SurfacePropositionSpine)
    (continuation : Phase1SurfaceContinueMutualRecursiveSessionSpine)
| Phase1ContinueMutualRecursiveSelectSession
    (choice : Phase1SurfaceContinueMutualRecursiveSessionChoiceSpine)
| Phase1ContinueMutualRecursiveOfferSession
    (choice : Phase1SurfaceContinueMutualRecursiveSessionChoiceSpine)
| Phase1ContinueMutualRecursiveEndSession
    (terminal : Phase1SurfaceEndSessionSpine)
| Phase1ContinueMutualRecursiveRecursiveSession
    (selected_tree : ParseTree)
| Phase1ContinueMutualRecursiveContinueSession
    (payload : Phase1SurfaceContinueSessionPayloadSpine)

with Phase1SurfaceContinueMutualRecursiveSessionChoiceSpine : Type :=
| Phase1ContinueMutualRecursiveChoice
    (direction : Phase1SurfaceSessionChoiceDirection)
    (first_branch : Phase1SurfaceContinueMutualRecursiveSessionBranchSpine)
    (rest_branches : Phase1SurfaceContinueMutualRecursiveSessionBranchTailSpine)

with Phase1SurfaceContinueMutualRecursiveSessionBranchSpine : Type :=
| Phase1ContinueMutualRecursiveBranch
    (label : string)
    (params : option (list Phase1SurfaceTermParamTypeSpine))
    (boundary : option Phase1SurfaceStaticTypeArgumentsReferenceSpine)
    (guard : option Phase1SurfacePropositionSpine)
    (continuation : Phase1SurfaceContinueMutualRecursiveSessionSpine)

with Phase1SurfaceContinueMutualRecursiveSessionBranchTailSpine : Type :=
| Phase1ContinueMutualRecursiveBranchTailNil
| Phase1ContinueMutualRecursiveBranchTailCons
    (branch : Phase1SurfaceContinueMutualRecursiveSessionBranchSpine)
    (rest : Phase1SurfaceContinueMutualRecursiveSessionBranchTailSpine).

Fixpoint phase1_surface_continue_mutual_recursive_session_spine_tree
  (session : Phase1SurfaceContinueMutualRecursiveSessionSpine) : ParseTree :=
  match session with
  | Phase1ContinueMutualRecursiveNonreferenceSession nonreference =>
      PTNonterminal "session_expression"
        (PTAlternative 0
          (phase1_surface_continue_mutual_recursive_nonreference_session_spine_tree
            nonreference))
  | Phase1ContinueMutualRecursiveStaticReferenceSession reference_tree =>
      PTNonterminal "session_expression" (PTAlternative 1 reference_tree)
  end

with phase1_surface_continue_mutual_recursive_nonreference_session_spine_tree
  (session : Phase1SurfaceContinueMutualRecursiveNonreferenceSessionSpine)
  : ParseTree :=
  match session with
  | Phase1ContinueMutualRecursiveTransferSession
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
  | Phase1ContinueMutualRecursiveSelectSession choice =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 2
          (phase1_surface_continue_mutual_recursive_session_choice_spine_tree
            choice))
  | Phase1ContinueMutualRecursiveOfferSession choice =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 3
          (phase1_surface_continue_mutual_recursive_session_choice_spine_tree
            choice))
  | Phase1ContinueMutualRecursiveEndSession terminal =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 4 (phase1_surface_end_session_spine_tree terminal))
  | Phase1ContinueMutualRecursiveRecursiveSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 5 selected_tree)
  | Phase1ContinueMutualRecursiveContinueSession payload =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 6
          (phase1_surface_continue_session_payload_spine_tree payload))
  end

with phase1_surface_continue_mutual_recursive_session_choice_spine_tree
  (choice : Phase1SurfaceContinueMutualRecursiveSessionChoiceSpine) : ParseTree :=
  match choice with
  | Phase1ContinueMutualRecursiveChoice direction first_branch rest_branches =>
      PTSequence
        [ PTLiteral (phase1_surface_session_choice_keyword direction);
          PTLiteral "{";
          phase1_surface_continue_mutual_recursive_session_branch_spine_tree
            first_branch;
          PTRepetition
            (phase1_surface_continue_mutual_recursive_session_branch_tail_spine_trees
              rest_branches);
          PTLiteral "}"
        ]
  end

with phase1_surface_continue_mutual_recursive_session_branch_spine_tree
  (branch : Phase1SurfaceContinueMutualRecursiveSessionBranchSpine) : ParseTree :=
  match branch with
  | Phase1ContinueMutualRecursiveBranch
      label params boundary guard continuation =>
      PTNonterminal "session_branch"
        (PTSequence
          [ phase1_surface_identifier_tree label;
            phase1_surface_session_branch_params_tree params;
            phase1_surface_boundary_refined_annotation_tree boundary;
            phase1_surface_guard_refined_annotation_tree guard;
            PTLiteral "=>";
            phase1_surface_continue_mutual_recursive_session_spine_tree
              continuation
          ])
  end

with phase1_surface_continue_mutual_recursive_session_branch_tail_spine_trees
  (branches : Phase1SurfaceContinueMutualRecursiveSessionBranchTailSpine)
  : list ParseTree :=
  match branches with
  | Phase1ContinueMutualRecursiveBranchTailNil => []
  | Phase1ContinueMutualRecursiveBranchTailCons branch rest =>
      phase1_surface_session_branch_suffix_tree
        (phase1_surface_continue_mutual_recursive_session_branch_spine_tree
          branch)
      :: phase1_surface_continue_mutual_recursive_session_branch_tail_spine_trees
           rest
  end.

Definition phase1_surface_normalize_continue_mutual_recursive_session_branch_with
  (normalize_continuation :
    Phase1SurfaceContinueTransferRecursiveSessionSpine ->
      option Phase1SurfaceContinueMutualRecursiveSessionSpine)
  (branch : Phase1SurfaceContinueChoiceOneStepSessionBranchSpine)
  : option Phase1SurfaceContinueMutualRecursiveSessionBranchSpine :=
  match branch with
  | Phase1ContinueChoiceOneStepBranch
      label params boundary guard continuation =>
      match normalize_continuation continuation with
      | Some refined_continuation =>
          Some
            (Phase1ContinueMutualRecursiveBranch
              label params boundary guard refined_continuation)
      | None => None
      end
  end.

Fixpoint
  phase1_surface_normalize_continue_mutual_recursive_session_branch_tail_with
  (normalize_continuation :
    Phase1SurfaceContinueTransferRecursiveSessionSpine ->
      option Phase1SurfaceContinueMutualRecursiveSessionSpine)
  (branches : Phase1SurfaceContinueChoiceOneStepSessionBranchTailSpine)
  : option Phase1SurfaceContinueMutualRecursiveSessionBranchTailSpine :=
  match branches with
  | Phase1ContinueChoiceOneStepBranchTailNil =>
      Some Phase1ContinueMutualRecursiveBranchTailNil
  | Phase1ContinueChoiceOneStepBranchTailCons branch rest =>
      match
        phase1_surface_normalize_continue_mutual_recursive_session_branch_with
          normalize_continuation branch,
        phase1_surface_normalize_continue_mutual_recursive_session_branch_tail_with
          normalize_continuation rest
      with
      | Some refined_branch, Some refined_rest =>
          Some
            (Phase1ContinueMutualRecursiveBranchTailCons
              refined_branch refined_rest)
      | _, _ => None
      end
  end.

Definition phase1_surface_normalize_continue_mutual_recursive_session_choice_with
  (normalize_continuation :
    Phase1SurfaceContinueTransferRecursiveSessionSpine ->
      option Phase1SurfaceContinueMutualRecursiveSessionSpine)
  (choice : Phase1SurfaceContinueChoiceOneStepSessionChoiceSpine)
  : option Phase1SurfaceContinueMutualRecursiveSessionChoiceSpine :=
  match choice with
  | Phase1ContinueChoiceOneStepChoice direction first_branch rest_branches =>
      match
        phase1_surface_normalize_continue_mutual_recursive_session_branch_with
          normalize_continuation first_branch,
        phase1_surface_normalize_continue_mutual_recursive_session_branch_tail_with
          normalize_continuation rest_branches
      with
      | Some refined_first, Some refined_rest =>
          Some
            (Phase1ContinueMutualRecursiveChoice
              direction refined_first refined_rest)
      | _, _ => None
      end
  end.

Fixpoint phase1_surface_normalize_continue_mutual_recursive_session_spine_fuel
  (fuel : nat)
  (session : Phase1SurfaceContinueChoiceOneStepSessionSpine)
  : option Phase1SurfaceContinueMutualRecursiveSessionSpine :=
  match fuel with
  | 0 => None
  | S remaining =>
      let normalize_continuation :=
        fun continuation : Phase1SurfaceContinueTransferRecursiveSessionSpine =>
          match
            phase1_surface_normalize_continue_choice_one_step_session_spine
              continuation
          with
          | Some step =>
              phase1_surface_normalize_continue_mutual_recursive_session_spine_fuel
                remaining step
          | None => None
          end in
      match session with
      | Phase1ContinueChoiceOneStepStaticReferenceSession reference_tree =>
          Some
            (Phase1ContinueMutualRecursiveStaticReferenceSession reference_tree)
      | Phase1ContinueChoiceOneStepNonreferenceSession nonreference =>
          match nonreference with
          | Phase1ContinueChoiceOneStepTransferSession
              direction parameter boundary guard continuation =>
              match normalize_continuation continuation with
              | Some refined_continuation =>
                  Some
                    (Phase1ContinueMutualRecursiveNonreferenceSession
                      (Phase1ContinueMutualRecursiveTransferSession
                        direction parameter boundary guard refined_continuation))
              | None => None
              end
          | Phase1ContinueChoiceOneStepSelectSession choice =>
              match
                phase1_surface_normalize_continue_mutual_recursive_session_choice_with
                  normalize_continuation choice
              with
              | Some refined_choice =>
                  Some
                    (Phase1ContinueMutualRecursiveNonreferenceSession
                      (Phase1ContinueMutualRecursiveSelectSession refined_choice))
              | None => None
              end
          | Phase1ContinueChoiceOneStepOfferSession choice =>
              match
                phase1_surface_normalize_continue_mutual_recursive_session_choice_with
                  normalize_continuation choice
              with
              | Some refined_choice =>
                  Some
                    (Phase1ContinueMutualRecursiveNonreferenceSession
                      (Phase1ContinueMutualRecursiveOfferSession refined_choice))
              | None => None
              end
          | Phase1ContinueChoiceOneStepEndSession terminal =>
              Some
                (Phase1ContinueMutualRecursiveNonreferenceSession
                  (Phase1ContinueMutualRecursiveEndSession terminal))
          | Phase1ContinueChoiceOneStepRecursiveSession selected_tree =>
              Some
                (Phase1ContinueMutualRecursiveNonreferenceSession
                  (Phase1ContinueMutualRecursiveRecursiveSession selected_tree))
          | Phase1ContinueChoiceOneStepContinueSession payload =>
              Some
                (Phase1ContinueMutualRecursiveNonreferenceSession
                  (Phase1ContinueMutualRecursiveContinueSession payload))
          end
      end
  end.

Lemma
  phase1_surface_normalize_continue_mutual_recursive_session_branch_with_round_trip :
  forall normalize_continuation branch refined,
    (forall continuation converted,
      normalize_continuation continuation = Some converted ->
      phase1_surface_continue_mutual_recursive_session_spine_tree converted =
        phase1_surface_continue_transfer_recursive_session_spine_tree
          continuation) ->
    phase1_surface_normalize_continue_mutual_recursive_session_branch_with
      normalize_continuation branch = Some refined ->
    phase1_surface_continue_mutual_recursive_session_branch_spine_tree refined =
      phase1_surface_continue_choice_one_step_session_branch_spine_tree branch.
Proof.
  intros normalize_continuation
    [label params boundary guard continuation]
    refined Hcontinuation Hnormalize.
  cbn in Hnormalize.
  destruct (normalize_continuation continuation)
    as [converted |] eqn:Hconverted; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite (Hcontinuation continuation converted Hconverted).
  reflexivity.
Qed.

Lemma
  phase1_surface_normalize_continue_mutual_recursive_session_branch_tail_with_round_trip :
  forall normalize_continuation branches refined,
    (forall continuation converted,
      normalize_continuation continuation = Some converted ->
      phase1_surface_continue_mutual_recursive_session_spine_tree converted =
        phase1_surface_continue_transfer_recursive_session_spine_tree
          continuation) ->
    phase1_surface_normalize_continue_mutual_recursive_session_branch_tail_with
      normalize_continuation branches = Some refined ->
    phase1_surface_continue_mutual_recursive_session_branch_tail_spine_trees
      refined =
    phase1_surface_continue_choice_one_step_session_branch_tail_spine_trees
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
      (phase1_surface_normalize_continue_mutual_recursive_session_branch_with
        normalize_continuation branch)
      as [refined_branch |] eqn:Hbranch; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_continue_mutual_recursive_session_branch_tail_with
        normalize_continuation rest)
      as [refined_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_continue_mutual_recursive_session_branch_with_round_trip
        normalize_continuation branch refined_branch
        Hcontinuation Hbranch).
    rewrite (IH refined_rest Hcontinuation Hrest).
    reflexivity.
Qed.

Lemma
  phase1_surface_normalize_continue_mutual_recursive_session_choice_with_round_trip :
  forall normalize_continuation choice refined,
    (forall continuation converted,
      normalize_continuation continuation = Some converted ->
      phase1_surface_continue_mutual_recursive_session_spine_tree converted =
        phase1_surface_continue_transfer_recursive_session_spine_tree
          continuation) ->
    phase1_surface_normalize_continue_mutual_recursive_session_choice_with
      normalize_continuation choice = Some refined ->
    phase1_surface_continue_mutual_recursive_session_choice_spine_tree refined =
      phase1_surface_continue_choice_one_step_session_choice_spine_tree choice.
Proof.
  intros normalize_continuation
    [direction first_branch rest_branches]
    refined Hcontinuation Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_continue_mutual_recursive_session_branch_with
      normalize_continuation first_branch)
    as [refined_first |] eqn:Hfirst; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_continue_mutual_recursive_session_branch_tail_with
      normalize_continuation rest_branches)
    as [refined_rest |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_continue_mutual_recursive_session_branch_with_round_trip
      normalize_continuation first_branch refined_first
      Hcontinuation Hfirst).
  rewrite
    (phase1_surface_normalize_continue_mutual_recursive_session_branch_tail_with_round_trip
      normalize_continuation rest_branches refined_rest
      Hcontinuation Hrest).
  reflexivity.
Qed.

Theorem
  phase1_surface_normalize_continue_mutual_recursive_session_spine_fuel_round_trip :
  forall fuel session refined,
    phase1_surface_normalize_continue_mutual_recursive_session_spine_fuel
      fuel session = Some refined ->
    phase1_surface_continue_mutual_recursive_session_spine_tree refined =
      phase1_surface_continue_choice_one_step_session_spine_tree session.
Proof.
  induction fuel as [|remaining IH]; intros session refined Hnormalize.
  - discriminate Hnormalize.
  - cbn in Hnormalize.
    assert (Hcontinuation :
      forall continuation converted,
        (match
          phase1_surface_normalize_continue_choice_one_step_session_spine
            continuation
        with
        | Some step =>
            phase1_surface_normalize_continue_mutual_recursive_session_spine_fuel
              remaining step
        | None => None
        end) = Some converted ->
        phase1_surface_continue_mutual_recursive_session_spine_tree converted =
          phase1_surface_continue_transfer_recursive_session_spine_tree
            continuation).
    {
      intros continuation converted Hconverted.
      destruct
        (phase1_surface_normalize_continue_choice_one_step_session_spine
          continuation)
        as [step |] eqn:Hstep; try discriminate Hconverted.
      transitivity
        (phase1_surface_continue_choice_one_step_session_spine_tree step).
      - eapply IH.
        exact Hconverted.
      - eapply
          phase1_surface_normalize_continue_choice_one_step_session_spine_round_trip.
        exact Hstep.
    }
    destruct session as [nonreference | reference_tree].
    + destruct nonreference as
        [direction parameter boundary guard continuation
        |choice
        |choice
        |terminal
        |selected_tree
        |payload].
      * destruct
          (match
            phase1_surface_normalize_continue_choice_one_step_session_spine
              continuation
          with
          | Some step =>
              phase1_surface_normalize_continue_mutual_recursive_session_spine_fuel
                remaining step
          | None => None
          end)
          as [converted |] eqn:Hconverted; try discriminate Hnormalize.
        inversion Hnormalize; subst refined.
        cbn.
        rewrite (Hcontinuation continuation converted Hconverted).
        reflexivity.
      * destruct
          (phase1_surface_normalize_continue_mutual_recursive_session_choice_with
            (fun continuation =>
              match
                phase1_surface_normalize_continue_choice_one_step_session_spine
                  continuation
              with
              | Some step =>
                  phase1_surface_normalize_continue_mutual_recursive_session_spine_fuel
                    remaining step
              | None => None
              end)
            choice)
          as [refined_choice |] eqn:Hchoice; try discriminate Hnormalize.
        inversion Hnormalize; subst refined.
        cbn.
        rewrite
          (phase1_surface_normalize_continue_mutual_recursive_session_choice_with_round_trip
            _ choice refined_choice Hcontinuation Hchoice).
        reflexivity.
      * destruct
          (phase1_surface_normalize_continue_mutual_recursive_session_choice_with
            (fun continuation =>
              match
                phase1_surface_normalize_continue_choice_one_step_session_spine
                  continuation
              with
              | Some step =>
                  phase1_surface_normalize_continue_mutual_recursive_session_spine_fuel
                    remaining step
              | None => None
              end)
            choice)
          as [refined_choice |] eqn:Hchoice; try discriminate Hnormalize.
        inversion Hnormalize; subst refined.
        cbn.
        rewrite
          (phase1_surface_normalize_continue_mutual_recursive_session_choice_with_round_trip
            _ choice refined_choice Hcontinuation Hchoice).
        reflexivity.
      * inversion Hnormalize; subst refined. reflexivity.
      * inversion Hnormalize; subst refined. reflexivity.
      * inversion Hnormalize; subst refined. reflexivity.
    + inversion Hnormalize; subst refined.
      reflexivity.
Qed.
