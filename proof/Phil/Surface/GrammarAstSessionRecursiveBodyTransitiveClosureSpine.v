From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionRecursiveBodyMutualAdapter.

Import ListNotations.
Open Scope string_scope.

(*
  Close recursive-body traversal transitively.

  The predecessor carrier already closes transfer and select/offer continuation
  recursion and refines each recursive payload body one level.  This family
  additionally makes recursive payload bodies point back to the same final
  session carrier.

  The four adapter fuels remain fixed parameters.  A separate traversal fuel
  decreases on every recursive structural edge: transfer continuation,
  choice-branch continuation, or recursive payload body.  Binder scope and
  recursion-variable resolution remain separate semantic obligations.
*)

Inductive Phase1SurfaceRecursiveBodyTransitiveSessionSpine : Type :=
| Phase1RecursiveBodyTransitiveNonreferenceSession
    (session : Phase1SurfaceRecursiveBodyTransitiveNonreferenceSessionSpine)
| Phase1RecursiveBodyTransitiveStaticReferenceSession
    (reference_tree : ParseTree)

with Phase1SurfaceRecursiveBodyTransitiveNonreferenceSessionSpine : Type :=
| Phase1RecursiveBodyTransitiveTransferSession
    (direction : Phase1SurfaceSessionTransferDirection)
    (parameter : Phase1SurfaceTermParamTypeSpine)
    (boundary : option Phase1SurfaceStaticTypeArgumentsReferenceSpine)
    (guard : option Phase1SurfacePropositionSpine)
    (continuation : Phase1SurfaceRecursiveBodyTransitiveSessionSpine)
| Phase1RecursiveBodyTransitiveSelectSession
    (choice : Phase1SurfaceRecursiveBodyTransitiveSessionChoiceSpine)
| Phase1RecursiveBodyTransitiveOfferSession
    (choice : Phase1SurfaceRecursiveBodyTransitiveSessionChoiceSpine)
| Phase1RecursiveBodyTransitiveEndSession
    (terminal : Phase1SurfaceEndSessionSpine)
| Phase1RecursiveBodyTransitiveRecursiveSession
    (name : string)
    (body : Phase1SurfaceRecursiveBodyTransitiveSessionSpine)
| Phase1RecursiveBodyTransitiveContinueSession
    (payload : Phase1SurfaceContinueSessionPayloadSpine)

with Phase1SurfaceRecursiveBodyTransitiveSessionChoiceSpine : Type :=
| Phase1RecursiveBodyTransitiveChoice
    (direction : Phase1SurfaceSessionChoiceDirection)
    (first_branch : Phase1SurfaceRecursiveBodyTransitiveSessionBranchSpine)
    (rest_branches : Phase1SurfaceRecursiveBodyTransitiveSessionBranchTailSpine)

with Phase1SurfaceRecursiveBodyTransitiveSessionBranchSpine : Type :=
| Phase1RecursiveBodyTransitiveBranch
    (label : string)
    (params : option (list Phase1SurfaceTermParamTypeSpine))
    (boundary : option Phase1SurfaceStaticTypeArgumentsReferenceSpine)
    (guard : option Phase1SurfacePropositionSpine)
    (continuation : Phase1SurfaceRecursiveBodyTransitiveSessionSpine)

with Phase1SurfaceRecursiveBodyTransitiveSessionBranchTailSpine : Type :=
| Phase1RecursiveBodyTransitiveBranchTailNil
| Phase1RecursiveBodyTransitiveBranchTailCons
    (branch : Phase1SurfaceRecursiveBodyTransitiveSessionBranchSpine)
    (rest : Phase1SurfaceRecursiveBodyTransitiveSessionBranchTailSpine).

Fixpoint phase1_surface_recursive_body_transitive_session_spine_tree
  (session : Phase1SurfaceRecursiveBodyTransitiveSessionSpine) : ParseTree :=
  match session with
  | Phase1RecursiveBodyTransitiveNonreferenceSession nonreference =>
      PTNonterminal "session_expression"
        (PTAlternative 0
          (phase1_surface_recursive_body_transitive_nonreference_session_spine_tree
            nonreference))
  | Phase1RecursiveBodyTransitiveStaticReferenceSession reference_tree =>
      PTNonterminal "session_expression" (PTAlternative 1 reference_tree)
  end

with phase1_surface_recursive_body_transitive_nonreference_session_spine_tree
  (session : Phase1SurfaceRecursiveBodyTransitiveNonreferenceSessionSpine)
  : ParseTree :=
  match session with
  | Phase1RecursiveBodyTransitiveTransferSession
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
              phase1_surface_recursive_body_transitive_session_spine_tree
                continuation
            ]))
  | Phase1RecursiveBodyTransitiveSelectSession choice =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 2
          (phase1_surface_recursive_body_transitive_session_choice_spine_tree
            choice))
  | Phase1RecursiveBodyTransitiveOfferSession choice =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 3
          (phase1_surface_recursive_body_transitive_session_choice_spine_tree
            choice))
  | Phase1RecursiveBodyTransitiveEndSession terminal =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 4 (phase1_surface_end_session_spine_tree terminal))
  | Phase1RecursiveBodyTransitiveRecursiveSession name body =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 5
          (PTSequence
            [ PTLiteral "recursive";
              phase1_surface_identifier_tree name;
              PTLiteral "=";
              phase1_surface_recursive_body_transitive_session_spine_tree body
            ]))
  | Phase1RecursiveBodyTransitiveContinueSession payload =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 6
          (phase1_surface_continue_session_payload_spine_tree payload))
  end

with phase1_surface_recursive_body_transitive_session_choice_spine_tree
  (choice : Phase1SurfaceRecursiveBodyTransitiveSessionChoiceSpine) : ParseTree :=
  match choice with
  | Phase1RecursiveBodyTransitiveChoice direction first_branch rest_branches =>
      PTSequence
        [ PTLiteral (phase1_surface_session_choice_keyword direction);
          PTLiteral "{";
          phase1_surface_recursive_body_transitive_session_branch_spine_tree
            first_branch;
          PTRepetition
            (phase1_surface_recursive_body_transitive_session_branch_tail_spine_trees
              rest_branches);
          PTLiteral "}"
        ]
  end

with phase1_surface_recursive_body_transitive_session_branch_spine_tree
  (branch : Phase1SurfaceRecursiveBodyTransitiveSessionBranchSpine) : ParseTree :=
  match branch with
  | Phase1RecursiveBodyTransitiveBranch
      label params boundary guard continuation =>
      PTNonterminal "session_branch"
        (PTSequence
          [ phase1_surface_identifier_tree label;
            phase1_surface_session_branch_params_tree params;
            phase1_surface_boundary_refined_annotation_tree boundary;
            phase1_surface_guard_refined_annotation_tree guard;
            PTLiteral "=>";
            phase1_surface_recursive_body_transitive_session_spine_tree
              continuation
          ])
  end

with phase1_surface_recursive_body_transitive_session_branch_tail_spine_trees
  (branches : Phase1SurfaceRecursiveBodyTransitiveSessionBranchTailSpine)
  : list ParseTree :=
  match branches with
  | Phase1RecursiveBodyTransitiveBranchTailNil => []
  | Phase1RecursiveBodyTransitiveBranchTailCons branch rest =>
      phase1_surface_session_branch_suffix_tree
        (phase1_surface_recursive_body_transitive_session_branch_spine_tree branch)
      :: phase1_surface_recursive_body_transitive_session_branch_tail_spine_trees
           rest
  end.

Definition phase1_surface_normalize_recursive_body_transitive_session_branch_with
  (normalize_continuation :
    Phase1SurfaceRecursiveBodyMutualRecursiveSessionSpine ->
      option Phase1SurfaceRecursiveBodyTransitiveSessionSpine)
  (branch : Phase1SurfaceRecursiveBodyMutualRecursiveSessionBranchSpine)
  : option Phase1SurfaceRecursiveBodyTransitiveSessionBranchSpine :=
  match branch with
  | Phase1RecursiveBodyMutualRecursiveBranch
      label params boundary guard continuation =>
      match normalize_continuation continuation with
      | Some refined_continuation =>
          Some
            (Phase1RecursiveBodyTransitiveBranch
              label params boundary guard refined_continuation)
      | None => None
      end
  end.

Fixpoint phase1_surface_normalize_recursive_body_transitive_session_branch_tail_with
  (normalize_continuation :
    Phase1SurfaceRecursiveBodyMutualRecursiveSessionSpine ->
      option Phase1SurfaceRecursiveBodyTransitiveSessionSpine)
  (branches : Phase1SurfaceRecursiveBodyMutualRecursiveSessionBranchTailSpine)
  : option Phase1SurfaceRecursiveBodyTransitiveSessionBranchTailSpine :=
  match branches with
  | Phase1RecursiveBodyMutualRecursiveBranchTailNil =>
      Some Phase1RecursiveBodyTransitiveBranchTailNil
  | Phase1RecursiveBodyMutualRecursiveBranchTailCons branch rest =>
      match
        phase1_surface_normalize_recursive_body_transitive_session_branch_with
          normalize_continuation branch,
        phase1_surface_normalize_recursive_body_transitive_session_branch_tail_with
          normalize_continuation rest
      with
      | Some refined_branch, Some refined_rest =>
          Some
            (Phase1RecursiveBodyTransitiveBranchTailCons
              refined_branch refined_rest)
      | _, _ => None
      end
  end.

Definition phase1_surface_normalize_recursive_body_transitive_session_choice_with
  (normalize_continuation :
    Phase1SurfaceRecursiveBodyMutualRecursiveSessionSpine ->
      option Phase1SurfaceRecursiveBodyTransitiveSessionSpine)
  (choice : Phase1SurfaceRecursiveBodyMutualRecursiveSessionChoiceSpine)
  : option Phase1SurfaceRecursiveBodyTransitiveSessionChoiceSpine :=
  match choice with
  | Phase1RecursiveBodyMutualRecursiveChoice direction first_branch rest_branches =>
      match
        phase1_surface_normalize_recursive_body_transitive_session_branch_with
          normalize_continuation first_branch,
        phase1_surface_normalize_recursive_body_transitive_session_branch_tail_with
          normalize_continuation rest_branches
      with
      | Some refined_first, Some refined_rest =>
          Some
            (Phase1RecursiveBodyTransitiveChoice
              direction refined_first refined_rest)
      | _, _ => None
      end
  end.

Fixpoint phase1_surface_normalize_recursive_body_transitive_session_spine_fuel
  (body_source_fuel body_closure_fuel transfer_fuel mutual_fuel traversal_fuel : nat)
  (session : Phase1SurfaceRecursiveBodyMutualRecursiveSessionSpine)
  : option Phase1SurfaceRecursiveBodyTransitiveSessionSpine :=
  match traversal_fuel with
  | 0 => None
  | S remaining =>
      let normalize_continuation :=
        phase1_surface_normalize_recursive_body_transitive_session_spine_fuel
          body_source_fuel body_closure_fuel transfer_fuel mutual_fuel remaining in
      match session with
      | Phase1RecursiveBodyMutualRecursiveStaticReferenceSession reference_tree =>
          Some (Phase1RecursiveBodyTransitiveStaticReferenceSession reference_tree)
      | Phase1RecursiveBodyMutualRecursiveNonreferenceSession nonreference =>
          match nonreference with
          | Phase1RecursiveBodyMutualRecursiveTransferSession
              direction parameter boundary guard continuation =>
              match normalize_continuation continuation with
              | Some refined_continuation =>
                  Some
                    (Phase1RecursiveBodyTransitiveNonreferenceSession
                      (Phase1RecursiveBodyTransitiveTransferSession
                        direction parameter boundary guard refined_continuation))
              | None => None
              end
          | Phase1RecursiveBodyMutualRecursiveSelectSession choice =>
              match
                phase1_surface_normalize_recursive_body_transitive_session_choice_with
                  normalize_continuation choice
              with
              | Some refined_choice =>
                  Some
                    (Phase1RecursiveBodyTransitiveNonreferenceSession
                      (Phase1RecursiveBodyTransitiveSelectSession refined_choice))
              | None => None
              end
          | Phase1RecursiveBodyMutualRecursiveOfferSession choice =>
              match
                phase1_surface_normalize_recursive_body_transitive_session_choice_with
                  normalize_continuation choice
              with
              | Some refined_choice =>
                  Some
                    (Phase1RecursiveBodyTransitiveNonreferenceSession
                      (Phase1RecursiveBodyTransitiveOfferSession refined_choice))
              | None => None
              end
          | Phase1RecursiveBodyMutualRecursiveEndSession terminal =>
              Some
                (Phase1RecursiveBodyTransitiveNonreferenceSession
                  (Phase1RecursiveBodyTransitiveEndSession terminal))
          | Phase1RecursiveBodyMutualRecursiveRecursiveSession payload =>
              match
                phase1_surface_normalize_recursive_body_mutual_adapter_fuels
                  body_source_fuel body_closure_fuel transfer_fuel mutual_fuel
                  (phase1_recursive_body_one_step_body payload)
              with
              | Some body_step =>
                  match normalize_continuation body_step with
                  | Some refined_body =>
                      Some
                        (Phase1RecursiveBodyTransitiveNonreferenceSession
                          (Phase1RecursiveBodyTransitiveRecursiveSession
                            (phase1_recursive_body_one_step_name payload)
                            refined_body))
                  | None => None
                  end
              | None => None
              end
          | Phase1RecursiveBodyMutualRecursiveContinueSession payload =>
              Some
                (Phase1RecursiveBodyTransitiveNonreferenceSession
                  (Phase1RecursiveBodyTransitiveContinueSession payload))
          end
      end
  end.

Lemma phase1_surface_normalize_recursive_body_transitive_session_branch_with_round_trip :
  forall normalize_continuation branch refined,
    (forall continuation converted,
      normalize_continuation continuation = Some converted ->
      phase1_surface_recursive_body_transitive_session_spine_tree converted =
        phase1_surface_recursive_body_mutual_recursive_session_spine_tree continuation) ->
    phase1_surface_normalize_recursive_body_transitive_session_branch_with
      normalize_continuation branch = Some refined ->
    phase1_surface_recursive_body_transitive_session_branch_spine_tree refined =
      phase1_surface_recursive_body_mutual_recursive_session_branch_spine_tree branch.
Proof.
  intros normalize_continuation
    [label params boundary guard continuation] refined Hcontinuation Hnormalize.
  cbn in Hnormalize.
  destruct (normalize_continuation continuation)
    as [converted |] eqn:Hconverted; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite (Hcontinuation continuation converted Hconverted).
  reflexivity.
Qed.

Lemma phase1_surface_normalize_recursive_body_transitive_session_branch_tail_with_round_trip :
  forall normalize_continuation branches refined,
    (forall continuation converted,
      normalize_continuation continuation = Some converted ->
      phase1_surface_recursive_body_transitive_session_spine_tree converted =
        phase1_surface_recursive_body_mutual_recursive_session_spine_tree continuation) ->
    phase1_surface_normalize_recursive_body_transitive_session_branch_tail_with
      normalize_continuation branches = Some refined ->
    phase1_surface_recursive_body_transitive_session_branch_tail_spine_trees refined =
      phase1_surface_recursive_body_mutual_recursive_session_branch_tail_spine_trees branches.
Proof.
  intros normalize_continuation branches.
  induction branches as [|branch rest IH];
    intros refined Hcontinuation Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_recursive_body_transitive_session_branch_with
        normalize_continuation branch)
      as [refined_branch |] eqn:Hbranch; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_recursive_body_transitive_session_branch_tail_with
        normalize_continuation rest)
      as [refined_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_recursive_body_transitive_session_branch_with_round_trip
        normalize_continuation branch refined_branch Hcontinuation Hbranch).
    rewrite (IH refined_rest Hcontinuation Hrest).
    reflexivity.
Qed.

Lemma phase1_surface_normalize_recursive_body_transitive_session_choice_with_round_trip :
  forall normalize_continuation choice refined,
    (forall continuation converted,
      normalize_continuation continuation = Some converted ->
      phase1_surface_recursive_body_transitive_session_spine_tree converted =
        phase1_surface_recursive_body_mutual_recursive_session_spine_tree continuation) ->
    phase1_surface_normalize_recursive_body_transitive_session_choice_with
      normalize_continuation choice = Some refined ->
    phase1_surface_recursive_body_transitive_session_choice_spine_tree refined =
      phase1_surface_recursive_body_mutual_recursive_session_choice_spine_tree choice.
Proof.
  intros normalize_continuation
    [direction first_branch rest_branches] refined Hcontinuation Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_recursive_body_transitive_session_branch_with
      normalize_continuation first_branch)
    as [refined_first |] eqn:Hfirst; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_recursive_body_transitive_session_branch_tail_with
      normalize_continuation rest_branches)
    as [refined_rest |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_recursive_body_transitive_session_branch_with_round_trip
      normalize_continuation first_branch refined_first Hcontinuation Hfirst).
  rewrite
    (phase1_surface_normalize_recursive_body_transitive_session_branch_tail_with_round_trip
      normalize_continuation rest_branches refined_rest Hcontinuation Hrest).
  reflexivity.
Qed.

Theorem phase1_surface_normalize_recursive_body_transitive_session_spine_fuel_round_trip :
  forall body_source_fuel body_closure_fuel transfer_fuel mutual_fuel traversal_fuel
    session refined,
    phase1_surface_normalize_recursive_body_transitive_session_spine_fuel
      body_source_fuel body_closure_fuel transfer_fuel mutual_fuel traversal_fuel
      session = Some refined ->
    phase1_surface_recursive_body_transitive_session_spine_tree refined =
      phase1_surface_recursive_body_mutual_recursive_session_spine_tree session.
Proof.
  intros body_source_fuel body_closure_fuel transfer_fuel mutual_fuel traversal_fuel.
  induction traversal_fuel as [|remaining IH]; intros session refined Hnormalize.
  - discriminate Hnormalize.
  - cbn in Hnormalize.
    let normalize_continuation :=
      constr:(phase1_surface_normalize_recursive_body_transitive_session_spine_fuel
        body_source_fuel body_closure_fuel transfer_fuel mutual_fuel remaining) in
    assert (Hcontinuation :
      forall continuation converted,
        normalize_continuation continuation = Some converted ->
        phase1_surface_recursive_body_transitive_session_spine_tree converted =
          phase1_surface_recursive_body_mutual_recursive_session_spine_tree continuation).
    {
      intros continuation converted Hconverted.
      eapply IH.
      exact Hconverted.
    }
    destruct session as [nonreference | reference_tree].
    + destruct nonreference as
        [direction parameter boundary guard continuation
        |choice
        |choice
        |terminal
        |payload
        |payload].
      * destruct (normalize_continuation continuation)
          as [converted |] eqn:Hconverted; try discriminate Hnormalize.
        inversion Hnormalize; subst refined.
        cbn.
        rewrite (Hcontinuation continuation converted Hconverted).
        reflexivity.
      * destruct
          (phase1_surface_normalize_recursive_body_transitive_session_choice_with
            normalize_continuation choice)
          as [converted |] eqn:Hchoice; try discriminate Hnormalize.
        inversion Hnormalize; subst refined.
        cbn.
        rewrite
          (phase1_surface_normalize_recursive_body_transitive_session_choice_with_round_trip
            normalize_continuation choice converted Hcontinuation Hchoice).
        reflexivity.
      * destruct
          (phase1_surface_normalize_recursive_body_transitive_session_choice_with
            normalize_continuation choice)
          as [converted |] eqn:Hchoice; try discriminate Hnormalize.
        inversion Hnormalize; subst refined.
        cbn.
        rewrite
          (phase1_surface_normalize_recursive_body_transitive_session_choice_with_round_trip
            normalize_continuation choice converted Hcontinuation Hchoice).
        reflexivity.
      * inversion Hnormalize; subst refined. reflexivity.
      * destruct
          (phase1_surface_normalize_recursive_body_mutual_adapter_fuels
            body_source_fuel body_closure_fuel transfer_fuel mutual_fuel
            (phase1_recursive_body_one_step_body payload))
          as [body_step |] eqn:Hbody_step; try discriminate Hnormalize.
        destruct (normalize_continuation body_step)
          as [converted_body |] eqn:Hbody; try discriminate Hnormalize.
        inversion Hnormalize; subst refined.
        cbn.
        rewrite (Hcontinuation body_step converted_body Hbody).
        rewrite
          (phase1_surface_normalize_recursive_body_mutual_adapter_fuels_round_trip
            body_source_fuel body_closure_fuel transfer_fuel mutual_fuel
            (phase1_recursive_body_one_step_body payload) body_step Hbody_step).
        reflexivity.
      * inversion Hnormalize; subst refined. reflexivity.
    + inversion Hnormalize; subst refined.
      reflexivity.
Qed.
