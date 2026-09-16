From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionContinueMutualRecursiveClosureSpine
  GrammarAstSessionRecursiveOneStepCarrierSpine
  GrammarAstSessionRecursiveBodyOneStepCarrierSpine
  GrammarAstSessionRecursiveBodyTransferRecursiveCarrierSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Compose transfer-recursive recursive-body refinement with one layer of
  select/offer branch continuations.

  Each branch continuation crosses the already-closed shallow recursive shell,
  one-level body refinement, and transfer-recursive body carrier under the
  supplied fuels. Nested select/offer choices reached from that continuation
  remain at their existing continue-mutual boundary. This is deliberately a
  one-step composition layer; mutual transfer/choice closure remains a
  successor.
*)

Definition phase1_surface_normalize_recursive_body_choice_one_step_continuation_fuels
  (body_source_fuel body_closure_fuel transfer_fuel : nat)
  (continuation : Phase1SurfaceContinueMutualRecursiveSessionSpine)
  : option Phase1SurfaceRecursiveBodyTransferRecursiveSessionSpine :=
  match phase1_surface_normalize_recursive_one_step_session_spine continuation with
  | Some shell =>
      match
        phase1_surface_normalize_recursive_body_one_step_session_spine_fuels
          body_source_fuel body_closure_fuel shell
      with
      | Some body_step =>
          phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels
            body_source_fuel body_closure_fuel transfer_fuel body_step
      | None => None
      end
  | None => None
  end.

Record Phase1SurfaceRecursiveBodyChoiceOneStepSessionBranchSpine : Type := {
  phase1_recursive_body_choice_branch_label : string;
  phase1_recursive_body_choice_branch_params :
    option (list Phase1SurfaceTermParamTypeSpine);
  phase1_recursive_body_choice_branch_boundary :
    option Phase1SurfaceStaticTypeArgumentsReferenceSpine;
  phase1_recursive_body_choice_branch_guard :
    option Phase1SurfacePropositionSpine;
  phase1_recursive_body_choice_branch_continuation :
    Phase1SurfaceRecursiveBodyTransferRecursiveSessionSpine
}.

Inductive Phase1SurfaceRecursiveBodyChoiceOneStepSessionBranchTailSpine : Type :=
| Phase1RecursiveBodyChoiceOneStepBranchTailNil
| Phase1RecursiveBodyChoiceOneStepBranchTailCons
    (branch : Phase1SurfaceRecursiveBodyChoiceOneStepSessionBranchSpine)
    (rest : Phase1SurfaceRecursiveBodyChoiceOneStepSessionBranchTailSpine).

Record Phase1SurfaceRecursiveBodyChoiceOneStepSessionChoiceSpine : Type := {
  phase1_recursive_body_choice_direction : Phase1SurfaceSessionChoiceDirection;
  phase1_recursive_body_choice_first_branch :
    Phase1SurfaceRecursiveBodyChoiceOneStepSessionBranchSpine;
  phase1_recursive_body_choice_rest_branches :
    Phase1SurfaceRecursiveBodyChoiceOneStepSessionBranchTailSpine
}.

Inductive Phase1SurfaceRecursiveBodyChoiceOneStepNonreferenceSessionSpine : Type :=
| Phase1RecursiveBodyChoiceOneStepTransferSession
    (direction : Phase1SurfaceSessionTransferDirection)
    (parameter : Phase1SurfaceTermParamTypeSpine)
    (boundary : option Phase1SurfaceStaticTypeArgumentsReferenceSpine)
    (guard : option Phase1SurfacePropositionSpine)
    (continuation : Phase1SurfaceRecursiveBodyTransferRecursiveSessionSpine)
| Phase1RecursiveBodyChoiceOneStepSelectSession
    (choice : Phase1SurfaceRecursiveBodyChoiceOneStepSessionChoiceSpine)
| Phase1RecursiveBodyChoiceOneStepOfferSession
    (choice : Phase1SurfaceRecursiveBodyChoiceOneStepSessionChoiceSpine)
| Phase1RecursiveBodyChoiceOneStepEndSession
    (terminal : Phase1SurfaceEndSessionSpine)
| Phase1RecursiveBodyChoiceOneStepRecursiveSession
    (payload : Phase1SurfaceRecursiveBodyOneStepPayloadSpine)
| Phase1RecursiveBodyChoiceOneStepContinueSession
    (payload : Phase1SurfaceContinueSessionPayloadSpine).

Inductive Phase1SurfaceRecursiveBodyChoiceOneStepSessionSpine : Type :=
| Phase1RecursiveBodyChoiceOneStepNonreferenceSession
    (session : Phase1SurfaceRecursiveBodyChoiceOneStepNonreferenceSessionSpine)
| Phase1RecursiveBodyChoiceOneStepStaticReferenceSession
    (reference_tree : ParseTree).

Definition phase1_surface_recursive_body_choice_one_step_session_branch_spine_tree
  (branch : Phase1SurfaceRecursiveBodyChoiceOneStepSessionBranchSpine)
  : ParseTree :=
  PTNonterminal "session_branch"
    (PTSequence
      [ phase1_surface_identifier_tree
          (phase1_recursive_body_choice_branch_label branch);
        phase1_surface_session_branch_params_tree
          (phase1_recursive_body_choice_branch_params branch);
        phase1_surface_boundary_refined_annotation_tree
          (phase1_recursive_body_choice_branch_boundary branch);
        phase1_surface_guard_refined_annotation_tree
          (phase1_recursive_body_choice_branch_guard branch);
        PTLiteral "=>";
        phase1_surface_recursive_body_transfer_recursive_session_spine_tree
          (phase1_recursive_body_choice_branch_continuation branch)
      ]).

Fixpoint
  phase1_surface_recursive_body_choice_one_step_session_branch_tail_spine_trees
  (branches : Phase1SurfaceRecursiveBodyChoiceOneStepSessionBranchTailSpine)
  : list ParseTree :=
  match branches with
  | Phase1RecursiveBodyChoiceOneStepBranchTailNil => []
  | Phase1RecursiveBodyChoiceOneStepBranchTailCons branch rest =>
      phase1_surface_session_branch_suffix_tree
        (phase1_surface_recursive_body_choice_one_step_session_branch_spine_tree
          branch)
      :: phase1_surface_recursive_body_choice_one_step_session_branch_tail_spine_trees
           rest
  end.

Definition phase1_surface_recursive_body_choice_one_step_session_choice_spine_tree
  (choice : Phase1SurfaceRecursiveBodyChoiceOneStepSessionChoiceSpine)
  : ParseTree :=
  PTSequence
    [ PTLiteral
        (phase1_surface_session_choice_keyword
          (phase1_recursive_body_choice_direction choice));
      PTLiteral "{";
      phase1_surface_recursive_body_choice_one_step_session_branch_spine_tree
        (phase1_recursive_body_choice_first_branch choice);
      PTRepetition
        (phase1_surface_recursive_body_choice_one_step_session_branch_tail_spine_trees
          (phase1_recursive_body_choice_rest_branches choice));
      PTLiteral "}"
    ].

Definition
  phase1_surface_recursive_body_choice_one_step_nonreference_session_spine_tree
  (session : Phase1SurfaceRecursiveBodyChoiceOneStepNonreferenceSessionSpine)
  : ParseTree :=
  match session with
  | Phase1RecursiveBodyChoiceOneStepTransferSession
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
  | Phase1RecursiveBodyChoiceOneStepSelectSession choice =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 2
          (phase1_surface_recursive_body_choice_one_step_session_choice_spine_tree
            choice))
  | Phase1RecursiveBodyChoiceOneStepOfferSession choice =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 3
          (phase1_surface_recursive_body_choice_one_step_session_choice_spine_tree
            choice))
  | Phase1RecursiveBodyChoiceOneStepEndSession terminal =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 4 (phase1_surface_end_session_spine_tree terminal))
  | Phase1RecursiveBodyChoiceOneStepRecursiveSession payload =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 5
          (phase1_surface_recursive_body_one_step_payload_spine_tree payload))
  | Phase1RecursiveBodyChoiceOneStepContinueSession payload =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 6
          (phase1_surface_continue_session_payload_spine_tree payload))
  end.

Definition phase1_surface_recursive_body_choice_one_step_session_spine_tree
  (session : Phase1SurfaceRecursiveBodyChoiceOneStepSessionSpine) : ParseTree :=
  match session with
  | Phase1RecursiveBodyChoiceOneStepNonreferenceSession nonreference =>
      PTNonterminal "session_expression"
        (PTAlternative 0
          (phase1_surface_recursive_body_choice_one_step_nonreference_session_spine_tree
            nonreference))
  | Phase1RecursiveBodyChoiceOneStepStaticReferenceSession reference_tree =>
      PTNonterminal "session_expression" (PTAlternative 1 reference_tree)
  end.

Definition
  phase1_surface_normalize_recursive_body_choice_one_step_session_branch_spine_fuels
  (body_source_fuel body_closure_fuel transfer_fuel : nat)
  (branch : Phase1SurfaceContinueMutualRecursiveSessionBranchSpine)
  : option Phase1SurfaceRecursiveBodyChoiceOneStepSessionBranchSpine :=
  match branch with
  | Phase1ContinueMutualRecursiveBranch
      label params boundary guard continuation =>
      match
        phase1_surface_normalize_recursive_body_choice_one_step_continuation_fuels
          body_source_fuel body_closure_fuel transfer_fuel continuation
      with
      | Some refined_continuation =>
          Some
            {| phase1_recursive_body_choice_branch_label := label;
               phase1_recursive_body_choice_branch_params := params;
               phase1_recursive_body_choice_branch_boundary := boundary;
               phase1_recursive_body_choice_branch_guard := guard;
               phase1_recursive_body_choice_branch_continuation :=
                 refined_continuation |}
      | None => None
      end
  end.

Fixpoint
  phase1_surface_normalize_recursive_body_choice_one_step_session_branch_tail_spine_fuels
  (body_source_fuel body_closure_fuel transfer_fuel : nat)
  (branches : Phase1SurfaceContinueMutualRecursiveSessionBranchTailSpine)
  : option Phase1SurfaceRecursiveBodyChoiceOneStepSessionBranchTailSpine :=
  match branches with
  | Phase1ContinueMutualRecursiveBranchTailNil =>
      Some Phase1RecursiveBodyChoiceOneStepBranchTailNil
  | Phase1ContinueMutualRecursiveBranchTailCons branch rest =>
      match
        phase1_surface_normalize_recursive_body_choice_one_step_session_branch_spine_fuels
          body_source_fuel body_closure_fuel transfer_fuel branch,
        phase1_surface_normalize_recursive_body_choice_one_step_session_branch_tail_spine_fuels
          body_source_fuel body_closure_fuel transfer_fuel rest
      with
      | Some refined_branch, Some refined_rest =>
          Some
            (Phase1RecursiveBodyChoiceOneStepBranchTailCons
              refined_branch refined_rest)
      | _, _ => None
      end
  end.

Definition
  phase1_surface_normalize_recursive_body_choice_one_step_session_choice_spine_fuels
  (body_source_fuel body_closure_fuel transfer_fuel : nat)
  (choice : Phase1SurfaceContinueMutualRecursiveSessionChoiceSpine)
  : option Phase1SurfaceRecursiveBodyChoiceOneStepSessionChoiceSpine :=
  match choice with
  | Phase1ContinueMutualRecursiveChoice direction first_branch rest_branches =>
      match
        phase1_surface_normalize_recursive_body_choice_one_step_session_branch_spine_fuels
          body_source_fuel body_closure_fuel transfer_fuel first_branch,
        phase1_surface_normalize_recursive_body_choice_one_step_session_branch_tail_spine_fuels
          body_source_fuel body_closure_fuel transfer_fuel rest_branches
      with
      | Some refined_first, Some refined_rest =>
          Some
            {| phase1_recursive_body_choice_direction := direction;
               phase1_recursive_body_choice_first_branch := refined_first;
               phase1_recursive_body_choice_rest_branches := refined_rest |}
      | _, _ => None
      end
  end.

Definition
  phase1_surface_normalize_recursive_body_choice_one_step_session_spine_fuels
  (body_source_fuel body_closure_fuel transfer_fuel : nat)
  (session : Phase1SurfaceRecursiveBodyTransferRecursiveSessionSpine)
  : option Phase1SurfaceRecursiveBodyChoiceOneStepSessionSpine :=
  match session with
  | Phase1RecursiveBodyTransferRecursiveStaticReferenceSession reference_tree =>
      Some (Phase1RecursiveBodyChoiceOneStepStaticReferenceSession reference_tree)
  | Phase1RecursiveBodyTransferRecursiveNonreferenceSession nonreference =>
      match nonreference with
      | Phase1RecursiveBodyTransferRecursiveTransferSession
          direction parameter boundary guard continuation =>
          Some
            (Phase1RecursiveBodyChoiceOneStepNonreferenceSession
              (Phase1RecursiveBodyChoiceOneStepTransferSession
                direction parameter boundary guard continuation))
      | Phase1RecursiveBodyTransferRecursiveSelectSession choice =>
          match
            phase1_surface_normalize_recursive_body_choice_one_step_session_choice_spine_fuels
              body_source_fuel body_closure_fuel transfer_fuel choice
          with
          | Some refined_choice =>
              Some
                (Phase1RecursiveBodyChoiceOneStepNonreferenceSession
                  (Phase1RecursiveBodyChoiceOneStepSelectSession refined_choice))
          | None => None
          end
      | Phase1RecursiveBodyTransferRecursiveOfferSession choice =>
          match
            phase1_surface_normalize_recursive_body_choice_one_step_session_choice_spine_fuels
              body_source_fuel body_closure_fuel transfer_fuel choice
          with
          | Some refined_choice =>
              Some
                (Phase1RecursiveBodyChoiceOneStepNonreferenceSession
                  (Phase1RecursiveBodyChoiceOneStepOfferSession refined_choice))
          | None => None
          end
      | Phase1RecursiveBodyTransferRecursiveEndSession terminal =>
          Some
            (Phase1RecursiveBodyChoiceOneStepNonreferenceSession
              (Phase1RecursiveBodyChoiceOneStepEndSession terminal))
      | Phase1RecursiveBodyTransferRecursiveRecursiveSession payload =>
          Some
            (Phase1RecursiveBodyChoiceOneStepNonreferenceSession
              (Phase1RecursiveBodyChoiceOneStepRecursiveSession payload))
      | Phase1RecursiveBodyTransferRecursiveContinueSession payload =>
          Some
            (Phase1RecursiveBodyChoiceOneStepNonreferenceSession
              (Phase1RecursiveBodyChoiceOneStepContinueSession payload))
      end
  end.

Theorem
  phase1_surface_normalize_recursive_body_choice_one_step_session_spine_fuels_round_trip :
  forall body_source_fuel body_closure_fuel transfer_fuel session refined,
    phase1_surface_normalize_recursive_body_choice_one_step_session_spine_fuels
      body_source_fuel body_closure_fuel transfer_fuel session = Some refined ->
    phase1_surface_recursive_body_choice_one_step_session_spine_tree refined =
      phase1_surface_recursive_body_transfer_recursive_session_spine_tree session.
Proof.
  intros body_source_fuel body_closure_fuel transfer_fuel session refined Hnormalize.
  assert (Hcontinuation :
    forall continuation converted,
      phase1_surface_normalize_recursive_body_choice_one_step_continuation_fuels
        body_source_fuel body_closure_fuel transfer_fuel continuation =
        Some converted ->
      phase1_surface_recursive_body_transfer_recursive_session_spine_tree
        converted =
      phase1_surface_continue_mutual_recursive_session_spine_tree continuation).
  {
    intros continuation converted Hconverted.
    unfold
      phase1_surface_normalize_recursive_body_choice_one_step_continuation_fuels
      in Hconverted.
    destruct
      (phase1_surface_normalize_recursive_one_step_session_spine continuation)
      as [shell |] eqn:Hshell; try discriminate Hconverted.
    destruct
      (phase1_surface_normalize_recursive_body_one_step_session_spine_fuels
        body_source_fuel body_closure_fuel shell)
      as [body_step |] eqn:Hbody; try discriminate Hconverted.
    transitivity
      (phase1_surface_recursive_body_one_step_session_spine_tree body_step).
    - eapply
        phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels_round_trip.
      exact Hconverted.
    - transitivity
        (phase1_surface_recursive_one_step_session_spine_tree shell).
      + eapply
          phase1_surface_normalize_recursive_body_one_step_session_spine_fuels_round_trip.
        exact Hbody.
      + eapply phase1_surface_normalize_recursive_one_step_session_spine_round_trip.
        exact Hshell.
  }
  assert (Hbranch :
    forall branch refined_branch,
      phase1_surface_normalize_recursive_body_choice_one_step_session_branch_spine_fuels
        body_source_fuel body_closure_fuel transfer_fuel branch =
        Some refined_branch ->
      phase1_surface_recursive_body_choice_one_step_session_branch_spine_tree
        refined_branch =
      phase1_surface_continue_mutual_recursive_session_branch_spine_tree branch).
  {
    intros [label params boundary guard continuation]
      refined_branch Hbranch_normalize.
    cbn in Hbranch_normalize.
    destruct
      (phase1_surface_normalize_recursive_body_choice_one_step_continuation_fuels
        body_source_fuel body_closure_fuel transfer_fuel continuation)
      as [refined_continuation |] eqn:Hcontinuation_normalize;
      try discriminate Hbranch_normalize.
    inversion Hbranch_normalize; subst refined_branch.
    cbn.
    rewrite
      (Hcontinuation continuation refined_continuation Hcontinuation_normalize).
    reflexivity.
  }
  assert (Htail :
    forall branches refined_branches,
      phase1_surface_normalize_recursive_body_choice_one_step_session_branch_tail_spine_fuels
        body_source_fuel body_closure_fuel transfer_fuel branches =
        Some refined_branches ->
      phase1_surface_recursive_body_choice_one_step_session_branch_tail_spine_trees
        refined_branches =
      phase1_surface_continue_mutual_recursive_session_branch_tail_spine_trees
        branches).
  {
    intros branches.
    induction branches as [|branch rest IHrest];
      intros refined_branches Htail_normalize.
    - cbn in Htail_normalize.
      inversion Htail_normalize; subst refined_branches.
      reflexivity.
    - cbn in Htail_normalize.
      destruct
        (phase1_surface_normalize_recursive_body_choice_one_step_session_branch_spine_fuels
          body_source_fuel body_closure_fuel transfer_fuel branch)
        as [refined_branch |] eqn:Hbranch_normalize;
        try discriminate Htail_normalize.
      destruct
        (phase1_surface_normalize_recursive_body_choice_one_step_session_branch_tail_spine_fuels
          body_source_fuel body_closure_fuel transfer_fuel rest)
        as [refined_rest |] eqn:Hrest_normalize;
        try discriminate Htail_normalize.
      inversion Htail_normalize; subst refined_branches.
      cbn.
      rewrite (Hbranch branch refined_branch Hbranch_normalize).
      rewrite (IHrest refined_rest Hrest_normalize).
      reflexivity.
  }
  assert (Hchoice :
    forall choice refined_choice,
      phase1_surface_normalize_recursive_body_choice_one_step_session_choice_spine_fuels
        body_source_fuel body_closure_fuel transfer_fuel choice =
        Some refined_choice ->
      phase1_surface_recursive_body_choice_one_step_session_choice_spine_tree
        refined_choice =
      phase1_surface_continue_mutual_recursive_session_choice_spine_tree choice).
  {
    intros [direction first_branch rest_branches]
      refined_choice Hchoice_normalize.
    cbn in Hchoice_normalize.
    destruct
      (phase1_surface_normalize_recursive_body_choice_one_step_session_branch_spine_fuels
        body_source_fuel body_closure_fuel transfer_fuel first_branch)
      as [refined_first |] eqn:Hfirst; try discriminate Hchoice_normalize.
    destruct
      (phase1_surface_normalize_recursive_body_choice_one_step_session_branch_tail_spine_fuels
        body_source_fuel body_closure_fuel transfer_fuel rest_branches)
      as [refined_rest |] eqn:Hrest; try discriminate Hchoice_normalize.
    inversion Hchoice_normalize; subst refined_choice.
    cbn.
    rewrite (Hbranch first_branch refined_first Hfirst).
    rewrite (Htail rest_branches refined_rest Hrest).
    reflexivity.
  }
  destruct session as [nonreference | reference_tree].
  - destruct nonreference as
      [direction parameter boundary guard continuation
      |choice
      |choice
      |terminal
      |payload
      |payload].
    + inversion Hnormalize; subst refined. reflexivity.
    + cbn in Hnormalize.
      destruct
        (phase1_surface_normalize_recursive_body_choice_one_step_session_choice_spine_fuels
          body_source_fuel body_closure_fuel transfer_fuel choice)
        as [refined_choice |] eqn:Hchoice_normalize;
        try discriminate Hnormalize.
      inversion Hnormalize; subst refined.
      cbn.
      rewrite (Hchoice choice refined_choice Hchoice_normalize).
      reflexivity.
    + cbn in Hnormalize.
      destruct
        (phase1_surface_normalize_recursive_body_choice_one_step_session_choice_spine_fuels
          body_source_fuel body_closure_fuel transfer_fuel choice)
        as [refined_choice |] eqn:Hchoice_normalize;
        try discriminate Hnormalize.
      inversion Hnormalize; subst refined.
      cbn.
      rewrite (Hchoice choice refined_choice Hchoice_normalize).
      reflexivity.
    + inversion Hnormalize; subst refined. reflexivity.
    + inversion Hnormalize; subst refined. reflexivity.
    + inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.
