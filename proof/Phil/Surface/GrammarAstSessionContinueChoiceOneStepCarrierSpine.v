From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionContinueTransferRecursiveCarrierSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Compose the transfer-recursive `continue identifier` carrier with one layer
  of select/offer branch continuations.

  A branch continuation is normalized through the already-closed transfer-
  recursive carrier. Nested select/offer choices reached from that continuation
  remain at their existing end-refined boundary. This is deliberately a one-
  step composition layer; mutual transfer/choice closure remains a successor.
*)

Inductive Phase1SurfaceContinueChoiceOneStepSessionSpine : Type :=
| Phase1ContinueChoiceOneStepNonreferenceSession
    (session : Phase1SurfaceContinueChoiceOneStepNonreferenceSessionSpine)
| Phase1ContinueChoiceOneStepStaticReferenceSession
    (reference_tree : ParseTree)

with Phase1SurfaceContinueChoiceOneStepNonreferenceSessionSpine : Type :=
| Phase1ContinueChoiceOneStepTransferSession
    (direction : Phase1SurfaceSessionTransferDirection)
    (parameter : Phase1SurfaceTermParamTypeSpine)
    (boundary : option Phase1SurfaceStaticTypeArgumentsReferenceSpine)
    (guard : option Phase1SurfacePropositionSpine)
    (continuation : Phase1SurfaceContinueTransferRecursiveSessionSpine)
| Phase1ContinueChoiceOneStepSelectSession
    (choice : Phase1SurfaceContinueChoiceOneStepSessionChoiceSpine)
| Phase1ContinueChoiceOneStepOfferSession
    (choice : Phase1SurfaceContinueChoiceOneStepSessionChoiceSpine)
| Phase1ContinueChoiceOneStepEndSession
    (terminal : Phase1SurfaceEndSessionSpine)
| Phase1ContinueChoiceOneStepRecursiveSession
    (selected_tree : ParseTree)
| Phase1ContinueChoiceOneStepContinueSession
    (payload : Phase1SurfaceContinueSessionPayloadSpine)

with Phase1SurfaceContinueChoiceOneStepSessionChoiceSpine : Type :=
| Phase1ContinueChoiceOneStepChoice
    (direction : Phase1SurfaceSessionChoiceDirection)
    (first_branch : Phase1SurfaceContinueChoiceOneStepSessionBranchSpine)
    (rest_branches : Phase1SurfaceContinueChoiceOneStepSessionBranchTailSpine)

with Phase1SurfaceContinueChoiceOneStepSessionBranchSpine : Type :=
| Phase1ContinueChoiceOneStepBranch
    (label : string)
    (params : option (list Phase1SurfaceTermParamTypeSpine))
    (boundary : option Phase1SurfaceStaticTypeArgumentsReferenceSpine)
    (guard : option Phase1SurfacePropositionSpine)
    (continuation : Phase1SurfaceContinueTransferRecursiveSessionSpine)

with Phase1SurfaceContinueChoiceOneStepSessionBranchTailSpine : Type :=
| Phase1ContinueChoiceOneStepBranchTailNil
| Phase1ContinueChoiceOneStepBranchTailCons
    (branch : Phase1SurfaceContinueChoiceOneStepSessionBranchSpine)
    (rest : Phase1SurfaceContinueChoiceOneStepSessionBranchTailSpine).

Fixpoint phase1_surface_continue_choice_one_step_session_spine_tree
  (session : Phase1SurfaceContinueChoiceOneStepSessionSpine) : ParseTree :=
  match session with
  | Phase1ContinueChoiceOneStepNonreferenceSession nonreference =>
      PTNonterminal "session_expression"
        (PTAlternative 0
          (phase1_surface_continue_choice_one_step_nonreference_session_spine_tree
            nonreference))
  | Phase1ContinueChoiceOneStepStaticReferenceSession reference_tree =>
      PTNonterminal "session_expression" (PTAlternative 1 reference_tree)
  end

with phase1_surface_continue_choice_one_step_nonreference_session_spine_tree
  (session : Phase1SurfaceContinueChoiceOneStepNonreferenceSessionSpine)
  : ParseTree :=
  match session with
  | Phase1ContinueChoiceOneStepTransferSession
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
  | Phase1ContinueChoiceOneStepSelectSession choice =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 2
          (phase1_surface_continue_choice_one_step_session_choice_spine_tree choice))
  | Phase1ContinueChoiceOneStepOfferSession choice =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 3
          (phase1_surface_continue_choice_one_step_session_choice_spine_tree choice))
  | Phase1ContinueChoiceOneStepEndSession terminal =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 4 (phase1_surface_end_session_spine_tree terminal))
  | Phase1ContinueChoiceOneStepRecursiveSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 5 selected_tree)
  | Phase1ContinueChoiceOneStepContinueSession payload =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 6
          (phase1_surface_continue_session_payload_spine_tree payload))
  end

with phase1_surface_continue_choice_one_step_session_choice_spine_tree
  (choice : Phase1SurfaceContinueChoiceOneStepSessionChoiceSpine) : ParseTree :=
  match choice with
  | Phase1ContinueChoiceOneStepChoice direction first_branch rest_branches =>
      PTSequence
        [ PTLiteral (phase1_surface_session_choice_keyword direction);
          PTLiteral "{";
          phase1_surface_continue_choice_one_step_session_branch_spine_tree first_branch;
          PTRepetition
            (phase1_surface_continue_choice_one_step_session_branch_tail_spine_trees
              rest_branches);
          PTLiteral "}"
        ]
  end

with phase1_surface_continue_choice_one_step_session_branch_spine_tree
  (branch : Phase1SurfaceContinueChoiceOneStepSessionBranchSpine) : ParseTree :=
  match branch with
  | Phase1ContinueChoiceOneStepBranch label params boundary guard continuation =>
      PTNonterminal "session_branch"
        (PTSequence
          [ phase1_surface_identifier_tree label;
            phase1_surface_session_branch_params_tree params;
            phase1_surface_boundary_refined_annotation_tree boundary;
            phase1_surface_guard_refined_annotation_tree guard;
            PTLiteral "=>";
            phase1_surface_continue_transfer_recursive_session_spine_tree continuation
          ])
  end

with phase1_surface_continue_choice_one_step_session_branch_tail_spine_trees
  (branches : Phase1SurfaceContinueChoiceOneStepSessionBranchTailSpine)
  : list ParseTree :=
  match branches with
  | Phase1ContinueChoiceOneStepBranchTailNil => []
  | Phase1ContinueChoiceOneStepBranchTailCons branch rest =>
      phase1_surface_session_branch_suffix_tree
        (phase1_surface_continue_choice_one_step_session_branch_spine_tree branch)
      :: phase1_surface_continue_choice_one_step_session_branch_tail_spine_trees rest
  end.

Fixpoint phase1_surface_normalize_continue_choice_one_step_session_spine
  (session : Phase1SurfaceContinueTransferRecursiveSessionSpine)
  : option Phase1SurfaceContinueChoiceOneStepSessionSpine :=
  match session with
  | Phase1ContinueTransferRecursiveNonreferenceSession nonreference =>
      match
        phase1_surface_normalize_continue_choice_one_step_nonreference_session_spine
          nonreference
      with
      | Some refined => Some (Phase1ContinueChoiceOneStepNonreferenceSession refined)
      | None => None
      end
  | Phase1ContinueTransferRecursiveStaticReferenceSession reference_tree =>
      Some (Phase1ContinueChoiceOneStepStaticReferenceSession reference_tree)
  end

with phase1_surface_normalize_continue_choice_one_step_nonreference_session_spine
  (session : Phase1SurfaceContinueTransferRecursiveNonreferenceSessionSpine)
  : option Phase1SurfaceContinueChoiceOneStepNonreferenceSessionSpine :=
  match session with
  | Phase1ContinueTransferRecursiveTransferSession
      direction parameter boundary guard continuation =>
      Some
        (Phase1ContinueChoiceOneStepTransferSession
          direction parameter boundary guard continuation)
  | Phase1ContinueTransferRecursiveSelectSession choice =>
      match phase1_surface_normalize_continue_choice_one_step_session_choice_spine choice with
      | Some refined_choice =>
          Some (Phase1ContinueChoiceOneStepSelectSession refined_choice)
      | None => None
      end
  | Phase1ContinueTransferRecursiveOfferSession choice =>
      match phase1_surface_normalize_continue_choice_one_step_session_choice_spine choice with
      | Some refined_choice =>
          Some (Phase1ContinueChoiceOneStepOfferSession refined_choice)
      | None => None
      end
  | Phase1ContinueTransferRecursiveEndSession terminal =>
      Some (Phase1ContinueChoiceOneStepEndSession terminal)
  | Phase1ContinueTransferRecursiveRecursiveSession selected_tree =>
      Some (Phase1ContinueChoiceOneStepRecursiveSession selected_tree)
  | Phase1ContinueTransferRecursiveContinueSession payload =>
      Some (Phase1ContinueChoiceOneStepContinueSession payload)
  end

with phase1_surface_normalize_continue_choice_one_step_session_choice_spine
  (choice : Phase1SurfaceEndRefinedRecursiveSessionChoiceSpine)
  : option Phase1SurfaceContinueChoiceOneStepSessionChoiceSpine :=
  match choice with
  | Phase1EndRefinedRecursiveChoice direction first_branch rest_branches =>
      match
        phase1_surface_normalize_continue_choice_one_step_session_branch_spine first_branch,
        phase1_surface_normalize_continue_choice_one_step_session_branch_tail_spine rest_branches
      with
      | Some refined_first, Some refined_rest =>
          Some
            (Phase1ContinueChoiceOneStepChoice
              direction refined_first refined_rest)
      | _, _ => None
      end
  end

with phase1_surface_normalize_continue_choice_one_step_session_branch_spine
  (branch : Phase1SurfaceEndRefinedRecursiveSessionBranchSpine)
  : option Phase1SurfaceContinueChoiceOneStepSessionBranchSpine :=
  match branch with
  | Phase1EndRefinedRecursiveBranch label params boundary guard continuation =>
      match phase1_surface_normalize_continue_transfer_recursive_session_spine continuation with
      | Some refined_continuation =>
          Some
            (Phase1ContinueChoiceOneStepBranch
              label params boundary guard refined_continuation)
      | None => None
      end
  end

with phase1_surface_normalize_continue_choice_one_step_session_branch_tail_spine
  (branches : Phase1SurfaceEndRefinedRecursiveSessionBranchTailSpine)
  : option Phase1SurfaceContinueChoiceOneStepSessionBranchTailSpine :=
  match branches with
  | Phase1EndRefinedRecursiveBranchTailNil =>
      Some Phase1ContinueChoiceOneStepBranchTailNil
  | Phase1EndRefinedRecursiveBranchTailCons branch rest =>
      match
        phase1_surface_normalize_continue_choice_one_step_session_branch_spine branch,
        phase1_surface_normalize_continue_choice_one_step_session_branch_tail_spine rest
      with
      | Some refined_branch, Some refined_rest =>
          Some
            (Phase1ContinueChoiceOneStepBranchTailCons
              refined_branch refined_rest)
      | _, _ => None
      end
  end.

Theorem phase1_surface_normalize_continue_choice_one_step_session_spine_round_trip :
  forall session refined,
    phase1_surface_normalize_continue_choice_one_step_session_spine session =
      Some refined ->
    phase1_surface_continue_choice_one_step_session_spine_tree refined =
      phase1_surface_continue_transfer_recursive_session_spine_tree session.
Proof.
  intros session refined Hnormalize.
  assert (Hbranch :
    forall branch refined_branch,
      phase1_surface_normalize_continue_choice_one_step_session_branch_spine branch =
        Some refined_branch ->
      phase1_surface_continue_choice_one_step_session_branch_spine_tree
        refined_branch =
      phase1_surface_end_refined_recursive_session_branch_spine_tree branch).
  {
    intros [label params boundary guard continuation]
      refined_branch Hbranch_normalize.
    cbn in Hbranch_normalize.
    destruct
      (phase1_surface_normalize_continue_transfer_recursive_session_spine continuation)
      as [refined_continuation |] eqn:Hcontinuation;
      try discriminate Hbranch_normalize.
    inversion Hbranch_normalize; subst refined_branch.
    cbn.
    rewrite
      (phase1_surface_normalize_continue_transfer_recursive_session_spine_round_trip
        continuation refined_continuation Hcontinuation).
    reflexivity.
  }
  assert (Htail :
    forall branches refined_branches,
      phase1_surface_normalize_continue_choice_one_step_session_branch_tail_spine
        branches = Some refined_branches ->
      phase1_surface_continue_choice_one_step_session_branch_tail_spine_trees
        refined_branches =
      phase1_surface_end_refined_recursive_session_branch_tail_spine_trees branches).
  {
    intros branches.
    induction branches as [|branch rest IHrest];
      intros refined_branches Htail_normalize.
    - cbn in Htail_normalize.
      inversion Htail_normalize; subst refined_branches.
      reflexivity.
    - cbn in Htail_normalize.
      destruct
        (phase1_surface_normalize_continue_choice_one_step_session_branch_spine branch)
        as [refined_branch |] eqn:Hbranch_normalize;
        try discriminate Htail_normalize.
      destruct
        (phase1_surface_normalize_continue_choice_one_step_session_branch_tail_spine rest)
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
      phase1_surface_normalize_continue_choice_one_step_session_choice_spine choice =
        Some refined_choice ->
      phase1_surface_continue_choice_one_step_session_choice_spine_tree
        refined_choice =
      phase1_surface_end_refined_recursive_session_choice_spine_tree choice).
  {
    intros [direction first_branch rest_branches]
      refined_choice Hchoice_normalize.
    cbn in Hchoice_normalize.
    destruct
      (phase1_surface_normalize_continue_choice_one_step_session_branch_spine first_branch)
      as [refined_first |] eqn:Hfirst;
      try discriminate Hchoice_normalize.
    destruct
      (phase1_surface_normalize_continue_choice_one_step_session_branch_tail_spine rest_branches)
      as [refined_rest |] eqn:Hrest;
      try discriminate Hchoice_normalize.
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
      |selected_tree
      |payload].
    + inversion Hnormalize; subst refined. reflexivity.
    + cbn in Hnormalize.
      destruct
        (phase1_surface_normalize_continue_choice_one_step_session_choice_spine choice)
        as [refined_choice |] eqn:Hchoice_normalize;
        try discriminate Hnormalize.
      inversion Hnormalize; subst refined.
      cbn.
      rewrite (Hchoice choice refined_choice Hchoice_normalize).
      reflexivity.
    + cbn in Hnormalize.
      destruct
        (phase1_surface_normalize_continue_choice_one_step_session_choice_spine choice)
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
