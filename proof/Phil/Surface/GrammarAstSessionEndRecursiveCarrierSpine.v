From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionEndCarrierSpine
  GrammarAstSessionMutualRecursiveClosureSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Lift the closed `end identifier` payload through the already-closed mutual
  transfer/choice recursive session carrier.  Transfer and choice continuations
  remain mutually recursive; only the end payload changes from an exact raw
  subtree to Phase1SurfaceEndSessionSpine.  Recursive/continue payloads remain
  exact certified boundaries for their successor refinement.
*)

Inductive Phase1SurfaceEndRefinedRecursiveSessionSpine : Type :=
| Phase1EndRefinedRecursiveNonreferenceSession
    (session : Phase1SurfaceEndRefinedRecursiveNonreferenceSessionSpine)
| Phase1EndRefinedRecursiveStaticReferenceSession
    (reference_tree : ParseTree)

with Phase1SurfaceEndRefinedRecursiveNonreferenceSessionSpine : Type :=
| Phase1EndRefinedRecursiveTransferSession
    (direction : Phase1SurfaceSessionTransferDirection)
    (parameter : Phase1SurfaceTermParamTypeSpine)
    (boundary : option Phase1SurfaceStaticTypeArgumentsReferenceSpine)
    (guard : option Phase1SurfacePropositionSpine)
    (continuation : Phase1SurfaceEndRefinedRecursiveSessionSpine)
| Phase1EndRefinedRecursiveSelectSession
    (choice : Phase1SurfaceEndRefinedRecursiveSessionChoiceSpine)
| Phase1EndRefinedRecursiveOfferSession
    (choice : Phase1SurfaceEndRefinedRecursiveSessionChoiceSpine)
| Phase1EndRefinedRecursiveEndSession
    (terminal : Phase1SurfaceEndSessionSpine)
| Phase1EndRefinedRecursiveRecursiveSession
    (selected_tree : ParseTree)
| Phase1EndRefinedRecursiveContinueSession
    (selected_tree : ParseTree)

with Phase1SurfaceEndRefinedRecursiveSessionChoiceSpine : Type :=
| Phase1EndRefinedRecursiveChoice
    (direction : Phase1SurfaceSessionChoiceDirection)
    (first_branch : Phase1SurfaceEndRefinedRecursiveSessionBranchSpine)
    (rest_branches : Phase1SurfaceEndRefinedRecursiveSessionBranchTailSpine)

with Phase1SurfaceEndRefinedRecursiveSessionBranchSpine : Type :=
| Phase1EndRefinedRecursiveBranch
    (label : string)
    (params : option (list Phase1SurfaceTermParamTypeSpine))
    (boundary : option Phase1SurfaceStaticTypeArgumentsReferenceSpine)
    (guard : option Phase1SurfacePropositionSpine)
    (continuation : Phase1SurfaceEndRefinedRecursiveSessionSpine)

with Phase1SurfaceEndRefinedRecursiveSessionBranchTailSpine : Type :=
| Phase1EndRefinedRecursiveBranchTailNil
| Phase1EndRefinedRecursiveBranchTailCons
    (branch : Phase1SurfaceEndRefinedRecursiveSessionBranchSpine)
    (rest : Phase1SurfaceEndRefinedRecursiveSessionBranchTailSpine).

Fixpoint phase1_surface_end_refined_recursive_session_spine_tree
  (session : Phase1SurfaceEndRefinedRecursiveSessionSpine) : ParseTree :=
  match session with
  | Phase1EndRefinedRecursiveNonreferenceSession nonreference =>
      PTNonterminal "session_expression"
        (PTAlternative 0
          (phase1_surface_end_refined_recursive_nonreference_session_spine_tree
            nonreference))
  | Phase1EndRefinedRecursiveStaticReferenceSession reference_tree =>
      PTNonterminal "session_expression" (PTAlternative 1 reference_tree)
  end

with phase1_surface_end_refined_recursive_nonreference_session_spine_tree
  (session : Phase1SurfaceEndRefinedRecursiveNonreferenceSessionSpine)
  : ParseTree :=
  match session with
  | Phase1EndRefinedRecursiveTransferSession
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
              phase1_surface_end_refined_recursive_session_spine_tree continuation
            ]))
  | Phase1EndRefinedRecursiveSelectSession choice =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 2
          (phase1_surface_end_refined_recursive_session_choice_spine_tree choice))
  | Phase1EndRefinedRecursiveOfferSession choice =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 3
          (phase1_surface_end_refined_recursive_session_choice_spine_tree choice))
  | Phase1EndRefinedRecursiveEndSession terminal =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 4 (phase1_surface_end_session_spine_tree terminal))
  | Phase1EndRefinedRecursiveRecursiveSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 5 selected_tree)
  | Phase1EndRefinedRecursiveContinueSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 6 selected_tree)
  end

with phase1_surface_end_refined_recursive_session_choice_spine_tree
  (choice : Phase1SurfaceEndRefinedRecursiveSessionChoiceSpine) : ParseTree :=
  match choice with
  | Phase1EndRefinedRecursiveChoice direction first_branch rest_branches =>
      PTSequence
        [ PTLiteral (phase1_surface_session_choice_keyword direction);
          PTLiteral "{";
          phase1_surface_end_refined_recursive_session_branch_spine_tree first_branch;
          PTRepetition
            (phase1_surface_end_refined_recursive_session_branch_tail_spine_trees
              rest_branches);
          PTLiteral "}"
        ]
  end

with phase1_surface_end_refined_recursive_session_branch_spine_tree
  (branch : Phase1SurfaceEndRefinedRecursiveSessionBranchSpine) : ParseTree :=
  match branch with
  | Phase1EndRefinedRecursiveBranch label params boundary guard continuation =>
      PTNonterminal "session_branch"
        (PTSequence
          [ phase1_surface_identifier_tree label;
            phase1_surface_session_branch_params_tree params;
            phase1_surface_boundary_refined_annotation_tree boundary;
            phase1_surface_guard_refined_annotation_tree guard;
            PTLiteral "=>";
            phase1_surface_end_refined_recursive_session_spine_tree continuation
          ])
  end

with phase1_surface_end_refined_recursive_session_branch_tail_spine_trees
  (branches : Phase1SurfaceEndRefinedRecursiveSessionBranchTailSpine)
  : list ParseTree :=
  match branches with
  | Phase1EndRefinedRecursiveBranchTailNil => []
  | Phase1EndRefinedRecursiveBranchTailCons branch rest =>
      phase1_surface_session_branch_suffix_tree
        (phase1_surface_end_refined_recursive_session_branch_spine_tree branch)
      :: phase1_surface_end_refined_recursive_session_branch_tail_spine_trees rest
  end.

Fixpoint phase1_surface_normalize_end_refined_recursive_session_spine
  (session : Phase1SurfaceMutualRecursiveSessionSpine)
  : option Phase1SurfaceEndRefinedRecursiveSessionSpine :=
  match session with
  | Phase1MutualRecursiveNonreferenceSession nonreference =>
      match
        phase1_surface_normalize_end_refined_recursive_nonreference_session_spine
          nonreference
      with
      | Some refined =>
          Some (Phase1EndRefinedRecursiveNonreferenceSession refined)
      | None => None
      end
  | Phase1MutualRecursiveStaticReferenceSession reference_tree =>
      Some (Phase1EndRefinedRecursiveStaticReferenceSession reference_tree)
  end

with phase1_surface_normalize_end_refined_recursive_nonreference_session_spine
  (session : Phase1SurfaceMutualRecursiveNonreferenceSessionSpine)
  : option Phase1SurfaceEndRefinedRecursiveNonreferenceSessionSpine :=
  match session with
  | Phase1MutualRecursiveTransferSession
      direction parameter boundary guard continuation =>
      match phase1_surface_normalize_end_refined_recursive_session_spine continuation with
      | Some refined_continuation =>
          Some
            (Phase1EndRefinedRecursiveTransferSession
              direction parameter boundary guard refined_continuation)
      | None => None
      end
  | Phase1MutualRecursiveSelectSession choice =>
      match phase1_surface_normalize_end_refined_recursive_session_choice_spine choice with
      | Some refined_choice =>
          Some (Phase1EndRefinedRecursiveSelectSession refined_choice)
      | None => None
      end
  | Phase1MutualRecursiveOfferSession choice =>
      match phase1_surface_normalize_end_refined_recursive_session_choice_spine choice with
      | Some refined_choice =>
          Some (Phase1EndRefinedRecursiveOfferSession refined_choice)
      | None => None
      end
  | Phase1MutualRecursiveEndSession selected_tree =>
      match phase1_surface_normalize_end_session_spine selected_tree with
      | Some terminal => Some (Phase1EndRefinedRecursiveEndSession terminal)
      | None => None
      end
  | Phase1MutualRecursiveRecursiveSession selected_tree =>
      Some (Phase1EndRefinedRecursiveRecursiveSession selected_tree)
  | Phase1MutualRecursiveContinueSession selected_tree =>
      Some (Phase1EndRefinedRecursiveContinueSession selected_tree)
  end

with phase1_surface_normalize_end_refined_recursive_session_choice_spine
  (choice : Phase1SurfaceMutualRecursiveSessionChoiceSpine)
  : option Phase1SurfaceEndRefinedRecursiveSessionChoiceSpine :=
  match choice with
  | Phase1MutualRecursiveChoice direction first_branch rest_branches =>
      match
        phase1_surface_normalize_end_refined_recursive_session_branch_spine first_branch,
        phase1_surface_normalize_end_refined_recursive_session_branch_tail_spine rest_branches
      with
      | Some refined_first, Some refined_rest =>
          Some
            (Phase1EndRefinedRecursiveChoice
              direction refined_first refined_rest)
      | _, _ => None
      end
  end

with phase1_surface_normalize_end_refined_recursive_session_branch_spine
  (branch : Phase1SurfaceMutualRecursiveSessionBranchSpine)
  : option Phase1SurfaceEndRefinedRecursiveSessionBranchSpine :=
  match branch with
  | Phase1MutualRecursiveBranch label params boundary guard continuation =>
      match phase1_surface_normalize_end_refined_recursive_session_spine continuation with
      | Some refined_continuation =>
          Some
            (Phase1EndRefinedRecursiveBranch
              label params boundary guard refined_continuation)
      | None => None
      end
  end

with phase1_surface_normalize_end_refined_recursive_session_branch_tail_spine
  (branches : Phase1SurfaceMutualRecursiveSessionBranchTailSpine)
  : option Phase1SurfaceEndRefinedRecursiveSessionBranchTailSpine :=
  match branches with
  | Phase1MutualRecursiveBranchTailNil =>
      Some Phase1EndRefinedRecursiveBranchTailNil
  | Phase1MutualRecursiveBranchTailCons branch rest =>
      match
        phase1_surface_normalize_end_refined_recursive_session_branch_spine branch,
        phase1_surface_normalize_end_refined_recursive_session_branch_tail_spine rest
      with
      | Some refined_branch, Some refined_rest =>
          Some
            (Phase1EndRefinedRecursiveBranchTailCons
              refined_branch refined_rest)
      | _, _ => None
      end
  end.

Theorem phase1_surface_normalize_end_refined_recursive_session_spine_round_trip :
  forall session refined,
    phase1_surface_normalize_end_refined_recursive_session_spine session =
      Some refined ->
    phase1_surface_end_refined_recursive_session_spine_tree refined =
      phase1_surface_mutual_recursive_session_spine_tree session.
Proof.
  fix IH_session 1.
  intros session refined Hnormalize.
  assert (Hbranch :
    forall branch refined_branch,
      phase1_surface_normalize_end_refined_recursive_session_branch_spine branch =
        Some refined_branch ->
      phase1_surface_end_refined_recursive_session_branch_spine_tree
        refined_branch =
      phase1_surface_mutual_recursive_session_branch_spine_tree branch).
  {
    intros [label params boundary guard continuation]
      refined_branch Hbranch_normalize.
    cbn in Hbranch_normalize.
    destruct
      (phase1_surface_normalize_end_refined_recursive_session_spine continuation)
      as [refined_continuation |] eqn:Hcontinuation;
      try discriminate Hbranch_normalize.
    inversion Hbranch_normalize; subst refined_branch.
    cbn.
    rewrite (IH_session continuation refined_continuation Hcontinuation).
    reflexivity.
  }
  assert (Htail :
    forall branches refined_branches,
      phase1_surface_normalize_end_refined_recursive_session_branch_tail_spine
        branches = Some refined_branches ->
      phase1_surface_end_refined_recursive_session_branch_tail_spine_trees
        refined_branches =
      phase1_surface_mutual_recursive_session_branch_tail_spine_trees branches).
  {
    intros branches.
    induction branches as [|branch rest IHrest];
      intros refined_branches Htail_normalize.
    - cbn in Htail_normalize.
      inversion Htail_normalize; subst refined_branches.
      reflexivity.
    - cbn in Htail_normalize.
      destruct
        (phase1_surface_normalize_end_refined_recursive_session_branch_spine branch)
        as [refined_branch |] eqn:Hbranch_normalize;
        try discriminate Htail_normalize.
      destruct
        (phase1_surface_normalize_end_refined_recursive_session_branch_tail_spine rest)
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
      phase1_surface_normalize_end_refined_recursive_session_choice_spine choice =
        Some refined_choice ->
      phase1_surface_end_refined_recursive_session_choice_spine_tree
        refined_choice =
      phase1_surface_mutual_recursive_session_choice_spine_tree choice).
  {
    intros [direction first_branch rest_branches]
      refined_choice Hchoice_normalize.
    cbn in Hchoice_normalize.
    destruct
      (phase1_surface_normalize_end_refined_recursive_session_branch_spine
        first_branch)
      as [refined_first |] eqn:Hfirst;
      try discriminate Hchoice_normalize.
    destruct
      (phase1_surface_normalize_end_refined_recursive_session_branch_tail_spine
        rest_branches)
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
      |selected_tree
      |selected_tree
      |selected_tree].
    + cbn in Hnormalize.
      destruct
        (phase1_surface_normalize_end_refined_recursive_session_spine continuation)
        as [refined_continuation |] eqn:Hcontinuation;
        try discriminate Hnormalize.
      inversion Hnormalize; subst refined.
      cbn.
      rewrite (IH_session continuation refined_continuation Hcontinuation).
      reflexivity.
    + cbn in Hnormalize.
      destruct
        (phase1_surface_normalize_end_refined_recursive_session_choice_spine choice)
        as [refined_choice |] eqn:Hchoice_normalize;
        try discriminate Hnormalize.
      inversion Hnormalize; subst refined.
      cbn.
      rewrite (Hchoice choice refined_choice Hchoice_normalize).
      reflexivity.
    + cbn in Hnormalize.
      destruct
        (phase1_surface_normalize_end_refined_recursive_session_choice_spine choice)
        as [refined_choice |] eqn:Hchoice_normalize;
        try discriminate Hnormalize.
      inversion Hnormalize; subst refined.
      cbn.
      rewrite (Hchoice choice refined_choice Hchoice_normalize).
      reflexivity.
    + cbn in Hnormalize.
      destruct (phase1_surface_normalize_end_session_spine selected_tree)
        as [terminal |] eqn:Hterminal; try discriminate Hnormalize.
      inversion Hnormalize; subst refined.
      cbn.
      rewrite
        (phase1_surface_normalize_end_session_spine_round_trip
          selected_tree terminal Hterminal).
      reflexivity.
    + inversion Hnormalize; subst refined.
      reflexivity.
    + inversion Hnormalize; subst refined.
      reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.
