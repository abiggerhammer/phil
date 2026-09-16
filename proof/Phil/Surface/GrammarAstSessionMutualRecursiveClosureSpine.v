From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionChoiceRecursiveCarrierSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Close transfer and select/offer continuation recursion into one carrier.

  The predecessor carrier opens a select/offer payload inside the recursive
  send/receive carrier, but its branch continuations still point at the older
  transfer-only recursive value.  This family makes both kinds of continuation
  point back to the same full-session carrier.  End/recursive/continue payloads
  remain at their exact certified ParseTree boundaries for later slices.
*)

Inductive Phase1SurfaceMutualRecursiveSessionSpine : Type :=
| Phase1MutualRecursiveNonreferenceSession
    (session : Phase1SurfaceMutualRecursiveNonreferenceSessionSpine)
| Phase1MutualRecursiveStaticReferenceSession
    (reference_tree : ParseTree)

with Phase1SurfaceMutualRecursiveNonreferenceSessionSpine : Type :=
| Phase1MutualRecursiveTransferSession
    (direction : Phase1SurfaceSessionTransferDirection)
    (parameter : Phase1SurfaceTermParamTypeSpine)
    (boundary : option Phase1SurfaceStaticTypeArgumentsReferenceSpine)
    (guard : option Phase1SurfacePropositionSpine)
    (continuation : Phase1SurfaceMutualRecursiveSessionSpine)
| Phase1MutualRecursiveSelectSession
    (choice : Phase1SurfaceMutualRecursiveSessionChoiceSpine)
| Phase1MutualRecursiveOfferSession
    (choice : Phase1SurfaceMutualRecursiveSessionChoiceSpine)
| Phase1MutualRecursiveEndSession
    (selected_tree : ParseTree)
| Phase1MutualRecursiveRecursiveSession
    (selected_tree : ParseTree)
| Phase1MutualRecursiveContinueSession
    (selected_tree : ParseTree)

with Phase1SurfaceMutualRecursiveSessionChoiceSpine : Type :=
| Phase1MutualRecursiveChoice
    (direction : Phase1SurfaceSessionChoiceDirection)
    (first_branch : Phase1SurfaceMutualRecursiveSessionBranchSpine)
    (rest_branches : Phase1SurfaceMutualRecursiveSessionBranchTailSpine)

with Phase1SurfaceMutualRecursiveSessionBranchSpine : Type :=
| Phase1MutualRecursiveBranch
    (label : string)
    (params : option (list Phase1SurfaceTermParamTypeSpine))
    (boundary : option Phase1SurfaceStaticTypeArgumentsReferenceSpine)
    (guard : option Phase1SurfacePropositionSpine)
    (continuation : Phase1SurfaceMutualRecursiveSessionSpine)

with Phase1SurfaceMutualRecursiveSessionBranchTailSpine : Type :=
| Phase1MutualRecursiveBranchTailNil
| Phase1MutualRecursiveBranchTailCons
    (branch : Phase1SurfaceMutualRecursiveSessionBranchSpine)
    (rest : Phase1SurfaceMutualRecursiveSessionBranchTailSpine).

Fixpoint phase1_surface_mutual_recursive_session_spine_tree
  (session : Phase1SurfaceMutualRecursiveSessionSpine) : ParseTree :=
  match session with
  | Phase1MutualRecursiveNonreferenceSession nonreference =>
      PTNonterminal "session_expression"
        (PTAlternative 0
          (phase1_surface_mutual_recursive_nonreference_session_spine_tree
            nonreference))
  | Phase1MutualRecursiveStaticReferenceSession reference_tree =>
      PTNonterminal "session_expression"
        (PTAlternative 1 reference_tree)
  end

with phase1_surface_mutual_recursive_nonreference_session_spine_tree
  (session : Phase1SurfaceMutualRecursiveNonreferenceSessionSpine)
  : ParseTree :=
  match session with
  | Phase1MutualRecursiveTransferSession
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
              phase1_surface_mutual_recursive_session_spine_tree continuation
            ]))
  | Phase1MutualRecursiveSelectSession choice =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 2
          (phase1_surface_mutual_recursive_session_choice_spine_tree choice))
  | Phase1MutualRecursiveOfferSession choice =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 3
          (phase1_surface_mutual_recursive_session_choice_spine_tree choice))
  | Phase1MutualRecursiveEndSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 4 selected_tree)
  | Phase1MutualRecursiveRecursiveSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 5 selected_tree)
  | Phase1MutualRecursiveContinueSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 6 selected_tree)
  end

with phase1_surface_mutual_recursive_session_choice_spine_tree
  (choice : Phase1SurfaceMutualRecursiveSessionChoiceSpine) : ParseTree :=
  match choice with
  | Phase1MutualRecursiveChoice direction first_branch rest_branches =>
      PTSequence
        [ PTLiteral (phase1_surface_session_choice_keyword direction);
          PTLiteral "{";
          phase1_surface_mutual_recursive_session_branch_spine_tree first_branch;
          PTRepetition
            (phase1_surface_mutual_recursive_session_branch_tail_spine_trees
              rest_branches);
          PTLiteral "}"
        ]
  end

with phase1_surface_mutual_recursive_session_branch_spine_tree
  (branch : Phase1SurfaceMutualRecursiveSessionBranchSpine) : ParseTree :=
  match branch with
  | Phase1MutualRecursiveBranch label params boundary guard continuation =>
      PTNonterminal "session_branch"
        (PTSequence
          [ phase1_surface_identifier_tree label;
            phase1_surface_session_branch_params_tree params;
            phase1_surface_boundary_refined_annotation_tree boundary;
            phase1_surface_guard_refined_annotation_tree guard;
            PTLiteral "=>";
            phase1_surface_mutual_recursive_session_spine_tree continuation
          ])
  end

with phase1_surface_mutual_recursive_session_branch_tail_spine_trees
  (branches : Phase1SurfaceMutualRecursiveSessionBranchTailSpine)
  : list ParseTree :=
  match branches with
  | Phase1MutualRecursiveBranchTailNil => []
  | Phase1MutualRecursiveBranchTailCons branch rest =>
      phase1_surface_session_branch_suffix_tree
        (phase1_surface_mutual_recursive_session_branch_spine_tree branch)
      :: phase1_surface_mutual_recursive_session_branch_tail_spine_trees rest
  end.

Definition phase1_surface_normalize_mutual_recursive_session_branch_with
  (normalize_continuation :
    Phase1SurfaceRecursiveTransferSessionSpine ->
      option Phase1SurfaceMutualRecursiveSessionSpine)
  (branch : Phase1SurfaceContinuationRefinedSessionBranchSpine)
  : option Phase1SurfaceMutualRecursiveSessionBranchSpine :=
  match
    normalize_continuation
      (phase1_continuation_refined_session_branch_continuation branch)
  with
  | Some continuation =>
      Some
        (Phase1MutualRecursiveBranch
          (phase1_continuation_refined_session_branch_label branch)
          (phase1_continuation_refined_session_branch_params branch)
          (phase1_continuation_refined_session_branch_boundary branch)
          (phase1_continuation_refined_session_branch_guard branch)
          continuation)
  | None => None
  end.

Fixpoint phase1_surface_normalize_mutual_recursive_session_branch_tail_with
  (normalize_continuation :
    Phase1SurfaceRecursiveTransferSessionSpine ->
      option Phase1SurfaceMutualRecursiveSessionSpine)
  (branches : list Phase1SurfaceContinuationRefinedSessionBranchSpine)
  : option Phase1SurfaceMutualRecursiveSessionBranchTailSpine :=
  match branches with
  | [] => Some Phase1MutualRecursiveBranchTailNil
  | branch :: rest =>
      match
        phase1_surface_normalize_mutual_recursive_session_branch_with
          normalize_continuation branch,
        phase1_surface_normalize_mutual_recursive_session_branch_tail_with
          normalize_continuation rest
      with
      | Some refined_branch, Some refined_rest =>
          Some
            (Phase1MutualRecursiveBranchTailCons
              refined_branch refined_rest)
      | _, _ => None
      end
  end.

Definition phase1_surface_normalize_mutual_recursive_session_choice_with
  (normalize_continuation :
    Phase1SurfaceRecursiveTransferSessionSpine ->
      option Phase1SurfaceMutualRecursiveSessionSpine)
  (choice : Phase1SurfaceContinuationRefinedSessionChoiceSpine)
  : option Phase1SurfaceMutualRecursiveSessionChoiceSpine :=
  match
    phase1_surface_normalize_mutual_recursive_session_branch_with
      normalize_continuation
      (phase1_continuation_refined_session_choice_first_branch choice),
    phase1_surface_normalize_mutual_recursive_session_branch_tail_with
      normalize_continuation
      (phase1_continuation_refined_session_choice_rest_branches choice)
  with
  | Some first_branch, Some rest_branches =>
      Some
        (Phase1MutualRecursiveChoice
          (phase1_continuation_refined_session_choice_direction choice)
          first_branch rest_branches)
  | _, _ => None
  end.

Fixpoint phase1_surface_normalize_mutual_recursive_session_spine_fuel
  (fuel : nat)
  (session : Phase1SurfaceChoiceRefinedRecursiveSessionSpine)
  : option Phase1SurfaceMutualRecursiveSessionSpine :=
  match fuel with
  | 0 => None
  | S remaining =>
      let normalize_continuation :=
        fun continuation : Phase1SurfaceRecursiveTransferSessionSpine =>
          match
            phase1_surface_normalize_choice_refined_recursive_session_spine_fuel
              remaining continuation
          with
          | Some step =>
              phase1_surface_normalize_mutual_recursive_session_spine_fuel
                remaining step
          | None => None
          end in
      match session with
      | Phase1ChoiceRefinedRecursiveStaticReferenceSession reference_tree =>
          Some (Phase1MutualRecursiveStaticReferenceSession reference_tree)
      | Phase1ChoiceRefinedRecursiveNonreferenceSession nonreference =>
          match nonreference with
          | Phase1ChoiceRefinedRecursiveTransferSession
              direction parameter boundary guard continuation =>
              match normalize_continuation continuation with
              | Some refined_continuation =>
                  Some
                    (Phase1MutualRecursiveNonreferenceSession
                      (Phase1MutualRecursiveTransferSession
                        direction parameter boundary guard refined_continuation))
              | None => None
              end
          | Phase1ChoiceRefinedRecursiveSelectSession choice =>
              match
                phase1_surface_normalize_mutual_recursive_session_choice_with
                  normalize_continuation choice
              with
              | Some refined_choice =>
                  Some
                    (Phase1MutualRecursiveNonreferenceSession
                      (Phase1MutualRecursiveSelectSession refined_choice))
              | None => None
              end
          | Phase1ChoiceRefinedRecursiveOfferSession choice =>
              match
                phase1_surface_normalize_mutual_recursive_session_choice_with
                  normalize_continuation choice
              with
              | Some refined_choice =>
                  Some
                    (Phase1MutualRecursiveNonreferenceSession
                      (Phase1MutualRecursiveOfferSession refined_choice))
              | None => None
              end
          | Phase1ChoiceRefinedRecursiveEndSession selected_tree =>
              Some
                (Phase1MutualRecursiveNonreferenceSession
                  (Phase1MutualRecursiveEndSession selected_tree))
          | Phase1ChoiceRefinedRecursiveRecursiveSession selected_tree =>
              Some
                (Phase1MutualRecursiveNonreferenceSession
                  (Phase1MutualRecursiveRecursiveSession selected_tree))
          | Phase1ChoiceRefinedRecursiveContinueSession selected_tree =>
              Some
                (Phase1MutualRecursiveNonreferenceSession
                  (Phase1MutualRecursiveContinueSession selected_tree))
          end
      end
  end.

Lemma phase1_surface_normalize_mutual_recursive_session_branch_with_round_trip :
  forall normalize_continuation branch refined,
    (forall continuation converted,
      normalize_continuation continuation = Some converted ->
      phase1_surface_mutual_recursive_session_spine_tree converted =
        phase1_surface_recursive_transfer_session_spine_tree continuation) ->
    phase1_surface_normalize_mutual_recursive_session_branch_with
      normalize_continuation branch = Some refined ->
    phase1_surface_mutual_recursive_session_branch_spine_tree refined =
      phase1_surface_continuation_refined_session_branch_spine_tree branch.
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
  phase1_surface_normalize_mutual_recursive_session_branch_tail_with_round_trip :
  forall normalize_continuation branches refined,
    (forall continuation converted,
      normalize_continuation continuation = Some converted ->
      phase1_surface_mutual_recursive_session_spine_tree converted =
        phase1_surface_recursive_transfer_session_spine_tree continuation) ->
    phase1_surface_normalize_mutual_recursive_session_branch_tail_with
      normalize_continuation branches = Some refined ->
    phase1_surface_mutual_recursive_session_branch_tail_spine_trees refined =
      map
        (fun branch =>
          phase1_surface_session_branch_suffix_tree
            (phase1_surface_continuation_refined_session_branch_spine_tree
              branch))
        branches.
Proof.
  intros normalize_continuation branches.
  induction branches as [|branch rest IH]; intros refined Hcontinuation Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_mutual_recursive_session_branch_with
        normalize_continuation branch)
      as [refined_branch |] eqn:Hbranch; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_mutual_recursive_session_branch_tail_with
        normalize_continuation rest)
      as [refined_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_mutual_recursive_session_branch_with_round_trip
        normalize_continuation branch refined_branch
        Hcontinuation Hbranch).
    rewrite (IH refined_rest Hcontinuation Hrest).
    reflexivity.
Qed.

Lemma phase1_surface_normalize_mutual_recursive_session_choice_with_round_trip :
  forall normalize_continuation choice refined,
    (forall continuation converted,
      normalize_continuation continuation = Some converted ->
      phase1_surface_mutual_recursive_session_spine_tree converted =
        phase1_surface_recursive_transfer_session_spine_tree continuation) ->
    phase1_surface_normalize_mutual_recursive_session_choice_with
      normalize_continuation choice = Some refined ->
    phase1_surface_mutual_recursive_session_choice_spine_tree refined =
      phase1_surface_continuation_refined_session_choice_spine_tree choice.
Proof.
  intros normalize_continuation
    [direction first_branch rest_branches]
    refined Hcontinuation Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_mutual_recursive_session_branch_with
      normalize_continuation first_branch)
    as [refined_first |] eqn:Hfirst; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_mutual_recursive_session_branch_tail_with
      normalize_continuation rest_branches)
    as [refined_rest |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_mutual_recursive_session_branch_with_round_trip
      normalize_continuation first_branch refined_first
      Hcontinuation Hfirst).
  rewrite
    (phase1_surface_normalize_mutual_recursive_session_branch_tail_with_round_trip
      normalize_continuation rest_branches refined_rest
      Hcontinuation Hrest).
  reflexivity.
Qed.

Theorem phase1_surface_normalize_mutual_recursive_session_spine_fuel_round_trip :
  forall fuel session refined,
    phase1_surface_normalize_mutual_recursive_session_spine_fuel
      fuel session = Some refined ->
    phase1_surface_mutual_recursive_session_spine_tree refined =
      phase1_surface_choice_refined_recursive_session_spine_tree session.
Proof.
  induction fuel as [|remaining IH]; intros session refined Hnormalize.
  - discriminate Hnormalize.
  - cbn in Hnormalize.
    assert (Hcontinuation :
      forall continuation converted,
        (match
          phase1_surface_normalize_choice_refined_recursive_session_spine_fuel
            remaining continuation
        with
        | Some step =>
            phase1_surface_normalize_mutual_recursive_session_spine_fuel
              remaining step
        | None => None
        end) = Some converted ->
        phase1_surface_mutual_recursive_session_spine_tree converted =
          phase1_surface_recursive_transfer_session_spine_tree continuation).
    {
      intros continuation converted Hconverted.
      destruct
        (phase1_surface_normalize_choice_refined_recursive_session_spine_fuel
          remaining continuation)
        as [step |] eqn:Hstep; try discriminate Hconverted.
      transitivity
        (phase1_surface_choice_refined_recursive_session_spine_tree step).
      - eapply IH.
        exact Hconverted.
      - eapply
          phase1_surface_normalize_choice_refined_recursive_session_spine_fuel_round_trip.
        exact Hstep.
    }
    destruct session as [nonreference | reference_tree].
    + destruct nonreference as
        [direction parameter boundary guard continuation
        |choice
        |choice
        |selected_tree
        |selected_tree
        |selected_tree].
      * cbn in Hnormalize.
        destruct
          (match
            phase1_surface_normalize_choice_refined_recursive_session_spine_fuel
              remaining continuation
          with
          | Some step =>
              phase1_surface_normalize_mutual_recursive_session_spine_fuel
                remaining step
          | None => None
          end)
          as [converted |] eqn:Hconverted; try discriminate Hnormalize.
        inversion Hnormalize; subst refined.
        cbn.
        rewrite (Hcontinuation continuation converted Hconverted).
        reflexivity.
      * cbn in Hnormalize.
        destruct
          (phase1_surface_normalize_mutual_recursive_session_choice_with
            (fun continuation =>
              match
                phase1_surface_normalize_choice_refined_recursive_session_spine_fuel
                  remaining continuation
              with
              | Some step =>
                  phase1_surface_normalize_mutual_recursive_session_spine_fuel
                    remaining step
              | None => None
              end)
            choice)
          as [converted |] eqn:Hchoice; try discriminate Hnormalize.
        inversion Hnormalize; subst refined.
        cbn.
        rewrite
          (phase1_surface_normalize_mutual_recursive_session_choice_with_round_trip
            (fun continuation =>
              match
                phase1_surface_normalize_choice_refined_recursive_session_spine_fuel
                  remaining continuation
              with
              | Some step =>
                  phase1_surface_normalize_mutual_recursive_session_spine_fuel
                    remaining step
              | None => None
              end)
            choice converted Hcontinuation Hchoice).
        reflexivity.
      * cbn in Hnormalize.
        destruct
          (phase1_surface_normalize_mutual_recursive_session_choice_with
            (fun continuation =>
              match
                phase1_surface_normalize_choice_refined_recursive_session_spine_fuel
                  remaining continuation
              with
              | Some step =>
                  phase1_surface_normalize_mutual_recursive_session_spine_fuel
                    remaining step
              | None => None
              end)
            choice)
          as [converted |] eqn:Hchoice; try discriminate Hnormalize.
        inversion Hnormalize; subst refined.
        cbn.
        rewrite
          (phase1_surface_normalize_mutual_recursive_session_choice_with_round_trip
            (fun continuation =>
              match
                phase1_surface_normalize_choice_refined_recursive_session_spine_fuel
                  remaining continuation
              with
              | Some step =>
                  phase1_surface_normalize_mutual_recursive_session_spine_fuel
                    remaining step
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
