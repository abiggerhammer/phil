From Stdlib Require Import Arith.PeanoNat Lists.List Strings.String Lia.

From Phil.Surface Require Import
  GrammarAstSessionContinueMutualRecursiveClosureSpine
  GrammarAstSessionContinueChoiceOneStepCarrierTotality
  GrammarAstSessionContinueTransferRecursiveCarrierTotality
  GrammarAstSessionMutualRecursiveClosureTotality
  GrammarAstSessionTransferRecursiveClosureTotality
  GrammarAstSessionBranchTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse and finite-fuel closure for the continue-refined mutual carrier. *)

Definition phase1_surface_normalize_continue_mutual_recursive_continuation_fuel
  (fuel : nat)
  (continuation : Phase1SurfaceContinueTransferRecursiveSessionSpine)
  : option Phase1SurfaceContinueMutualRecursiveSessionSpine :=
  match
    phase1_surface_normalize_continue_choice_one_step_session_spine continuation
  with
  | Some step =>
      phase1_surface_normalize_continue_mutual_recursive_session_spine_fuel
        fuel step
  | None => None
  end.

Lemma
  phase1_surface_normalize_continue_mutual_recursive_session_branch_with_respects :
  forall normalize_left normalize_right branch refined,
    (forall continuation converted,
      normalize_left continuation = Some converted ->
      normalize_right continuation = Some converted) ->
    phase1_surface_normalize_continue_mutual_recursive_session_branch_with
      normalize_left branch = Some refined ->
    phase1_surface_normalize_continue_mutual_recursive_session_branch_with
      normalize_right branch = Some refined.
Proof.
  intros normalize_left normalize_right
    [label params boundary guard continuation] refined Hrespect Hnormalize.
  cbn in Hnormalize |- *.
  destruct (normalize_left continuation)
    as [converted |] eqn:Hconverted; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  rewrite (Hrespect continuation converted Hconverted).
  reflexivity.
Qed.

Lemma
  phase1_surface_normalize_continue_mutual_recursive_session_branch_tail_with_respects :
  forall normalize_left normalize_right branches refined,
    (forall continuation converted,
      normalize_left continuation = Some converted ->
      normalize_right continuation = Some converted) ->
    phase1_surface_normalize_continue_mutual_recursive_session_branch_tail_with
      normalize_left branches = Some refined ->
    phase1_surface_normalize_continue_mutual_recursive_session_branch_tail_with
      normalize_right branches = Some refined.
Proof.
  intros normalize_left normalize_right branches.
  induction branches as [|branch rest IH];
    intros refined Hrespect Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize |- *.
    destruct
      (phase1_surface_normalize_continue_mutual_recursive_session_branch_with
        normalize_left branch)
      as [refined_branch |] eqn:Hbranch; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_continue_mutual_recursive_session_branch_tail_with
        normalize_left rest)
      as [refined_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    rewrite
      (phase1_surface_normalize_continue_mutual_recursive_session_branch_with_respects
        normalize_left normalize_right branch refined_branch
        Hrespect Hbranch).
    rewrite (IH refined_rest Hrespect Hrest).
    reflexivity.
Qed.

Lemma
  phase1_surface_normalize_continue_mutual_recursive_session_choice_with_respects :
  forall normalize_left normalize_right choice refined,
    (forall continuation converted,
      normalize_left continuation = Some converted ->
      normalize_right continuation = Some converted) ->
    phase1_surface_normalize_continue_mutual_recursive_session_choice_with
      normalize_left choice = Some refined ->
    phase1_surface_normalize_continue_mutual_recursive_session_choice_with
      normalize_right choice = Some refined.
Proof.
  intros normalize_left normalize_right
    [direction first_branch rest_branches] refined Hrespect Hnormalize.
  cbn in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_continue_mutual_recursive_session_branch_with
      normalize_left first_branch)
    as [refined_first |] eqn:Hfirst; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_continue_mutual_recursive_session_branch_tail_with
      normalize_left rest_branches)
    as [refined_rest |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  rewrite
    (phase1_surface_normalize_continue_mutual_recursive_session_branch_with_respects
      normalize_left normalize_right first_branch refined_first
      Hrespect Hfirst).
  rewrite
    (phase1_surface_normalize_continue_mutual_recursive_session_branch_tail_with_respects
      normalize_left normalize_right rest_branches refined_rest
      Hrespect Hrest).
  reflexivity.
Qed.

Lemma
  phase1_surface_normalize_continue_mutual_recursive_session_spine_fuel_monotone :
  forall fuel larger session refined,
    fuel <= larger ->
    phase1_surface_normalize_continue_mutual_recursive_session_spine_fuel
      fuel session = Some refined ->
    phase1_surface_normalize_continue_mutual_recursive_session_spine_fuel
      larger session = Some refined.
Proof.
  induction fuel as [|fuel IH];
    intros larger session refined Hle Hnormalize.
  - discriminate Hnormalize.
  - destruct larger as [|larger].
    + lia.
    + assert (Hremaining : fuel <= larger) by lia.
      assert (Hcontinuation :
        forall continuation converted,
          phase1_surface_normalize_continue_mutual_recursive_continuation_fuel
            fuel continuation = Some converted ->
          phase1_surface_normalize_continue_mutual_recursive_continuation_fuel
            larger continuation = Some converted).
      {
        intros continuation converted Hconverted.
        unfold
          phase1_surface_normalize_continue_mutual_recursive_continuation_fuel
          in Hconverted |- *.
        destruct
          (phase1_surface_normalize_continue_choice_one_step_session_spine
            continuation)
          as [step |] eqn:Hstep; try discriminate Hconverted.
        eapply IH.
        - exact Hremaining.
        - exact Hconverted.
      }
      destruct session as [nonreference | reference_tree].
      * destruct nonreference as
          [direction parameter boundary guard continuation
          |choice
          |choice
          |terminal
          |selected_tree
          |payload].
        -- cbn [phase1_surface_normalize_continue_mutual_recursive_session_spine_fuel]
             in Hnormalize |- *.
           fold phase1_surface_normalize_continue_mutual_recursive_continuation_fuel
             in Hnormalize |- *.
           destruct
             (phase1_surface_normalize_continue_mutual_recursive_continuation_fuel
               fuel continuation)
             as [converted |] eqn:Hconverted; try discriminate Hnormalize.
           inversion Hnormalize; subst refined.
           rewrite (Hcontinuation continuation converted Hconverted).
           reflexivity.
        -- cbn [phase1_surface_normalize_continue_mutual_recursive_session_spine_fuel]
             in Hnormalize |- *.
           fold phase1_surface_normalize_continue_mutual_recursive_continuation_fuel
             in Hnormalize |- *.
           destruct
             (phase1_surface_normalize_continue_mutual_recursive_session_choice_with
               (phase1_surface_normalize_continue_mutual_recursive_continuation_fuel fuel)
               choice)
             as [converted |] eqn:Hchoice; try discriminate Hnormalize.
           inversion Hnormalize; subst refined.
           pose proof
             (phase1_surface_normalize_continue_mutual_recursive_session_choice_with_respects
               (phase1_surface_normalize_continue_mutual_recursive_continuation_fuel fuel)
               (phase1_surface_normalize_continue_mutual_recursive_continuation_fuel larger)
               choice converted Hcontinuation Hchoice)
             as Hchoice_larger.
           rewrite Hchoice_larger.
           reflexivity.
        -- cbn [phase1_surface_normalize_continue_mutual_recursive_session_spine_fuel]
             in Hnormalize |- *.
           fold phase1_surface_normalize_continue_mutual_recursive_continuation_fuel
             in Hnormalize |- *.
           destruct
             (phase1_surface_normalize_continue_mutual_recursive_session_choice_with
               (phase1_surface_normalize_continue_mutual_recursive_continuation_fuel fuel)
               choice)
             as [converted |] eqn:Hchoice; try discriminate Hnormalize.
           inversion Hnormalize; subst refined.
           pose proof
             (phase1_surface_normalize_continue_mutual_recursive_session_choice_with_respects
               (phase1_surface_normalize_continue_mutual_recursive_continuation_fuel fuel)
               (phase1_surface_normalize_continue_mutual_recursive_continuation_fuel larger)
               choice converted Hcontinuation Hchoice)
             as Hchoice_larger.
           rewrite Hchoice_larger.
           reflexivity.
        -- inversion Hnormalize; subst refined. reflexivity.
        -- inversion Hnormalize; subst refined. reflexivity.
        -- inversion Hnormalize; subst refined. reflexivity.
      * inversion Hnormalize; subst refined.
        reflexivity.
Qed.

Lemma
  phase1_surface_normalize_continue_mutual_recursive_continuation_fuel_monotone :
  forall fuel larger continuation refined,
    fuel <= larger ->
    phase1_surface_normalize_continue_mutual_recursive_continuation_fuel
      fuel continuation = Some refined ->
    phase1_surface_normalize_continue_mutual_recursive_continuation_fuel
      larger continuation = Some refined.
Proof.
  intros fuel larger continuation refined Hle Hnormalize.
  unfold phase1_surface_normalize_continue_mutual_recursive_continuation_fuel
    in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_continue_choice_one_step_session_spine continuation)
    as [step |] eqn:Hstep; try discriminate Hnormalize.
  eapply
    phase1_surface_normalize_continue_mutual_recursive_session_spine_fuel_monotone.
  - exact Hle.
  - exact Hnormalize.
Qed.

Definition phase1_surface_normalize_continue_mutual_recursive_session_branch_fuel
  (fuel : nat)
  (branch : Phase1SurfaceContinueChoiceOneStepSessionBranchSpine)
  : option Phase1SurfaceContinueMutualRecursiveSessionBranchSpine :=
  phase1_surface_normalize_continue_mutual_recursive_session_branch_with
    (phase1_surface_normalize_continue_mutual_recursive_continuation_fuel fuel)
    branch.

Definition
  phase1_surface_normalize_continue_mutual_recursive_session_branch_tail_fuel
  (fuel : nat)
  (branches : Phase1SurfaceContinueChoiceOneStepSessionBranchTailSpine)
  : option Phase1SurfaceContinueMutualRecursiveSessionBranchTailSpine :=
  phase1_surface_normalize_continue_mutual_recursive_session_branch_tail_with
    (phase1_surface_normalize_continue_mutual_recursive_continuation_fuel fuel)
    branches.

Definition phase1_surface_normalize_continue_mutual_recursive_session_choice_fuel
  (fuel : nat)
  (choice : Phase1SurfaceContinueChoiceOneStepSessionChoiceSpine)
  : option Phase1SurfaceContinueMutualRecursiveSessionChoiceSpine :=
  phase1_surface_normalize_continue_mutual_recursive_session_choice_with
    (phase1_surface_normalize_continue_mutual_recursive_continuation_fuel fuel)
    choice.

Lemma
  phase1_surface_normalize_continue_mutual_recursive_session_branch_fuel_monotone :
  forall fuel larger branch refined,
    fuel <= larger ->
    phase1_surface_normalize_continue_mutual_recursive_session_branch_fuel
      fuel branch = Some refined ->
    phase1_surface_normalize_continue_mutual_recursive_session_branch_fuel
      larger branch = Some refined.
Proof.
  intros fuel larger branch refined Hle Hnormalize.
  unfold phase1_surface_normalize_continue_mutual_recursive_session_branch_fuel
    in Hnormalize |- *.
  eapply
    phase1_surface_normalize_continue_mutual_recursive_session_branch_with_respects.
  - intros continuation converted Hconverted.
    eapply
      phase1_surface_normalize_continue_mutual_recursive_continuation_fuel_monotone.
    + exact Hle.
    + exact Hconverted.
  - exact Hnormalize.
Qed.

Lemma
  phase1_surface_normalize_continue_mutual_recursive_session_branch_tail_fuel_monotone :
  forall fuel larger branches refined,
    fuel <= larger ->
    phase1_surface_normalize_continue_mutual_recursive_session_branch_tail_fuel
      fuel branches = Some refined ->
    phase1_surface_normalize_continue_mutual_recursive_session_branch_tail_fuel
      larger branches = Some refined.
Proof.
  intros fuel larger branches refined Hle Hnormalize.
  unfold
    phase1_surface_normalize_continue_mutual_recursive_session_branch_tail_fuel
    in Hnormalize |- *.
  eapply
    phase1_surface_normalize_continue_mutual_recursive_session_branch_tail_with_respects.
  - intros continuation converted Hconverted.
    eapply
      phase1_surface_normalize_continue_mutual_recursive_continuation_fuel_monotone.
    + exact Hle.
    + exact Hconverted.
  - exact Hnormalize.
Qed.

Lemma
  phase1_surface_normalize_continue_mutual_recursive_session_choice_fuel_monotone :
  forall fuel larger choice refined,
    fuel <= larger ->
    phase1_surface_normalize_continue_mutual_recursive_session_choice_fuel
      fuel choice = Some refined ->
    phase1_surface_normalize_continue_mutual_recursive_session_choice_fuel
      larger choice = Some refined.
Proof.
  intros fuel larger choice refined Hle Hnormalize.
  unfold phase1_surface_normalize_continue_mutual_recursive_session_choice_fuel
    in Hnormalize |- *.
  eapply
    phase1_surface_normalize_continue_mutual_recursive_session_choice_with_respects.
  - intros continuation converted Hconverted.
    eapply
      phase1_surface_normalize_continue_mutual_recursive_continuation_fuel_monotone.
    + exact Hle.
    + exact Hconverted.
  - exact Hnormalize.
Qed.

Lemma phase1_surface_continue_choice_one_step_branch_exposes_continuation :
  forall path input rest branch,
    Derives phase1_surface_rules path
      (ENonterminal "session_branch") input rest
      (phase1_surface_continue_choice_one_step_session_branch_spine_tree branch) ->
    exists continuation_path continuation_input continuation_rest,
      Derives phase1_surface_rules continuation_path
        (ENonterminal "session_expression")
        continuation_input continuation_rest
        (phase1_surface_continue_transfer_recursive_session_spine_tree
          (match branch with
           | Phase1ContinueChoiceOneStepBranch _ _ _ _ continuation => continuation
           end)) /\
      List.length continuation_input <= List.length input.
Proof.
  intros path input rest
    [label params boundary guard continuation] Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "session_branch" input rest
      (phase1_surface_continue_choice_one_step_session_branch_spine_tree
        (Phase1ContinueChoiceOneStepBranch
          label params boundary guard continuation))
      Hderive)
    as [body [subtree [Hlookup [Hnode Hbody]]]].
  rewrite phase1_surface_session_branch_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  unfold phase1_surface_session_branch_expression_for_totality in Hbody.
  cbn in Hnode.
  inversion Hnode; subst subtree.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "session_branch"))
      [ ENonterminal "identifier";
        phase1_surface_session_branch_params_expression_for_totality;
        phase1_surface_session_branch_boundary_expression_for_totality;
        phase1_surface_session_branch_guard_expression_for_totality;
        ELiteral "=>";
        ENonterminal "session_expression"
      ]
      input rest
      (PTSequence
        [ phase1_surface_identifier_tree label;
          phase1_surface_session_branch_params_tree params;
          phase1_surface_boundary_refined_annotation_tree boundary;
          phase1_surface_guard_refined_annotation_tree guard;
          PTLiteral "=>";
          phase1_surface_continue_transfer_recursive_session_spine_tree
            continuation
        ])
      Hbody)
    as [trees [Htree Hitems]].
  cbn in Htree.
  inversion Htree; subst trees.
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hcontinuation : Derives phase1_surface_rules ?continuation_path
      (ENonterminal "session_expression")
      ?continuation_input ?continuation_rest
      (phase1_surface_continue_transfer_recursive_session_spine_tree
        continuation) |- _ =>
      exists continuation_path, continuation_input, continuation_rest;
      split;
      [ exact Hcontinuation
      | pose proof
          (phase1_surface_derivation_rest_length_le_input
            _ _ _ _ _ Hcontinuation) as Hlength;
        lia ]
  end.
Qed.

Lemma
  phase1_surface_normalize_continue_mutual_recursive_session_branch_fuel_total_from_derivation :
  forall parent_length path input rest branch,
    List.length input < parent_length ->
    Derives phase1_surface_rules path
      (ENonterminal "session_branch") input rest
      (phase1_surface_continue_choice_one_step_session_branch_spine_tree branch) ->
    (forall continuation_path continuation_input continuation_rest continuation,
      List.length continuation_input < parent_length ->
      Derives phase1_surface_rules continuation_path
        (ENonterminal "session_expression")
        continuation_input continuation_rest
        (phase1_surface_continue_transfer_recursive_session_spine_tree continuation) ->
      exists fuel converted,
        phase1_surface_normalize_continue_mutual_recursive_continuation_fuel
          fuel continuation = Some converted) ->
    exists fuel refined,
      phase1_surface_normalize_continue_mutual_recursive_session_branch_fuel
        fuel branch = Some refined.
Proof.
  intros parent_length path input rest branch Hinput Hderive Hsolver.
  destruct
    (phase1_surface_continue_choice_one_step_branch_exposes_continuation
      path input rest branch Hderive)
    as [continuation_path [continuation_input [continuation_rest
      [Hcontinuation Hcontinuation_length]]]].
  assert (Hcontinuation_bound :
    List.length continuation_input < parent_length) by lia.
  destruct
    (Hsolver continuation_path continuation_input continuation_rest
      (match branch with
       | Phase1ContinueChoiceOneStepBranch _ _ _ _ continuation => continuation
       end)
      Hcontinuation_bound Hcontinuation)
    as [fuel [converted Hconverted]].
  exists fuel.
  unfold phase1_surface_normalize_continue_mutual_recursive_session_branch_fuel,
    phase1_surface_normalize_continue_mutual_recursive_session_branch_with.
  destruct branch as [label params boundary guard continuation].
  cbn in Hconverted |- *.
  rewrite Hconverted.
  eexists.
  reflexivity.
Qed.

Lemma
  phase1_surface_normalize_continue_mutual_recursive_session_branch_tail_fuel_total_from_repetition :
  forall parent_length path input rest branches,
    List.length input < parent_length ->
    DerivesRepetition phase1_surface_rules path
      phase1_surface_session_branch_suffix_expression_for_totality
      input rest
      (phase1_surface_continue_choice_one_step_session_branch_tail_spine_trees
        branches) ->
    (forall continuation_path continuation_input continuation_rest continuation,
      List.length continuation_input < parent_length ->
      Derives phase1_surface_rules continuation_path
        (ENonterminal "session_expression")
        continuation_input continuation_rest
        (phase1_surface_continue_transfer_recursive_session_spine_tree continuation) ->
      exists fuel converted,
        phase1_surface_normalize_continue_mutual_recursive_continuation_fuel
          fuel continuation = Some converted) ->
    exists fuel refined,
      phase1_surface_normalize_continue_mutual_recursive_session_branch_tail_fuel
        fuel branches = Some refined.
Proof.
  intros parent_length path input rest branches Hinput Hderive Hsolver.
  revert input rest Hinput Hderive.
  induction branches as [|branch branches IH];
    intros input rest Hinput Hderive.
  - cbn in Hderive.
    inversion Hderive; subst.
    exists 1, Phase1ContinueMutualRecursiveBranchTailNil.
    reflexivity.
  - cbn in Hderive.
    inversion Hderive as
      [|path0 body0 input0 middle0 rest0 tree0 trees0
         Hbody Hprogress Hrest]; subst.
    unfold phase1_surface_session_branch_suffix_expression_for_totality
      in Hbody.
    destruct
      (derives_sequence_expression_exposes_items
        phase1_surface_rules
        (descend path AtRepetitionBody)
        [ ELiteral "|"; ENonterminal "session_branch" ]
        input middle0
        (phase1_surface_session_branch_suffix_tree
          (phase1_surface_continue_choice_one_step_session_branch_spine_tree
            branch))
        Hbody)
      as [trees [Htree Hitems]].
    cbn [phase1_surface_session_branch_suffix_tree] in Htree.
    inversion Htree; subst trees.
    repeat match goal with
    | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
        inversion Hseq; subst; clear Hseq
    end.
    match goal with
    | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
        inversion Hnil; subst; clear Hnil
    end.
    match goal with
    | Hpipe : Derives phase1_surface_rules _
        (ELiteral "|") ?pipe_input ?branch_input _,
      Hbranch : Derives phase1_surface_rules _
        (ENonterminal "session_branch") ?branch_input ?branch_rest
        (phase1_surface_continue_choice_one_step_session_branch_spine_tree
          branch) |- _ =>
        pose proof
          (phase1_surface_derivation_rest_length_le_input
            _ _ _ _ _ Hpipe) as Hpipe_length;
        assert (Hbranch_bound :
          List.length branch_input < parent_length) by lia;
        destruct
          (phase1_surface_normalize_continue_mutual_recursive_session_branch_fuel_total_from_derivation
            parent_length _ branch_input branch_rest branch
            Hbranch_bound Hbranch Hsolver)
          as [branch_fuel [refined_branch Hbranch_normalize]]
    end.
    pose proof
      (phase1_surface_derivation_rest_length_le_input
        _ _ _ _ _ Hbody) as Hbody_length.
    assert (Hrest_bound : List.length middle0 < parent_length) by lia.
    destruct (IH middle0 rest0 Hrest_bound Hrest)
      as [rest_fuel [refined_rest Hrest_normalize]].
    let fuel := constr:(Nat.max branch_fuel rest_fuel) in
    pose proof
      (phase1_surface_normalize_continue_mutual_recursive_session_branch_fuel_monotone
        branch_fuel fuel branch refined_branch
        (Nat.le_max_l branch_fuel rest_fuel) Hbranch_normalize)
      as Hbranch_lifted.
    pose proof
      (phase1_surface_normalize_continue_mutual_recursive_session_branch_tail_fuel_monotone
        rest_fuel fuel branches refined_rest
        (Nat.le_max_r branch_fuel rest_fuel) Hrest_normalize)
      as Hrest_lifted.
    exists fuel,
      (Phase1ContinueMutualRecursiveBranchTailCons
        refined_branch refined_rest).
    unfold
      phase1_surface_normalize_continue_mutual_recursive_session_branch_tail_fuel.
    cbn.
    fold phase1_surface_normalize_continue_mutual_recursive_session_branch_fuel.
    fold
      phase1_surface_normalize_continue_mutual_recursive_session_branch_tail_fuel.
    rewrite Hbranch_lifted, Hrest_lifted.
    reflexivity.
Qed.

Lemma
  phase1_surface_normalize_continue_mutual_recursive_session_choice_fuel_total_from_derivation :
  forall direction path input rest choice,
    Derives phase1_surface_rules path
      (phase1_surface_session_choice_expression_for_totality direction)
      input rest
      (phase1_surface_continue_choice_one_step_session_choice_spine_tree choice) ->
    (forall continuation_path continuation_input continuation_rest continuation,
      List.length continuation_input < List.length input ->
      Derives phase1_surface_rules continuation_path
        (ENonterminal "session_expression")
        continuation_input continuation_rest
        (phase1_surface_continue_transfer_recursive_session_spine_tree continuation) ->
      exists fuel converted,
        phase1_surface_normalize_continue_mutual_recursive_continuation_fuel
          fuel continuation = Some converted) ->
    exists fuel refined,
      phase1_surface_normalize_continue_mutual_recursive_session_choice_fuel
        fuel choice = Some refined.
Proof.
  intros direction path input rest
    [choice_direction first_branch rest_branches] Hderive Hsolver.
  unfold phase1_surface_session_choice_expression_for_totality in Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral (phase1_surface_session_choice_keyword direction);
        ELiteral "{";
        ENonterminal "session_branch";
        ERepetition phase1_surface_session_branch_suffix_expression_for_totality;
        ELiteral "}"
      ]
      input rest
      (phase1_surface_continue_choice_one_step_session_choice_spine_tree
        (Phase1ContinueChoiceOneStepChoice
          choice_direction first_branch rest_branches))
      Hderive)
    as [trees [Htree Hitems]].
  cbn in Htree.
  inversion Htree; subst trees.
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hkeyword : Derives phase1_surface_rules _
      (ELiteral (phase1_surface_session_choice_keyword direction))
      ?keyword_input ?keyword_rest ?keyword_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _
          (phase1_surface_session_choice_keyword direction)
          keyword_input keyword_rest keyword_tree Hkeyword)
        as [keyword_tail
          [Hkeyword_input [Hkeyword_rest Hkeyword_tree_exact]]];
      assert (Hkeyword_length :
        List.length keyword_rest < List.length keyword_input);
      [ rewrite Hkeyword_input, Hkeyword_rest; cbn; lia
      | idtac ]
  end.
  match goal with
  | Hopen : Derives phase1_surface_rules _
      (ELiteral "{") ?open_input ?first_input _,
    Hfirst : Derives phase1_surface_rules _
      (ENonterminal "session_branch") ?first_input ?repetition_input
      (phase1_surface_continue_choice_one_step_session_branch_spine_tree
        first_branch),
    Hrest : Derives phase1_surface_rules _
      (ERepetition phase1_surface_session_branch_suffix_expression_for_totality)
      ?repetition_input ?after_repetition
      (PTRepetition
        (phase1_surface_continue_choice_one_step_session_branch_tail_spine_trees
          rest_branches)) |- _ =>
      pose proof
        (phase1_surface_derivation_rest_length_le_input
          _ _ _ _ _ Hopen) as Hopen_length;
      assert (Hfirst_bound :
        List.length first_input < List.length input) by lia;
      destruct
        (phase1_surface_normalize_continue_mutual_recursive_session_branch_fuel_total_from_derivation
          (List.length input) _ first_input repetition_input first_branch
          Hfirst_bound Hfirst Hsolver)
        as [first_fuel [refined_first Hfirst_normalize]];
      pose proof
        (phase1_surface_derivation_rest_length_le_input
          _ _ _ _ _ Hfirst) as Hfirst_length;
      assert (Hrest_bound :
        List.length repetition_input < List.length input) by lia;
      destruct
        (phase1_surface_repetition_derivation_exposes
          _ phase1_surface_session_branch_suffix_expression_for_totality
          _ _
          (PTRepetition
            (phase1_surface_continue_choice_one_step_session_branch_tail_spine_trees
              rest_branches))
          Hrest)
        as [rest_trees [Hrest_tree Hrest_derive]];
      cbn in Hrest_tree;
      inversion Hrest_tree; subst rest_trees;
      destruct
        (phase1_surface_normalize_continue_mutual_recursive_session_branch_tail_fuel_total_from_repetition
          (List.length input) _ repetition_input after_repetition
          rest_branches Hrest_bound Hrest_derive Hsolver)
        as [rest_fuel [refined_rest Hrest_normalize]];
      let fuel := constr:(Nat.max first_fuel rest_fuel) in
      pose proof
        (phase1_surface_normalize_continue_mutual_recursive_session_branch_fuel_monotone
          first_fuel fuel first_branch refined_first
          (Nat.le_max_l first_fuel rest_fuel) Hfirst_normalize)
        as Hfirst_lifted;
      pose proof
        (phase1_surface_normalize_continue_mutual_recursive_session_branch_tail_fuel_monotone
          rest_fuel fuel rest_branches refined_rest
          (Nat.le_max_r first_fuel rest_fuel) Hrest_normalize)
        as Hrest_lifted;
      exists fuel,
        (Phase1ContinueMutualRecursiveChoice
          choice_direction refined_first refined_rest);
      unfold phase1_surface_normalize_continue_mutual_recursive_session_choice_fuel,
        phase1_surface_normalize_continue_mutual_recursive_session_choice_with;
      cbn;
      fold phase1_surface_normalize_continue_mutual_recursive_session_branch_fuel;
      fold
        phase1_surface_normalize_continue_mutual_recursive_session_branch_tail_fuel;
      rewrite Hfirst_lifted, Hrest_lifted;
      reflexivity
  end.
Qed.

Lemma
  phase1_surface_normalize_continue_mutual_recursive_session_spine_fuel_total_measure :
  forall measure path input rest session,
    List.length input < measure ->
    Derives phase1_surface_rules path
      (ENonterminal "session_expression") input rest
      (phase1_surface_continue_choice_one_step_session_spine_tree session) ->
    exists fuel refined,
      phase1_surface_normalize_continue_mutual_recursive_session_spine_fuel
        fuel session = Some refined.
Proof.
  induction measure as [|measure IH];
    intros path input rest session Hmeasure Hderive.
  - lia.
  - assert (Hsolver :
      forall continuation_path continuation_input continuation_rest continuation,
        List.length continuation_input < List.length input ->
        Derives phase1_surface_rules continuation_path
          (ENonterminal "session_expression")
          continuation_input continuation_rest
          (phase1_surface_continue_transfer_recursive_session_spine_tree
            continuation) ->
        exists fuel converted,
          phase1_surface_normalize_continue_mutual_recursive_continuation_fuel
            fuel continuation = Some converted).
    {
      intros continuation_path continuation_input continuation_rest
        continuation Hshorter Hcontinuation.
      destruct
        (phase1_surface_normalize_continue_choice_one_step_session_spine_total_from_derivation
          continuation_path continuation_input continuation_rest
          continuation Hcontinuation)
        as [step Hstep].
      pose proof
        (phase1_surface_normalize_continue_choice_one_step_session_spine_round_trip
          continuation step Hstep) as Hstep_tree.
      assert (Hrecursive_measure :
        List.length continuation_input < measure) by lia.
      rewrite <- Hstep_tree in Hcontinuation.
      destruct
        (IH continuation_path continuation_input continuation_rest
          step Hrecursive_measure Hcontinuation)
        as [fuel [converted Hrecursive]].
      exists fuel, converted.
      unfold
        phase1_surface_normalize_continue_mutual_recursive_continuation_fuel.
      rewrite Hstep.
      exact Hrecursive.
    }
    destruct session as [nonreference | reference_tree].
    + destruct nonreference as
        [direction parameter boundary guard continuation
        |choice
        |choice
        |terminal
        |selected_tree
        |payload].
      * let transfer := constr:(
          {| phase1_guard_refined_transfer_direction := direction;
             phase1_guard_refined_transfer_parameter := parameter;
             phase1_guard_refined_transfer_boundary := boundary;
             phase1_guard_refined_transfer_guard := guard;
             phase1_guard_refined_transfer_continuation_tree :=
               phase1_surface_continue_transfer_recursive_session_spine_tree
                 continuation |}) in
        assert (Htransfer_tree :
          phase1_surface_guard_refined_boundary_typed_transfer_session_spine_tree
            (Phase1GuardRefinedBoundaryTypedTransferNonreferenceSession
              (Phase1GuardRefinedBoundaryTypedTransferSession transfer)) =
          phase1_surface_continue_choice_one_step_session_spine_tree
            (Phase1ContinueChoiceOneStepNonreferenceSession
              (Phase1ContinueChoiceOneStepTransferSession
                direction parameter boundary guard continuation)))
          by reflexivity;
        destruct
          (phase1_surface_guard_refined_transfer_continuation_derivation_shorter
            path input rest
            (phase1_surface_continue_choice_one_step_session_spine_tree
              (Phase1ContinueChoiceOneStepNonreferenceSession
                (Phase1ContinueChoiceOneStepTransferSession
                  direction parameter boundary guard continuation)))
            transfer Hderive Htransfer_tree)
          as [continuation_path [continuation_input [continuation_rest
            [Hcontinuation Hshorter]]]];
        destruct
          (Hsolver continuation_path continuation_input continuation_rest
            continuation Hshorter Hcontinuation)
          as [fuel [converted Hconverted]];
        exists (S fuel),
          (Phase1ContinueMutualRecursiveNonreferenceSession
            (Phase1ContinueMutualRecursiveTransferSession
              direction parameter boundary guard converted));
        cbn [phase1_surface_normalize_continue_mutual_recursive_session_spine_fuel];
        fold
          phase1_surface_normalize_continue_mutual_recursive_continuation_fuel;
        rewrite Hconverted;
        reflexivity.
      * destruct
          (phase1_surface_selected_choice_derivation
            Phase1SessionSelect path input rest
            (phase1_surface_continue_choice_one_step_session_choice_spine_tree
              choice)
            Hderive)
          as [choice_path Hchoice];
        destruct
          (phase1_surface_normalize_continue_mutual_recursive_session_choice_fuel_total_from_derivation
            Phase1SessionSelect choice_path input rest choice Hchoice Hsolver)
          as [fuel [refined_choice Hchoice_normalize]];
        exists (S fuel),
          (Phase1ContinueMutualRecursiveNonreferenceSession
            (Phase1ContinueMutualRecursiveSelectSession refined_choice));
        cbn [phase1_surface_normalize_continue_mutual_recursive_session_spine_fuel];
        fold
          phase1_surface_normalize_continue_mutual_recursive_continuation_fuel;
        change
          (match
            phase1_surface_normalize_continue_mutual_recursive_session_choice_fuel
              fuel choice
          with
          | Some refined =>
              Some
                (Phase1ContinueMutualRecursiveNonreferenceSession
                  (Phase1ContinueMutualRecursiveSelectSession refined))
          | None => None
          end =
          Some
            (Phase1ContinueMutualRecursiveNonreferenceSession
              (Phase1ContinueMutualRecursiveSelectSession refined_choice)));
        rewrite Hchoice_normalize;
        reflexivity.
      * destruct
          (phase1_surface_selected_choice_derivation
            Phase1SessionOffer path input rest
            (phase1_surface_continue_choice_one_step_session_choice_spine_tree
              choice)
            Hderive)
          as [choice_path Hchoice];
        destruct
          (phase1_surface_normalize_continue_mutual_recursive_session_choice_fuel_total_from_derivation
            Phase1SessionOffer choice_path input rest choice Hchoice Hsolver)
          as [fuel [refined_choice Hchoice_normalize]];
        exists (S fuel),
          (Phase1ContinueMutualRecursiveNonreferenceSession
            (Phase1ContinueMutualRecursiveOfferSession refined_choice));
        cbn [phase1_surface_normalize_continue_mutual_recursive_session_spine_fuel];
        fold
          phase1_surface_normalize_continue_mutual_recursive_continuation_fuel;
        change
          (match
            phase1_surface_normalize_continue_mutual_recursive_session_choice_fuel
              fuel choice
          with
          | Some refined =>
              Some
                (Phase1ContinueMutualRecursiveNonreferenceSession
                  (Phase1ContinueMutualRecursiveOfferSession refined))
          | None => None
          end =
          Some
            (Phase1ContinueMutualRecursiveNonreferenceSession
              (Phase1ContinueMutualRecursiveOfferSession refined_choice)));
        rewrite Hchoice_normalize;
        reflexivity.
      * exists 1,
          (Phase1ContinueMutualRecursiveNonreferenceSession
            (Phase1ContinueMutualRecursiveEndSession terminal)).
        reflexivity.
      * exists 1,
          (Phase1ContinueMutualRecursiveNonreferenceSession
            (Phase1ContinueMutualRecursiveRecursiveSession selected_tree)).
        reflexivity.
      * exists 1,
          (Phase1ContinueMutualRecursiveNonreferenceSession
            (Phase1ContinueMutualRecursiveContinueSession payload)).
        reflexivity.
    + exists 1,
        (Phase1ContinueMutualRecursiveStaticReferenceSession reference_tree).
      reflexivity.
Qed.

Theorem
  phase1_surface_normalize_continue_mutual_recursive_session_spine_fuel_total_from_derivation :
  forall path input rest session,
    Derives phase1_surface_rules path
      (ENonterminal "session_expression") input rest
      (phase1_surface_continue_choice_one_step_session_spine_tree session) ->
    exists fuel refined,
      phase1_surface_normalize_continue_mutual_recursive_session_spine_fuel
        fuel session = Some refined /\
      phase1_surface_continue_mutual_recursive_session_spine_tree refined =
        phase1_surface_continue_choice_one_step_session_spine_tree session.
Proof.
  intros path input rest session Hderive.
  destruct
    (phase1_surface_normalize_continue_mutual_recursive_session_spine_fuel_total_measure
      (S (List.length input)) path input rest session
      (Nat.lt_succ_diag_r (List.length input)) Hderive)
    as [fuel [refined Hnormalize]].
  exists fuel, refined.
  split.
  - exact Hnormalize.
  - eapply
      phase1_surface_normalize_continue_mutual_recursive_session_spine_fuel_round_trip.
    exact Hnormalize.
Qed.
