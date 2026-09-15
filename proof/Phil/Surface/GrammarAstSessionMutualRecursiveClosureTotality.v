From Stdlib Require Import Arith.PeanoNat Lists.List Strings.String Lia.

From Phil.Surface Require Import
  GrammarAstSessionMutualRecursiveClosureSpine
  GrammarAstSessionBranchContinuationCarrierTotality
  GrammarAstSessionTransferRecursiveClosureTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse and fuel closure for the mutual transfer/choice recursive carrier. *)

Lemma
  phase1_surface_normalize_continuation_refined_session_choice_spine_fuel_monotone :
  forall fuel larger choice refined,
    fuel <= larger ->
    phase1_surface_normalize_continuation_refined_session_choice_spine_fuel
      fuel choice = Some refined ->
    phase1_surface_normalize_continuation_refined_session_choice_spine_fuel
      larger choice = Some refined.
Proof.
  intros fuel larger [direction first_branch rest_branches]
    refined Hle Hnormalize.
  cbn in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_continuation_refined_session_branch_spine_fuel
      fuel first_branch)
    as [refined_first |] eqn:Hfirst; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_continuation_refined_session_branch_spines_fuel
      fuel rest_branches)
    as [refined_rest |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  rewrite
    (phase1_surface_normalize_continuation_refined_session_branch_spine_fuel_monotone
      fuel larger first_branch refined_first Hle Hfirst).
  rewrite
    (phase1_surface_normalize_continuation_refined_session_branch_spines_fuel_monotone
      fuel larger rest_branches refined_rest Hle Hrest).
  reflexivity.
Qed.

Lemma
  phase1_surface_normalize_continuation_refined_session_choice_tree_fuel_monotone :
  forall fuel larger direction tree refined,
    fuel <= larger ->
    phase1_surface_normalize_continuation_refined_session_choice_tree_fuel
      fuel direction tree = Some refined ->
    phase1_surface_normalize_continuation_refined_session_choice_tree_fuel
      larger direction tree = Some refined.
Proof.
  intros fuel larger direction tree refined Hle Hnormalize.
  unfold phase1_surface_normalize_continuation_refined_session_choice_tree_fuel
    in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_guard_refined_session_choice_tree direction tree)
    as [choice |] eqn:Hchoice; try discriminate Hnormalize.
  rewrite Hchoice.
  eapply
    phase1_surface_normalize_continuation_refined_session_choice_spine_fuel_monotone.
  - exact Hle.
  - exact Hnormalize.
Qed.

Lemma
  phase1_surface_normalize_choice_refined_recursive_nonreference_session_spine_fuel_monotone :
  forall fuel larger session refined,
    fuel <= larger ->
    phase1_surface_normalize_choice_refined_recursive_nonreference_session_spine_fuel
      fuel session = Some refined ->
    phase1_surface_normalize_choice_refined_recursive_nonreference_session_spine_fuel
      larger session = Some refined.
Proof.
  intros fuel larger session refined Hle Hnormalize.
  destruct session as
    [direction parameter boundary guard continuation
    |selected_tree
    |selected_tree
    |selected_tree
    |selected_tree
    |selected_tree].
  - inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize |- *.
    destruct
      (phase1_surface_normalize_continuation_refined_session_choice_tree_fuel
        fuel Phase1SessionSelect selected_tree)
      as [choice |] eqn:Hchoice; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    rewrite
      (phase1_surface_normalize_continuation_refined_session_choice_tree_fuel_monotone
        fuel larger Phase1SessionSelect selected_tree choice Hle Hchoice).
    reflexivity.
  - cbn in Hnormalize |- *.
    destruct
      (phase1_surface_normalize_continuation_refined_session_choice_tree_fuel
        fuel Phase1SessionOffer selected_tree)
      as [choice |] eqn:Hchoice; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    rewrite
      (phase1_surface_normalize_continuation_refined_session_choice_tree_fuel_monotone
        fuel larger Phase1SessionOffer selected_tree choice Hle Hchoice).
    reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
Qed.

Lemma
  phase1_surface_normalize_choice_refined_recursive_session_spine_fuel_monotone :
  forall fuel larger session refined,
    fuel <= larger ->
    phase1_surface_normalize_choice_refined_recursive_session_spine_fuel
      fuel session = Some refined ->
    phase1_surface_normalize_choice_refined_recursive_session_spine_fuel
      larger session = Some refined.
Proof.
  intros fuel larger [nonreference | reference_tree] refined Hle Hnormalize.
  - cbn in Hnormalize |- *.
    destruct
      (phase1_surface_normalize_choice_refined_recursive_nonreference_session_spine_fuel
        fuel nonreference)
      as [actual |] eqn:Hnonreference; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    rewrite
      (phase1_surface_normalize_choice_refined_recursive_nonreference_session_spine_fuel_monotone
        fuel larger nonreference actual Hle Hnonreference).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Lemma
  phase1_surface_normalize_choice_refined_recursive_session_tree_fuel_monotone :
  forall fuel larger tree refined,
    fuel <= larger ->
    phase1_surface_normalize_choice_refined_recursive_session_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_normalize_choice_refined_recursive_session_tree_fuel
      larger tree = Some refined.
Proof.
  intros fuel larger tree refined Hle Hnormalize.
  unfold phase1_surface_normalize_choice_refined_recursive_session_tree_fuel
    in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_recursive_transfer_session_tree_fuel fuel tree)
    as [session |] eqn:Hsession; try discriminate Hnormalize.
  pose proof
    (phase1_surface_normalize_recursive_transfer_session_tree_fuel_monotone
      fuel larger tree session Hle Hsession) as Hsession_larger.
  rewrite Hsession_larger.
  eapply
    phase1_surface_normalize_choice_refined_recursive_session_spine_fuel_monotone.
  - exact Hle.
  - exact Hnormalize.
Qed.

Lemma phase1_surface_normalize_mutual_recursive_session_branch_with_respects :
  forall normalize_left normalize_right branch refined,
    (forall continuation converted,
      normalize_left continuation = Some converted ->
      normalize_right continuation = Some converted) ->
    phase1_surface_normalize_mutual_recursive_session_branch_with
      normalize_left branch = Some refined ->
    phase1_surface_normalize_mutual_recursive_session_branch_with
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
  phase1_surface_normalize_mutual_recursive_session_branch_tail_with_respects :
  forall normalize_left normalize_right branches refined,
    (forall continuation converted,
      normalize_left continuation = Some converted ->
      normalize_right continuation = Some converted) ->
    phase1_surface_normalize_mutual_recursive_session_branch_tail_with
      normalize_left branches = Some refined ->
    phase1_surface_normalize_mutual_recursive_session_branch_tail_with
      normalize_right branches = Some refined.
Proof.
  intros normalize_left normalize_right branches.
  induction branches as [|branch rest IH]; intros refined Hrespect Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize |- *.
    destruct
      (phase1_surface_normalize_mutual_recursive_session_branch_with
        normalize_left branch)
      as [refined_branch |] eqn:Hbranch; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_mutual_recursive_session_branch_tail_with
        normalize_left rest)
      as [refined_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    rewrite
      (phase1_surface_normalize_mutual_recursive_session_branch_with_respects
        normalize_left normalize_right branch refined_branch
        Hrespect Hbranch).
    rewrite (IH refined_rest Hrespect Hrest).
    reflexivity.
Qed.

Lemma phase1_surface_normalize_mutual_recursive_session_choice_with_respects :
  forall normalize_left normalize_right choice refined,
    (forall continuation converted,
      normalize_left continuation = Some converted ->
      normalize_right continuation = Some converted) ->
    phase1_surface_normalize_mutual_recursive_session_choice_with
      normalize_left choice = Some refined ->
    phase1_surface_normalize_mutual_recursive_session_choice_with
      normalize_right choice = Some refined.
Proof.
  intros normalize_left normalize_right
    [direction first_branch rest_branches] refined Hrespect Hnormalize.
  cbn in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_mutual_recursive_session_branch_with
      normalize_left first_branch)
    as [refined_first |] eqn:Hfirst; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_mutual_recursive_session_branch_tail_with
      normalize_left rest_branches)
    as [refined_rest |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  rewrite
    (phase1_surface_normalize_mutual_recursive_session_branch_with_respects
      normalize_left normalize_right first_branch refined_first
      Hrespect Hfirst).
  rewrite
    (phase1_surface_normalize_mutual_recursive_session_branch_tail_with_respects
      normalize_left normalize_right rest_branches refined_rest
      Hrespect Hrest).
  reflexivity.
Qed.

Definition phase1_surface_normalize_mutual_recursive_continuation_fuel
  (fuel : nat)
  (continuation : Phase1SurfaceRecursiveTransferSessionSpine)
  : option Phase1SurfaceMutualRecursiveSessionSpine :=
  match
    phase1_surface_normalize_choice_refined_recursive_session_spine_fuel
      fuel continuation
  with
  | Some step =>
      phase1_surface_normalize_mutual_recursive_session_spine_fuel fuel step
  | None => None
  end.

Lemma phase1_surface_normalize_mutual_recursive_session_spine_fuel_monotone :
  forall fuel larger session refined,
    fuel <= larger ->
    phase1_surface_normalize_mutual_recursive_session_spine_fuel
      fuel session = Some refined ->
    phase1_surface_normalize_mutual_recursive_session_spine_fuel
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
          phase1_surface_normalize_mutual_recursive_continuation_fuel
            fuel continuation = Some converted ->
          phase1_surface_normalize_mutual_recursive_continuation_fuel
            larger continuation = Some converted).
      {
        intros continuation converted Hconverted.
        unfold phase1_surface_normalize_mutual_recursive_continuation_fuel
          in Hconverted |- *.
        destruct
          (phase1_surface_normalize_choice_refined_recursive_session_spine_fuel
            fuel continuation)
          as [step |] eqn:Hstep; try discriminate Hconverted.
        pose proof
          (phase1_surface_normalize_choice_refined_recursive_session_spine_fuel_monotone
            fuel larger continuation step Hremaining Hstep) as Hstep_larger.
        rewrite Hstep_larger.
        eapply IH.
        - exact Hremaining.
        - exact Hconverted.
      }
      destruct session as [nonreference | reference_tree].
      * destruct nonreference as
          [direction parameter boundary guard continuation
          |choice
          |choice
          |selected_tree
          |selected_tree
          |selected_tree].
        -- cbn [phase1_surface_normalize_mutual_recursive_session_spine_fuel]
             in Hnormalize |- *.
           fold phase1_surface_normalize_mutual_recursive_continuation_fuel
             in Hnormalize |- *.
           destruct
             (phase1_surface_normalize_mutual_recursive_continuation_fuel
               fuel continuation)
             as [converted |] eqn:Hconverted; try discriminate Hnormalize.
           inversion Hnormalize; subst refined.
           rewrite (Hcontinuation continuation converted Hconverted).
           reflexivity.
        -- cbn [phase1_surface_normalize_mutual_recursive_session_spine_fuel]
             in Hnormalize |- *.
           fold phase1_surface_normalize_mutual_recursive_continuation_fuel
             in Hnormalize |- *.
           destruct
             (phase1_surface_normalize_mutual_recursive_session_choice_with
               (phase1_surface_normalize_mutual_recursive_continuation_fuel fuel)
               choice)
             as [converted |] eqn:Hchoice; try discriminate Hnormalize.
           inversion Hnormalize; subst refined.
           pose proof
             (phase1_surface_normalize_mutual_recursive_session_choice_with_respects
               (phase1_surface_normalize_mutual_recursive_continuation_fuel fuel)
               (phase1_surface_normalize_mutual_recursive_continuation_fuel larger)
               choice converted Hcontinuation Hchoice)
             as Hchoice_larger.
           rewrite Hchoice_larger.
           reflexivity.
        -- cbn [phase1_surface_normalize_mutual_recursive_session_spine_fuel]
             in Hnormalize |- *.
           fold phase1_surface_normalize_mutual_recursive_continuation_fuel
             in Hnormalize |- *.
           destruct
             (phase1_surface_normalize_mutual_recursive_session_choice_with
               (phase1_surface_normalize_mutual_recursive_continuation_fuel fuel)
               choice)
             as [converted |] eqn:Hchoice; try discriminate Hnormalize.
           inversion Hnormalize; subst refined.
           pose proof
             (phase1_surface_normalize_mutual_recursive_session_choice_with_respects
               (phase1_surface_normalize_mutual_recursive_continuation_fuel fuel)
               (phase1_surface_normalize_mutual_recursive_continuation_fuel larger)
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

Lemma phase1_surface_normalize_mutual_recursive_continuation_fuel_monotone :
  forall fuel larger continuation refined,
    fuel <= larger ->
    phase1_surface_normalize_mutual_recursive_continuation_fuel
      fuel continuation = Some refined ->
    phase1_surface_normalize_mutual_recursive_continuation_fuel
      larger continuation = Some refined.
Proof.
  intros fuel larger continuation refined Hle Hnormalize.
  unfold phase1_surface_normalize_mutual_recursive_continuation_fuel
    in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_choice_refined_recursive_session_spine_fuel
      fuel continuation)
    as [step |] eqn:Hstep; try discriminate Hnormalize.
  pose proof
    (phase1_surface_normalize_choice_refined_recursive_session_spine_fuel_monotone
      fuel larger continuation step Hle Hstep) as Hstep_larger.
  rewrite Hstep_larger.
  eapply phase1_surface_normalize_mutual_recursive_session_spine_fuel_monotone.
  - exact Hle.
  - exact Hnormalize.
Qed.

Definition phase1_surface_normalize_mutual_recursive_session_branch_fuel
  (fuel : nat)
  (branch : Phase1SurfaceContinuationRefinedSessionBranchSpine)
  : option Phase1SurfaceMutualRecursiveSessionBranchSpine :=
  phase1_surface_normalize_mutual_recursive_session_branch_with
    (phase1_surface_normalize_mutual_recursive_continuation_fuel fuel)
    branch.

Definition phase1_surface_normalize_mutual_recursive_session_branch_tail_fuel
  (fuel : nat)
  (branches : list Phase1SurfaceContinuationRefinedSessionBranchSpine)
  : option Phase1SurfaceMutualRecursiveSessionBranchTailSpine :=
  phase1_surface_normalize_mutual_recursive_session_branch_tail_with
    (phase1_surface_normalize_mutual_recursive_continuation_fuel fuel)
    branches.

Definition phase1_surface_normalize_mutual_recursive_session_choice_fuel
  (fuel : nat)
  (choice : Phase1SurfaceContinuationRefinedSessionChoiceSpine)
  : option Phase1SurfaceMutualRecursiveSessionChoiceSpine :=
  phase1_surface_normalize_mutual_recursive_session_choice_with
    (phase1_surface_normalize_mutual_recursive_continuation_fuel fuel)
    choice.

Lemma phase1_surface_normalize_mutual_recursive_session_branch_fuel_monotone :
  forall fuel larger branch refined,
    fuel <= larger ->
    phase1_surface_normalize_mutual_recursive_session_branch_fuel
      fuel branch = Some refined ->
    phase1_surface_normalize_mutual_recursive_session_branch_fuel
      larger branch = Some refined.
Proof.
  intros fuel larger branch refined Hle Hnormalize.
  unfold phase1_surface_normalize_mutual_recursive_session_branch_fuel
    in Hnormalize |- *.
  eapply phase1_surface_normalize_mutual_recursive_session_branch_with_respects.
  - intros continuation converted Hconverted.
    eapply phase1_surface_normalize_mutual_recursive_continuation_fuel_monotone.
    + exact Hle.
    + exact Hconverted.
  - exact Hnormalize.
Qed.

Lemma
  phase1_surface_normalize_mutual_recursive_session_branch_tail_fuel_monotone :
  forall fuel larger branches refined,
    fuel <= larger ->
    phase1_surface_normalize_mutual_recursive_session_branch_tail_fuel
      fuel branches = Some refined ->
    phase1_surface_normalize_mutual_recursive_session_branch_tail_fuel
      larger branches = Some refined.
Proof.
  intros fuel larger branches refined Hle Hnormalize.
  unfold phase1_surface_normalize_mutual_recursive_session_branch_tail_fuel
    in Hnormalize |- *.
  eapply
    phase1_surface_normalize_mutual_recursive_session_branch_tail_with_respects.
  - intros continuation converted Hconverted.
    eapply phase1_surface_normalize_mutual_recursive_continuation_fuel_monotone.
    + exact Hle.
    + exact Hconverted.
  - exact Hnormalize.
Qed.

Lemma phase1_surface_normalize_mutual_recursive_session_choice_fuel_monotone :
  forall fuel larger choice refined,
    fuel <= larger ->
    phase1_surface_normalize_mutual_recursive_session_choice_fuel
      fuel choice = Some refined ->
    phase1_surface_normalize_mutual_recursive_session_choice_fuel
      larger choice = Some refined.
Proof.
  intros fuel larger choice refined Hle Hnormalize.
  unfold phase1_surface_normalize_mutual_recursive_session_choice_fuel
    in Hnormalize |- *.
  eapply phase1_surface_normalize_mutual_recursive_session_choice_with_respects.
  - intros continuation converted Hconverted.
    eapply phase1_surface_normalize_mutual_recursive_continuation_fuel_monotone.
    + exact Hle.
    + exact Hconverted.
  - exact Hnormalize.
Qed.

Lemma phase1_surface_selected_choice_derivation :
  forall direction path input rest choice_tree,
    Derives phase1_surface_rules path
      (ENonterminal "session_expression")
      input rest
      (PTNonterminal "session_expression"
        (PTAlternative 0
          (PTNonterminal "nonreference_session_expression"
            (PTAlternative
              (phase1_surface_session_choice_index direction)
              choice_tree)))) ->
    exists choice_path,
      Derives phase1_surface_rules choice_path
        (phase1_surface_session_choice_expression_for_totality direction)
        input rest choice_tree.
Proof.
  intros direction path input rest choice_tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "session_expression"
      input rest
      (PTNonterminal "session_expression"
        (PTAlternative 0
          (PTNonterminal "nonreference_session_expression"
            (PTAlternative
              (phase1_surface_session_choice_index direction)
              choice_tree))))
      Hderive)
    as [body [subtree [Hlookup [Hnode Hbody]]]].
  rewrite phase1_surface_session_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  cbn in Hnode.
  inversion Hnode; subst subtree.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "session_expression"))
      phase1_surface_session_items_for_totality
      input rest
      (PTAlternative 0
        (PTNonterminal "nonreference_session_expression"
          (PTAlternative
            (phase1_surface_session_choice_index direction)
            choice_tree)))
      Hbody)
    as [index [item [selected [Hnth [Hselected_tree Hselected]]]]].
  cbn in Hselected_tree.
  inversion Hselected_tree; subst index selected.
  cbn in Hnth.
  inversion Hnth; subst item.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules
      _
      "nonreference_session_expression"
      input rest
      (PTNonterminal "nonreference_session_expression"
        (PTAlternative
          (phase1_surface_session_choice_index direction)
          choice_tree))
      Hselected)
    as [nonreference_body
      [nonreference_subtree
        [Hnonreference_lookup [Hnonreference_node Hnonreference_body]]]].
  rewrite phase1_surface_nonreference_session_lookup_for_totality
    in Hnonreference_lookup.
  inversion Hnonreference_lookup; subst nonreference_body.
  cbn in Hnonreference_node.
  inversion Hnonreference_node; subst nonreference_subtree.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      _
      phase1_surface_nonreference_session_items_for_totality
      input rest
      (PTAlternative
        (phase1_surface_session_choice_index direction)
        choice_tree)
      Hnonreference_body)
    as [choice_index [choice_item [selected_choice
      [Hchoice_nth [Hchoice_tree Hchoice]]]]].
  cbn in Hchoice_tree.
  inversion Hchoice_tree; subst choice_index selected_choice.
  destruct direction.
  - cbn in Hchoice_nth.
    inversion Hchoice_nth; subst choice_item.
    eexists.
    exact Hchoice.
  - cbn in Hchoice_nth.
    inversion Hchoice_nth; subst choice_item.
    eexists.
    exact Hchoice.
Qed.

Lemma
  phase1_surface_normalize_choice_refined_recursive_session_spine_fuel_total_from_derivation :
  forall path input rest tree session,
    Derives phase1_surface_rules path
      (ENonterminal "session_expression") input rest tree ->
    phase1_surface_recursive_transfer_session_spine_tree session = tree ->
    exists fuel refined,
      phase1_surface_normalize_choice_refined_recursive_session_spine_fuel
        fuel session = Some refined.
Proof.
  intros path input rest tree session Hderive Htree.
  rewrite <- Htree in Hderive.
  destruct session as [nonreference | reference_tree].
  - destruct nonreference as
      [direction parameter boundary guard continuation
      |selected_tree
      |selected_tree
      |selected_tree
      |selected_tree
      |selected_tree].
    + exists 1.
      eexists.
      reflexivity.
    + destruct
        (phase1_surface_selected_choice_derivation
          Phase1SessionSelect path input rest selected_tree Hderive)
        as [choice_path Hchoice].
      destruct
        (phase1_surface_normalize_continuation_refined_session_choice_tree_fuel_total_from_derivation
          Phase1SessionSelect choice_path input rest selected_tree Hchoice)
        as [fuel [choice [Hchoice_normalize Hchoice_tree]]].
      exists fuel, (Phase1ChoiceRefinedRecursiveNonreferenceSession
        (Phase1ChoiceRefinedRecursiveSelectSession choice)).
      cbn.
      rewrite Hchoice_normalize.
      reflexivity.
    + destruct
        (phase1_surface_selected_choice_derivation
          Phase1SessionOffer path input rest selected_tree Hderive)
        as [choice_path Hchoice].
      destruct
        (phase1_surface_normalize_continuation_refined_session_choice_tree_fuel_total_from_derivation
          Phase1SessionOffer choice_path input rest selected_tree Hchoice)
        as [fuel [choice [Hchoice_normalize Hchoice_tree]]].
      exists fuel, (Phase1ChoiceRefinedRecursiveNonreferenceSession
        (Phase1ChoiceRefinedRecursiveOfferSession choice)).
      cbn.
      rewrite Hchoice_normalize.
      reflexivity.
    + exists 1. eexists. reflexivity.
    + exists 1. eexists. reflexivity.
    + exists 1. eexists. reflexivity.
  - exists 1.
    eexists.
    reflexivity.
Qed.

Lemma
  phase1_surface_normalize_choice_refined_recursive_session_tree_fuel_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "session_expression") input rest tree ->
    exists fuel refined,
      phase1_surface_normalize_choice_refined_recursive_session_tree_fuel
        fuel tree = Some refined /\
      phase1_surface_choice_refined_recursive_session_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_recursive_transfer_session_tree_total_from_derivation
      path input rest tree Hderive)
    as [session [Hsession Hsession_tree]].
  destruct
    (phase1_surface_normalize_choice_refined_recursive_session_spine_fuel_total_from_derivation
      path input rest tree session Hderive Hsession_tree)
    as [refined_fuel [refined Hrefined]].
  let recursive_fuel := constr:(S (List.length input)) in
  let fuel := constr:(Nat.max recursive_fuel refined_fuel) in
  pose proof
    (phase1_surface_normalize_recursive_transfer_session_tree_fuel_monotone
      recursive_fuel fuel tree session
      (Nat.le_max_l recursive_fuel refined_fuel) Hsession)
    as Hsession_lifted.
  pose proof
    (phase1_surface_normalize_choice_refined_recursive_session_spine_fuel_monotone
      refined_fuel fuel session refined
      (Nat.le_max_r recursive_fuel refined_fuel) Hrefined)
    as Hrefined_lifted.
  assert (Hresult :
    phase1_surface_normalize_choice_refined_recursive_session_tree_fuel
      fuel tree = Some refined).
  {
    unfold phase1_surface_normalize_choice_refined_recursive_session_tree_fuel.
    rewrite Hsession_lifted.
    exact Hrefined_lifted.
  }
  exists fuel, refined.
  split.
  - exact Hresult.
  - eapply
      phase1_surface_normalize_choice_refined_recursive_session_tree_fuel_round_trip.
    exact Hresult.
Qed.

Lemma
  phase1_surface_continuation_refined_session_branch_exposes_continuation :
  forall path input rest branch,
    Derives phase1_surface_rules path
      (ENonterminal "session_branch")
      input rest
      (phase1_surface_continuation_refined_session_branch_spine_tree branch) ->
    exists continuation_path continuation_input continuation_rest,
      Derives phase1_surface_rules continuation_path
        (ENonterminal "session_expression")
        continuation_input continuation_rest
        (phase1_surface_recursive_transfer_session_spine_tree
          (phase1_continuation_refined_session_branch_continuation branch)) /\
      List.length continuation_input <= List.length input.
Proof.
  intros path input rest
    [label params boundary guard continuation] Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "session_branch"
      input rest
      (phase1_surface_continuation_refined_session_branch_spine_tree
        {| phase1_continuation_refined_session_branch_label := label;
           phase1_continuation_refined_session_branch_params := params;
           phase1_continuation_refined_session_branch_boundary := boundary;
           phase1_continuation_refined_session_branch_guard := guard;
           phase1_continuation_refined_session_branch_continuation := continuation |})
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
          phase1_surface_recursive_transfer_session_spine_tree continuation
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
  | Hlabel : Derives phase1_surface_rules _
      (ENonterminal "identifier") _ _ _ |- _ =>
      pose proof
        (phase1_surface_derivation_rest_length_le_input
          _ _ _ _ _ Hlabel) as Hlabel_length
  end.
  match goal with
  | Hparams : Derives phase1_surface_rules _
      phase1_surface_session_branch_params_expression_for_totality _ _ _ |- _ =>
      pose proof
        (phase1_surface_derivation_rest_length_le_input
          _ _ _ _ _ Hparams) as Hparams_length
  end.
  match goal with
  | Hboundary : Derives phase1_surface_rules _
      phase1_surface_session_branch_boundary_expression_for_totality _ _ _ |- _ =>
      pose proof
        (phase1_surface_derivation_rest_length_le_input
          _ _ _ _ _ Hboundary) as Hboundary_length
  end.
  match goal with
  | Hguard : Derives phase1_surface_rules _
      phase1_surface_session_branch_guard_expression_for_totality _ _ _ |- _ =>
      pose proof
        (phase1_surface_derivation_rest_length_le_input
          _ _ _ _ _ Hguard) as Hguard_length
  end.
  match goal with
  | Harrow : Derives phase1_surface_rules _
      (ELiteral "=>") _ _ _ |- _ =>
      pose proof
        (phase1_surface_derivation_rest_length_le_input
          _ _ _ _ _ Harrow) as Harrow_length
  end.
  match goal with
  | Hcontinuation : Derives phase1_surface_rules ?continuation_path
      (ENonterminal "session_expression")
      ?continuation_input ?continuation_rest
      (phase1_surface_recursive_transfer_session_spine_tree continuation) |- _ =>
      exists continuation_path, continuation_input, continuation_rest;
      split;
      [ exact Hcontinuation
      | lia ]
  end.
Qed.

Lemma
  phase1_surface_normalize_mutual_recursive_session_branch_fuel_total_from_derivation :
  forall parent_length path input rest branch,
    List.length input < parent_length ->
    Derives phase1_surface_rules path
      (ENonterminal "session_branch")
      input rest
      (phase1_surface_continuation_refined_session_branch_spine_tree branch) ->
    (forall continuation_path continuation_input continuation_rest continuation,
      List.length continuation_input < parent_length ->
      Derives phase1_surface_rules continuation_path
        (ENonterminal "session_expression")
        continuation_input continuation_rest
        (phase1_surface_recursive_transfer_session_spine_tree continuation) ->
      exists fuel converted,
        phase1_surface_normalize_mutual_recursive_continuation_fuel
          fuel continuation = Some converted) ->
    exists fuel refined,
      phase1_surface_normalize_mutual_recursive_session_branch_fuel
        fuel branch = Some refined.
Proof.
  intros parent_length path input rest branch
    Hinput Hderive Hsolver.
  destruct
    (phase1_surface_continuation_refined_session_branch_exposes_continuation
      path input rest branch Hderive)
    as [continuation_path [continuation_input [continuation_rest
      [Hcontinuation Hcontinuation_length]]]].
  assert (Hcontinuation_bound :
    List.length continuation_input < parent_length) by lia.
  destruct
    (Hsolver continuation_path continuation_input continuation_rest
      (phase1_continuation_refined_session_branch_continuation branch)
      Hcontinuation_bound Hcontinuation)
    as [fuel [converted Hconverted]].
  exists fuel.
  unfold phase1_surface_normalize_mutual_recursive_session_branch_fuel,
    phase1_surface_normalize_mutual_recursive_session_branch_with.
  rewrite Hconverted.
  eexists.
  reflexivity.
Qed.

Lemma
  phase1_surface_normalize_mutual_recursive_session_branch_tail_fuel_total_from_repetition :
  forall parent_length path body input rest branches,
    List.length input < parent_length ->
    DerivesRepetition phase1_surface_rules path body input rest
      (map
        (fun branch =>
          phase1_surface_session_branch_suffix_tree
            (phase1_surface_continuation_refined_session_branch_spine_tree branch))
        branches) ->
    body = phase1_surface_session_branch_suffix_expression_for_totality ->
    (forall continuation_path continuation_input continuation_rest continuation,
      List.length continuation_input < parent_length ->
      Derives phase1_surface_rules continuation_path
        (ENonterminal "session_expression")
        continuation_input continuation_rest
        (phase1_surface_recursive_transfer_session_spine_tree continuation) ->
      exists fuel converted,
        phase1_surface_normalize_mutual_recursive_continuation_fuel
          fuel continuation = Some converted) ->
    exists fuel refined,
      phase1_surface_normalize_mutual_recursive_session_branch_tail_fuel
        fuel branches = Some refined.
Proof.
  intros parent_length path body input rest branches
    Hinput Hderive Hbody_shape Hsolver.
  subst body.
  revert input rest Hinput Hderive.
  induction branches as [|branch branches IH];
    intros input rest Hinput Hderive.
  - cbn in Hderive.
    inversion Hderive; subst.
    exists 1, Phase1MutualRecursiveBranchTailNil.
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
        [ ELiteral "|";
          ENonterminal "session_branch"
        ]
        input middle0
        (phase1_surface_session_branch_suffix_tree
          (phase1_surface_continuation_refined_session_branch_spine_tree branch))
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
        (phase1_surface_continuation_refined_session_branch_spine_tree branch)
        |- _ =>
        pose proof
          (phase1_surface_derivation_rest_length_le_input
            _ _ _ _ _ Hpipe) as Hpipe_length;
        assert (Hbranch_bound :
          List.length branch_input < parent_length) by lia;
        destruct
          (phase1_surface_normalize_mutual_recursive_session_branch_fuel_total_from_derivation
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
      (phase1_surface_normalize_mutual_recursive_session_branch_fuel_monotone
        branch_fuel fuel branch refined_branch
        (Nat.le_max_l branch_fuel rest_fuel) Hbranch_normalize)
      as Hbranch_lifted.
    pose proof
      (phase1_surface_normalize_mutual_recursive_session_branch_tail_fuel_monotone
        rest_fuel fuel branches refined_rest
        (Nat.le_max_r branch_fuel rest_fuel) Hrest_normalize)
      as Hrest_lifted.
    exists fuel,
      (Phase1MutualRecursiveBranchTailCons refined_branch refined_rest).
    unfold phase1_surface_normalize_mutual_recursive_session_branch_tail_fuel.
    cbn.
    fold phase1_surface_normalize_mutual_recursive_session_branch_fuel.
    fold phase1_surface_normalize_mutual_recursive_session_branch_tail_fuel.
    rewrite Hbranch_lifted, Hrest_lifted.
    reflexivity.
Qed.

Lemma
  phase1_surface_normalize_mutual_recursive_session_choice_fuel_total_from_derivation :
  forall direction path input rest choice,
    Derives phase1_surface_rules path
      (phase1_surface_session_choice_expression_for_totality direction)
      input rest
      (phase1_surface_continuation_refined_session_choice_spine_tree choice) ->
    (forall continuation_path continuation_input continuation_rest continuation,
      List.length continuation_input < List.length input ->
      Derives phase1_surface_rules continuation_path
        (ENonterminal "session_expression")
        continuation_input continuation_rest
        (phase1_surface_recursive_transfer_session_spine_tree continuation) ->
      exists fuel converted,
        phase1_surface_normalize_mutual_recursive_continuation_fuel
          fuel continuation = Some converted) ->
    exists fuel refined,
      phase1_surface_normalize_mutual_recursive_session_choice_fuel
        fuel choice = Some refined.
Proof.
  intros direction path input rest
    [choice_direction first_branch rest_branches]
    Hderive Hsolver.
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
      (phase1_surface_continuation_refined_session_choice_spine_tree
        {| phase1_continuation_refined_session_choice_direction :=
             choice_direction;
           phase1_continuation_refined_session_choice_first_branch := first_branch;
           phase1_continuation_refined_session_choice_rest_branches :=
             rest_branches |})
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
      [ rewrite Hkeyword_input, Hkeyword_rest;
        cbn;
        lia
      | idtac ]
  end.
  match goal with
  | Hopen : Derives phase1_surface_rules _
      (ELiteral "{") ?open_input ?first_input _,
    Hfirst : Derives phase1_surface_rules _
      (ENonterminal "session_branch") ?first_input ?repetition_input
      (phase1_surface_continuation_refined_session_branch_spine_tree first_branch),
    Hrest : Derives phase1_surface_rules _
      (ERepetition phase1_surface_session_branch_suffix_expression_for_totality)
      ?repetition_input ?after_repetition
      (PTRepetition
        (map
          (fun branch =>
            phase1_surface_session_branch_suffix_tree
              (phase1_surface_continuation_refined_session_branch_spine_tree branch))
          rest_branches))
      |- _ =>
      pose proof
        (phase1_surface_derivation_rest_length_le_input
          _ _ _ _ _ Hopen) as Hopen_length;
      assert (Hfirst_bound :
        List.length first_input < List.length input) by lia;
      destruct
        (phase1_surface_normalize_mutual_recursive_session_branch_fuel_total_from_derivation
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
            (map
              (fun branch =>
                phase1_surface_session_branch_suffix_tree
                  (phase1_surface_continuation_refined_session_branch_spine_tree
                    branch))
              rest_branches))
          Hrest)
        as [rest_trees [Hrest_tree Hrest_derive]];
      cbn in Hrest_tree;
      inversion Hrest_tree; subst rest_trees;
      destruct
        (phase1_surface_normalize_mutual_recursive_session_branch_tail_fuel_total_from_repetition
          (List.length input) _ _
          repetition_input after_repetition rest_branches
          Hrest_bound Hrest_derive eq_refl Hsolver)
        as [rest_fuel [refined_rest Hrest_normalize]];
      let fuel := constr:(Nat.max first_fuel rest_fuel) in
      pose proof
        (phase1_surface_normalize_mutual_recursive_session_branch_fuel_monotone
          first_fuel fuel first_branch refined_first
          (Nat.le_max_l first_fuel rest_fuel) Hfirst_normalize)
        as Hfirst_lifted;
      pose proof
        (phase1_surface_normalize_mutual_recursive_session_branch_tail_fuel_monotone
          rest_fuel fuel rest_branches refined_rest
          (Nat.le_max_r first_fuel rest_fuel) Hrest_normalize)
        as Hrest_lifted;
      exists fuel,
        (Phase1MutualRecursiveChoice choice_direction
          refined_first refined_rest);
      unfold phase1_surface_normalize_mutual_recursive_session_choice_fuel;
      unfold phase1_surface_normalize_mutual_recursive_session_choice_with;
      cbn;
      fold phase1_surface_normalize_mutual_recursive_session_branch_fuel;
      fold phase1_surface_normalize_mutual_recursive_session_branch_tail_fuel;
      rewrite Hfirst_lifted, Hrest_lifted;
      reflexivity
  end.
Qed.

Lemma
  phase1_surface_normalize_mutual_recursive_session_spine_fuel_total_measure :
  forall measure path input rest tree session,
    List.length input < measure ->
    Derives phase1_surface_rules path
      (ENonterminal "session_expression") input rest tree ->
    phase1_surface_choice_refined_recursive_session_spine_tree session = tree ->
    exists fuel refined,
      phase1_surface_normalize_mutual_recursive_session_spine_fuel
        fuel session = Some refined.
Proof.
  induction measure as [|measure IH];
    intros path input rest tree session Hmeasure Hderive Htree.
  - lia.
  - rewrite <- Htree in Hderive.
    assert (Hsolver :
      forall continuation_path continuation_input continuation_rest continuation,
        List.length continuation_input < List.length input ->
        Derives phase1_surface_rules continuation_path
          (ENonterminal "session_expression")
          continuation_input continuation_rest
          (phase1_surface_recursive_transfer_session_spine_tree continuation) ->
        exists fuel converted,
          phase1_surface_normalize_mutual_recursive_continuation_fuel
            fuel continuation = Some converted).
    {
      intros continuation_path continuation_input continuation_rest
        continuation Hshorter Hcontinuation.
      destruct
        (phase1_surface_normalize_choice_refined_recursive_session_spine_fuel_total_from_derivation
          continuation_path continuation_input continuation_rest
          (phase1_surface_recursive_transfer_session_spine_tree continuation)
          continuation Hcontinuation eq_refl)
        as [step_fuel [step Hstep]].
      pose proof
        (phase1_surface_normalize_choice_refined_recursive_session_spine_fuel_round_trip
          step_fuel continuation step Hstep) as Hstep_tree.
      assert (Hrecursive_measure :
        List.length continuation_input < measure) by lia.
      destruct
        (IH continuation_path continuation_input continuation_rest
          (phase1_surface_recursive_transfer_session_spine_tree continuation)
          step Hrecursive_measure Hcontinuation Hstep_tree)
        as [recursive_fuel [converted Hrecursive]].
      let fuel := constr:(Nat.max step_fuel recursive_fuel) in
      pose proof
        (phase1_surface_normalize_choice_refined_recursive_session_spine_fuel_monotone
          step_fuel fuel continuation step
          (Nat.le_max_l step_fuel recursive_fuel) Hstep)
        as Hstep_lifted.
      pose proof
        (phase1_surface_normalize_mutual_recursive_session_spine_fuel_monotone
          recursive_fuel fuel step converted
          (Nat.le_max_r step_fuel recursive_fuel) Hrecursive)
        as Hrecursive_lifted.
      exists fuel, converted.
      unfold phase1_surface_normalize_mutual_recursive_continuation_fuel.
      rewrite Hstep_lifted.
      exact Hrecursive_lifted.
    }
    destruct session as [nonreference | reference_tree].
    + destruct nonreference as
        [direction parameter boundary guard continuation
        |choice
        |choice
        |selected_tree
        |selected_tree
        |selected_tree].
      * assert (Htransfer_tree :
          phase1_surface_guard_refined_boundary_typed_transfer_session_spine_tree
            (Phase1GuardRefinedBoundaryTypedTransferNonreferenceSession
              (Phase1GuardRefinedBoundaryTypedTransferSession
                {| phase1_guard_refined_transfer_direction := direction;
                   phase1_guard_refined_transfer_parameter := parameter;
                   phase1_guard_refined_transfer_boundary := boundary;
                   phase1_guard_refined_transfer_guard := guard;
                   phase1_guard_refined_transfer_continuation_tree :=
                     phase1_surface_recursive_transfer_session_spine_tree
                       continuation |})) =
          phase1_surface_choice_refined_recursive_session_spine_tree
            (Phase1ChoiceRefinedRecursiveNonreferenceSession
              (Phase1ChoiceRefinedRecursiveTransferSession
                direction parameter boundary guard continuation))).
        {
          reflexivity.
        }
        destruct
          (phase1_surface_guard_refined_transfer_continuation_derivation_shorter
            path input rest
            (phase1_surface_choice_refined_recursive_session_spine_tree
              (Phase1ChoiceRefinedRecursiveNonreferenceSession
                (Phase1ChoiceRefinedRecursiveTransferSession
                  direction parameter boundary guard continuation)))
            {| phase1_guard_refined_transfer_direction := direction;
               phase1_guard_refined_transfer_parameter := parameter;
               phase1_guard_refined_transfer_boundary := boundary;
               phase1_guard_refined_transfer_guard := guard;
               phase1_guard_refined_transfer_continuation_tree :=
                 phase1_surface_recursive_transfer_session_spine_tree
                   continuation |}
            Hderive Htransfer_tree)
          as [continuation_path [continuation_input [continuation_rest
            [Hcontinuation Hshorter]]]].
        destruct
          (Hsolver continuation_path continuation_input continuation_rest
            continuation Hshorter Hcontinuation)
          as [fuel [converted Hconverted]].
        exists (S fuel),
          (Phase1MutualRecursiveNonreferenceSession
            (Phase1MutualRecursiveTransferSession
              direction parameter boundary guard converted)).
        cbn [phase1_surface_normalize_mutual_recursive_session_spine_fuel].
        fold phase1_surface_normalize_mutual_recursive_continuation_fuel.
        rewrite Hconverted.
        reflexivity.
      * destruct
          (phase1_surface_selected_choice_derivation
            Phase1SessionSelect path input rest
            (phase1_surface_continuation_refined_session_choice_spine_tree choice)
            Hderive)
          as [choice_path Hchoice].
        destruct
          (phase1_surface_normalize_mutual_recursive_session_choice_fuel_total_from_derivation
            Phase1SessionSelect choice_path input rest choice
            Hchoice Hsolver)
          as [fuel [refined_choice Hchoice_normalize]].
        exists (S fuel),
          (Phase1MutualRecursiveNonreferenceSession
            (Phase1MutualRecursiveSelectSession refined_choice)).
        cbn [phase1_surface_normalize_mutual_recursive_session_spine_fuel].
        fold phase1_surface_normalize_mutual_recursive_continuation_fuel.
        change
          (match
            phase1_surface_normalize_mutual_recursive_session_choice_fuel
              fuel choice
          with
          | Some refined =>
              Some
                (Phase1MutualRecursiveNonreferenceSession
                  (Phase1MutualRecursiveSelectSession refined))
          | None => None
          end =
          Some
            (Phase1MutualRecursiveNonreferenceSession
              (Phase1MutualRecursiveSelectSession refined_choice))).
        rewrite Hchoice_normalize.
        reflexivity.
      * destruct
          (phase1_surface_selected_choice_derivation
            Phase1SessionOffer path input rest
            (phase1_surface_continuation_refined_session_choice_spine_tree choice)
            Hderive)
          as [choice_path Hchoice].
        destruct
          (phase1_surface_normalize_mutual_recursive_session_choice_fuel_total_from_derivation
            Phase1SessionOffer choice_path input rest choice
            Hchoice Hsolver)
          as [fuel [refined_choice Hchoice_normalize]].
        exists (S fuel),
          (Phase1MutualRecursiveNonreferenceSession
            (Phase1MutualRecursiveOfferSession refined_choice)).
        cbn [phase1_surface_normalize_mutual_recursive_session_spine_fuel].
        fold phase1_surface_normalize_mutual_recursive_continuation_fuel.
        change
          (match
            phase1_surface_normalize_mutual_recursive_session_choice_fuel
              fuel choice
          with
          | Some refined =>
              Some
                (Phase1MutualRecursiveNonreferenceSession
                  (Phase1MutualRecursiveOfferSession refined))
          | None => None
          end =
          Some
            (Phase1MutualRecursiveNonreferenceSession
              (Phase1MutualRecursiveOfferSession refined_choice))).
        rewrite Hchoice_normalize.
        reflexivity.
      * exists 1,
          (Phase1MutualRecursiveNonreferenceSession
            (Phase1MutualRecursiveEndSession selected_tree)).
        reflexivity.
      * exists 1,
          (Phase1MutualRecursiveNonreferenceSession
            (Phase1MutualRecursiveRecursiveSession selected_tree)).
        reflexivity.
      * exists 1,
          (Phase1MutualRecursiveNonreferenceSession
            (Phase1MutualRecursiveContinueSession selected_tree)).
        reflexivity.
    + exists 1, (Phase1MutualRecursiveStaticReferenceSession reference_tree).
      reflexivity.
Qed.

Definition phase1_surface_normalize_mutual_recursive_session_tree_fuel
  (fuel : nat)
  (tree : ParseTree)
  : option Phase1SurfaceMutualRecursiveSessionSpine :=
  match
    phase1_surface_normalize_choice_refined_recursive_session_tree_fuel fuel tree
  with
  | Some step =>
      phase1_surface_normalize_mutual_recursive_session_spine_fuel fuel step
  | None => None
  end.

Theorem
  phase1_surface_normalize_mutual_recursive_session_tree_fuel_round_trip :
  forall fuel tree refined,
    phase1_surface_normalize_mutual_recursive_session_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_mutual_recursive_session_spine_tree refined = tree.
Proof.
  intros fuel tree refined Hnormalize.
  unfold phase1_surface_normalize_mutual_recursive_session_tree_fuel
    in Hnormalize.
  destruct
    (phase1_surface_normalize_choice_refined_recursive_session_tree_fuel
      fuel tree)
    as [step |] eqn:Hstep; try discriminate Hnormalize.
  transitivity
    (phase1_surface_choice_refined_recursive_session_spine_tree step).
  - eapply phase1_surface_normalize_mutual_recursive_session_spine_fuel_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_choice_refined_recursive_session_tree_fuel_round_trip.
    exact Hstep.
Qed.

Theorem
  phase1_surface_normalize_mutual_recursive_session_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "session_expression") input rest tree ->
    exists fuel refined,
      phase1_surface_normalize_mutual_recursive_session_tree_fuel
        fuel tree = Some refined /\
      phase1_surface_mutual_recursive_session_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_choice_refined_recursive_session_tree_fuel_total_from_derivation
      path input rest tree Hderive)
    as [step_fuel [step [Hstep Hstep_tree]]].
  destruct
    (phase1_surface_normalize_mutual_recursive_session_spine_fuel_total_measure
      (S (List.length input)) path input rest tree step
      (Nat.lt_succ_diag_r (List.length input))
      Hderive Hstep_tree)
    as [recursive_fuel [refined Hrecursive]].
  let fuel := constr:(Nat.max step_fuel recursive_fuel) in
  pose proof
    (phase1_surface_normalize_choice_refined_recursive_session_tree_fuel_monotone
      step_fuel fuel tree step
      (Nat.le_max_l step_fuel recursive_fuel) Hstep)
    as Hstep_lifted.
  pose proof
    (phase1_surface_normalize_mutual_recursive_session_spine_fuel_monotone
      recursive_fuel fuel step refined
      (Nat.le_max_r step_fuel recursive_fuel) Hrecursive)
    as Hrecursive_lifted.
  assert (Hresult :
    phase1_surface_normalize_mutual_recursive_session_tree_fuel
      fuel tree = Some refined).
  {
    unfold phase1_surface_normalize_mutual_recursive_session_tree_fuel.
    rewrite Hstep_lifted.
    exact Hrecursive_lifted.
  }
  exists fuel, refined.
  split.
  - exact Hresult.
  - eapply
      phase1_surface_normalize_mutual_recursive_session_tree_fuel_round_trip.
    exact Hresult.
Qed.
