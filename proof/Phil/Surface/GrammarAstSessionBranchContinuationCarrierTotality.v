From Stdlib Require Import Arith.PeanoNat Lists.List Strings.String Lia.

From Phil.Surface Require Import
  GrammarAstSessionBranchContinuationCarrierSpine
  GrammarAstSessionBranchGuardCarrierTotality
  GrammarAstSessionTransferRecursiveClosureTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the continuation-refined select/offer branch carrier from #1060. *)

Lemma phase1_surface_normalize_recursive_transfer_session_spine_fuel_monotone :
  forall fuel larger session refined,
    fuel <= larger ->
    phase1_surface_normalize_recursive_transfer_session_spine_fuel
      fuel session = Some refined ->
    phase1_surface_normalize_recursive_transfer_session_spine_fuel
      larger session = Some refined.
Proof.
  induction fuel as [|fuel IH]; intros larger session refined Hle Hnormalize.
  - discriminate Hnormalize.
  - destruct larger as [|larger].
    + lia.
    + cbn in Hnormalize |- *.
      destruct
        (phase1_surface_normalize_continuation_refined_transfer_session_spine
          session)
        as [step |] eqn:Hstep; try discriminate Hnormalize.
      rewrite Hstep.
      destruct step as [nonreference | reference_tree].
      * destruct nonreference as
          [transfer | selected | selected | selected | selected | selected].
        -- destruct
             (phase1_surface_normalize_recursive_transfer_session_spine_fuel
               fuel
               (phase1_continuation_refined_transfer_continuation transfer))
             as [continuation |] eqn:Hcontinuation;
             try discriminate Hnormalize.
           inversion Hnormalize; subst refined.
           assert (Hfuel : fuel <= larger) by lia.
           rewrite
             (IH larger
               (phase1_continuation_refined_transfer_continuation transfer)
               continuation Hfuel Hcontinuation).
           reflexivity.
        -- inversion Hnormalize; subst refined. reflexivity.
        -- inversion Hnormalize; subst refined. reflexivity.
        -- inversion Hnormalize; subst refined. reflexivity.
        -- inversion Hnormalize; subst refined. reflexivity.
        -- inversion Hnormalize; subst refined. reflexivity.
      * inversion Hnormalize; subst refined.
        reflexivity.
Qed.

Lemma phase1_surface_normalize_recursive_transfer_session_tree_fuel_monotone :
  forall fuel larger tree refined,
    fuel <= larger ->
    phase1_surface_normalize_recursive_transfer_session_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_normalize_recursive_transfer_session_tree_fuel
      larger tree = Some refined.
Proof.
  intros fuel larger tree refined Hle Hnormalize.
  unfold phase1_surface_normalize_recursive_transfer_session_tree_fuel
    in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_guard_refined_boundary_typed_transfer_session_tree
      tree)
    as [session |] eqn:Hsession; try discriminate Hnormalize.
  eapply phase1_surface_normalize_recursive_transfer_session_spine_fuel_monotone.
  - exact Hle.
  - exact Hnormalize.
Qed.

Lemma
  phase1_surface_normalize_continuation_refined_session_branch_spine_fuel_monotone :
  forall fuel larger branch refined,
    fuel <= larger ->
    phase1_surface_normalize_continuation_refined_session_branch_spine_fuel
      fuel branch = Some refined ->
    phase1_surface_normalize_continuation_refined_session_branch_spine_fuel
      larger branch = Some refined.
Proof.
  intros fuel larger
    [label params boundary guard continuation_tree]
    refined Hle Hnormalize.
  cbn in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_recursive_transfer_session_tree_fuel
      fuel continuation_tree)
    as [continuation |] eqn:Hcontinuation; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  pose proof
    (phase1_surface_normalize_recursive_transfer_session_tree_fuel_monotone
      fuel larger continuation_tree continuation Hle Hcontinuation)
    as Hlarger.
  rewrite Hlarger.
  reflexivity.
Qed.

Lemma
  phase1_surface_normalize_continuation_refined_session_branch_spines_fuel_monotone :
  forall fuel larger branches refined,
    fuel <= larger ->
    phase1_surface_normalize_continuation_refined_session_branch_spines_fuel
      fuel branches = Some refined ->
    phase1_surface_normalize_continuation_refined_session_branch_spines_fuel
      larger branches = Some refined.
Proof.
  intros fuel larger branches.
  induction branches as [|branch rest IH]; intros refined Hle Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize |- *.
    destruct
      (phase1_surface_normalize_continuation_refined_session_branch_spine_fuel
        fuel branch)
      as [refined_branch |] eqn:Hbranch; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_continuation_refined_session_branch_spines_fuel
        fuel rest)
      as [refined_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    rewrite
      (phase1_surface_normalize_continuation_refined_session_branch_spine_fuel_monotone
        fuel larger branch refined_branch Hle Hbranch).
    rewrite (IH refined_rest Hle Hrest).
    reflexivity.
Qed.

Lemma
  phase1_surface_normalize_continuation_refined_session_branch_spine_fuel_total_from_derivation :
  forall path input rest branch,
    Derives phase1_surface_rules path
      (ENonterminal "session_branch") input rest
      (phase1_surface_guard_refined_session_branch_spine_tree branch) ->
    exists fuel refined,
      phase1_surface_normalize_continuation_refined_session_branch_spine_fuel
        fuel branch = Some refined.
Proof.
  intros path input rest branch Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "session_branch"
      input rest
      (phase1_surface_guard_refined_session_branch_spine_tree branch)
      Hderive)
    as [body [subtree [Hlookup [Hnode Hbody]]]].
  rewrite phase1_surface_session_branch_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  unfold phase1_surface_session_branch_expression_for_totality in Hbody.
  cbn [phase1_surface_guard_refined_session_branch_spine_tree] in Hnode.
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
        [ phase1_surface_identifier_tree
            (phase1_guard_refined_session_branch_label branch);
          phase1_surface_session_branch_params_tree
            (phase1_guard_refined_session_branch_params branch);
          phase1_surface_boundary_refined_annotation_tree
            (phase1_guard_refined_session_branch_boundary branch);
          phase1_surface_guard_refined_annotation_tree
            (phase1_guard_refined_session_branch_guard branch);
          PTLiteral "=>";
          phase1_guard_refined_session_branch_continuation_tree branch
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
  | Hcontinuation : Derives phase1_surface_rules _
      (ENonterminal "session_expression")
      ?continuation_input ?continuation_rest
      (phase1_guard_refined_session_branch_continuation_tree branch) |- _ =>
      destruct
        (phase1_surface_normalize_recursive_transfer_session_tree_total_from_derivation
          _ continuation_input continuation_rest
          (phase1_guard_refined_session_branch_continuation_tree branch)
          Hcontinuation)
        as [continuation [Hcontinuation_normalize Hcontinuation_tree]];
      exists (S (List.length continuation_input));
      exists
        {| phase1_continuation_refined_session_branch_label :=
             phase1_guard_refined_session_branch_label branch;
           phase1_continuation_refined_session_branch_params :=
             phase1_guard_refined_session_branch_params branch;
           phase1_continuation_refined_session_branch_boundary :=
             phase1_guard_refined_session_branch_boundary branch;
           phase1_continuation_refined_session_branch_guard :=
             phase1_guard_refined_session_branch_guard branch;
           phase1_continuation_refined_session_branch_continuation :=
             continuation |};
      unfold
        phase1_surface_normalize_continuation_refined_session_branch_spine_fuel;
      rewrite Hcontinuation_normalize;
      reflexivity
  end.
Qed.

Lemma
  phase1_surface_normalize_continuation_refined_session_branch_spines_fuel_total_from_repetition :
  forall path body input rest branches,
    DerivesRepetition phase1_surface_rules path body input rest
      (map
        (fun branch =>
          phase1_surface_session_branch_suffix_tree
            (phase1_surface_guard_refined_session_branch_spine_tree branch))
        branches) ->
    body = phase1_surface_session_branch_suffix_expression_for_totality ->
    exists fuel refined,
      phase1_surface_normalize_continuation_refined_session_branch_spines_fuel
        fuel branches = Some refined.
Proof.
  intros path body input rest branches Hderive Hbody_shape.
  subst body.
  revert input rest Hderive.
  induction branches as [|branch branches IH]; intros input rest Hderive.
  - cbn in Hderive.
    inversion Hderive; subst.
    exists 1, [].
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
          (phase1_surface_guard_refined_session_branch_spine_tree branch))
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
    | Hbranch : Derives phase1_surface_rules _
        (ENonterminal "session_branch") _ _
        (phase1_surface_guard_refined_session_branch_spine_tree branch) |- _ =>
        destruct
          (phase1_surface_normalize_continuation_refined_session_branch_spine_fuel_total_from_derivation
            _ _ _ branch Hbranch)
          as [branch_fuel [refined_branch Hbranch_normalize]];
        destruct (IH _ _ Hrest)
          as [rest_fuel [refined_rest Hrest_normalize]];
        let fuel := constr:(Nat.max branch_fuel rest_fuel) in
        pose proof
          (phase1_surface_normalize_continuation_refined_session_branch_spine_fuel_monotone
            branch_fuel fuel branch refined_branch
            (Nat.le_max_l branch_fuel rest_fuel) Hbranch_normalize)
          as Hbranch_lifted;
        pose proof
          (phase1_surface_normalize_continuation_refined_session_branch_spines_fuel_monotone
            rest_fuel fuel branches refined_rest
            (Nat.le_max_r branch_fuel rest_fuel) Hrest_normalize)
          as Hrest_lifted;
        exists fuel, (refined_branch :: refined_rest);
        cbn;
        rewrite Hbranch_lifted, Hrest_lifted;
        reflexivity
    end.
Qed.

Theorem
  phase1_surface_normalize_continuation_refined_session_choice_tree_fuel_total_from_derivation :
  forall direction path input rest tree,
    Derives phase1_surface_rules path
      (phase1_surface_session_choice_expression_for_totality direction)
      input rest tree ->
    exists fuel choice,
      phase1_surface_normalize_continuation_refined_session_choice_tree_fuel
        fuel direction tree = Some choice /\
      phase1_surface_continuation_refined_session_choice_spine_tree choice = tree.
Proof.
  intros direction path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_guard_refined_session_choice_tree_total_from_derivation
      direction path input rest tree Hderive)
    as [guard_choice [Hguard_normalize Hguard_tree]].
  destruct guard_choice as [choice_direction first_branch rest_branches].
  cbn in Hguard_tree, Hguard_normalize.
  rewrite <- Hguard_tree in Hderive.
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
      (phase1_surface_guard_refined_session_choice_spine_tree
        {| phase1_guard_refined_session_choice_direction := choice_direction;
           phase1_guard_refined_session_choice_first_branch := first_branch;
           phase1_guard_refined_session_choice_rest_branches := rest_branches |})
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
  | Hfirst : Derives phase1_surface_rules _
      (ENonterminal "session_branch") _ _
      (phase1_surface_guard_refined_session_branch_spine_tree first_branch),
    Hrest : Derives phase1_surface_rules _
      (ERepetition phase1_surface_session_branch_suffix_expression_for_totality)
      _ _
      (PTRepetition
        (map
          (fun branch =>
            phase1_surface_session_branch_suffix_tree
              (phase1_surface_guard_refined_session_branch_spine_tree branch))
          rest_branches)) |- _ =>
      destruct
        (phase1_surface_normalize_continuation_refined_session_branch_spine_fuel_total_from_derivation
          _ _ _ first_branch Hfirst)
        as [first_fuel [refined_first Hfirst_normalize]];
      destruct
        (phase1_surface_repetition_derivation_exposes
          _ phase1_surface_session_branch_suffix_expression_for_totality
          _ _
          (PTRepetition
            (map
              (fun branch =>
                phase1_surface_session_branch_suffix_tree
                  (phase1_surface_guard_refined_session_branch_spine_tree branch))
              rest_branches))
          Hrest)
        as [rest_trees [Hrest_tree Hrest_derive]];
      cbn in Hrest_tree;
      inversion Hrest_tree; subst rest_trees;
      destruct
        (phase1_surface_normalize_continuation_refined_session_branch_spines_fuel_total_from_repetition
          _ _ _ _ rest_branches Hrest_derive eq_refl)
        as [rest_fuel [refined_rest Hrest_normalize]];
      let fuel := constr:(Nat.max first_fuel rest_fuel) in
      pose proof
        (phase1_surface_normalize_continuation_refined_session_branch_spine_fuel_monotone
          first_fuel fuel first_branch refined_first
          (Nat.le_max_l first_fuel rest_fuel) Hfirst_normalize)
        as Hfirst_lifted;
      pose proof
        (phase1_surface_normalize_continuation_refined_session_branch_spines_fuel_monotone
          rest_fuel fuel rest_branches refined_rest
          (Nat.le_max_r first_fuel rest_fuel) Hrest_normalize)
        as Hrest_lifted;
      let choice := constr:(
        {| phase1_continuation_refined_session_choice_direction :=
             choice_direction;
           phase1_continuation_refined_session_choice_first_branch :=
             refined_first;
           phase1_continuation_refined_session_choice_rest_branches :=
             refined_rest |}) in
      assert (Hchoice :
        phase1_surface_normalize_continuation_refined_session_choice_spine_fuel
          fuel
          {| phase1_guard_refined_session_choice_direction := choice_direction;
             phase1_guard_refined_session_choice_first_branch := first_branch;
             phase1_guard_refined_session_choice_rest_branches := rest_branches |} =
          Some choice).
      [ cbn;
        rewrite Hfirst_lifted, Hrest_lifted;
        reflexivity
      | assert (Hnormalize :
          phase1_surface_normalize_continuation_refined_session_choice_tree_fuel
            fuel direction tree = Some choice);
        [ unfold
            phase1_surface_normalize_continuation_refined_session_choice_tree_fuel;
          rewrite Hguard_normalize;
          exact Hchoice
        | exists fuel, choice;
          split;
          [ exact Hnormalize
          | eapply
              phase1_surface_normalize_continuation_refined_session_choice_tree_fuel_round_trip;
            exact Hnormalize ] ] ]
  end.
Qed.
