From Stdlib Require Import Arith.PeanoNat Lists.List Strings.String Lia.

From Phil.Surface Require Import
  GrammarAstSessionRecursiveBodyChoiceOneStepCarrierSpine
  GrammarAstSessionRecursiveBodyTransferRecursiveCarrierTotality
  GrammarAstSessionRecursiveBodyOneStepCarrierTotality
  GrammarAstSessionRecursiveOneStepCarrierTotality
  GrammarAstSessionMutualRecursiveClosureTotality
  GrammarAstSessionBranchTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Converse for one-step select/offer propagation of recursive-body refinement
  from #1127.

  All branch continuations share the same body-source, body-closure, and
  transfer-recursion fuels.  This proof closes monotonicity in those fuels,
  then combines the finite branch requirements componentwise with Nat.max.
  There is no recursive session hypothesis in this layer.
*)

Lemma
  phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels_transfer_monotone :
  forall body_source_fuel body_closure_fuel transfer_fuel larger_transfer
    session refined,
    transfer_fuel <= larger_transfer ->
    phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels
      body_source_fuel body_closure_fuel transfer_fuel session = Some refined ->
    phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels
      body_source_fuel body_closure_fuel larger_transfer session = Some refined.
Proof.
  induction transfer_fuel as [|transfer_fuel IH];
    intros larger_transfer session refined Hle Hnormalize.
  - discriminate Hnormalize.
  - destruct larger_transfer as [|larger_transfer].
    + lia.
    + assert (Hremaining : transfer_fuel <= larger_transfer) by lia.
      assert (Hcontinuation :
        forall continuation converted,
          (match
            phase1_surface_normalize_recursive_one_step_session_spine continuation
          with
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
          end) = Some converted ->
          (match
            phase1_surface_normalize_recursive_one_step_session_spine continuation
          with
          | Some shell =>
              match
                phase1_surface_normalize_recursive_body_one_step_session_spine_fuels
                  body_source_fuel body_closure_fuel shell
              with
              | Some body_step =>
                  phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels
                    body_source_fuel body_closure_fuel larger_transfer body_step
              | None => None
              end
          | None => None
          end) = Some converted).
      {
        intros continuation converted Hconverted.
        destruct
          (phase1_surface_normalize_recursive_one_step_session_spine continuation)
          as [shell |] eqn:Hshell; try discriminate Hconverted.
        destruct
          (phase1_surface_normalize_recursive_body_one_step_session_spine_fuels
            body_source_fuel body_closure_fuel shell)
          as [body_step |] eqn:Hbody; try discriminate Hconverted.
        rewrite Hshell, Hbody.
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
          |payload
          |payload].
        -- cbn [phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels]
             in Hnormalize |- *.
           destruct
             (match
               phase1_surface_normalize_recursive_one_step_session_spine continuation
             with
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
             end)
             as [converted |] eqn:Hconverted; try discriminate Hnormalize.
           inversion Hnormalize; subst refined.
           rewrite (Hcontinuation continuation converted Hconverted).
           reflexivity.
        -- inversion Hnormalize; subst refined. reflexivity.
        -- inversion Hnormalize; subst refined. reflexivity.
        -- inversion Hnormalize; subst refined. reflexivity.
        -- inversion Hnormalize; subst refined. reflexivity.
        -- inversion Hnormalize; subst refined. reflexivity.
      * inversion Hnormalize; subst refined.
        reflexivity.
Qed.

Lemma
  phase1_surface_normalize_recursive_body_choice_one_step_continuation_fuels_monotone :
  forall source_fuel larger_source closure_fuel larger_closure
    transfer_fuel larger_transfer continuation refined,
    source_fuel <= larger_source ->
    closure_fuel <= larger_closure ->
    transfer_fuel <= larger_transfer ->
    phase1_surface_normalize_recursive_body_choice_one_step_continuation_fuels
      source_fuel closure_fuel transfer_fuel continuation = Some refined ->
    phase1_surface_normalize_recursive_body_choice_one_step_continuation_fuels
      larger_source larger_closure larger_transfer continuation = Some refined.
Proof.
  intros source_fuel larger_source closure_fuel larger_closure
    transfer_fuel larger_transfer continuation refined
    Hsource Hclosure Htransfer Hnormalize.
  unfold
    phase1_surface_normalize_recursive_body_choice_one_step_continuation_fuels
    in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_recursive_one_step_session_spine continuation)
    as [shell |] eqn:Hshell; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_recursive_body_one_step_session_spine_fuels
      source_fuel closure_fuel shell)
    as [body_step |] eqn:Hbody; try discriminate Hnormalize.
  pose proof
    (phase1_surface_normalize_recursive_body_one_step_session_spine_fuels_monotone
      source_fuel larger_source closure_fuel larger_closure
      shell body_step Hsource Hclosure Hbody)
    as Hbody_larger.
  rewrite Hshell, Hbody_larger.
  pose proof
    (phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels_body_monotone
      source_fuel larger_source closure_fuel larger_closure
      transfer_fuel body_step refined
      Hsource Hclosure Hnormalize)
    as Hbody_fuels_larger.
  eapply
    phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels_transfer_monotone.
  - exact Htransfer.
  - exact Hbody_fuels_larger.
Qed.

Lemma
  phase1_surface_normalize_recursive_body_choice_one_step_session_branch_spine_fuels_monotone :
  forall source_fuel larger_source closure_fuel larger_closure
    transfer_fuel larger_transfer branch refined,
    source_fuel <= larger_source ->
    closure_fuel <= larger_closure ->
    transfer_fuel <= larger_transfer ->
    phase1_surface_normalize_recursive_body_choice_one_step_session_branch_spine_fuels
      source_fuel closure_fuel transfer_fuel branch = Some refined ->
    phase1_surface_normalize_recursive_body_choice_one_step_session_branch_spine_fuels
      larger_source larger_closure larger_transfer branch = Some refined.
Proof.
  intros source_fuel larger_source closure_fuel larger_closure
    transfer_fuel larger_transfer
    [label params boundary guard continuation] refined
    Hsource Hclosure Htransfer Hnormalize.
  cbn in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_recursive_body_choice_one_step_continuation_fuels
      source_fuel closure_fuel transfer_fuel continuation)
    as [converted |] eqn:Hconverted; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  pose proof
    (phase1_surface_normalize_recursive_body_choice_one_step_continuation_fuels_monotone
      source_fuel larger_source closure_fuel larger_closure
      transfer_fuel larger_transfer continuation converted
      Hsource Hclosure Htransfer Hconverted)
    as Hconverted_larger.
  rewrite Hconverted_larger.
  reflexivity.
Qed.

Lemma
  phase1_surface_normalize_recursive_body_choice_one_step_session_branch_tail_spine_fuels_monotone :
  forall source_fuel larger_source closure_fuel larger_closure
    transfer_fuel larger_transfer branches refined,
    source_fuel <= larger_source ->
    closure_fuel <= larger_closure ->
    transfer_fuel <= larger_transfer ->
    phase1_surface_normalize_recursive_body_choice_one_step_session_branch_tail_spine_fuels
      source_fuel closure_fuel transfer_fuel branches = Some refined ->
    phase1_surface_normalize_recursive_body_choice_one_step_session_branch_tail_spine_fuels
      larger_source larger_closure larger_transfer branches = Some refined.
Proof.
  intros source_fuel larger_source closure_fuel larger_closure
    transfer_fuel larger_transfer branches.
  induction branches as [|branch rest IH];
    intros refined Hsource Hclosure Htransfer Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize |- *.
    destruct
      (phase1_surface_normalize_recursive_body_choice_one_step_session_branch_spine_fuels
        source_fuel closure_fuel transfer_fuel branch)
      as [refined_branch |] eqn:Hbranch; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_recursive_body_choice_one_step_session_branch_tail_spine_fuels
        source_fuel closure_fuel transfer_fuel rest)
      as [refined_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    pose proof
      (phase1_surface_normalize_recursive_body_choice_one_step_session_branch_spine_fuels_monotone
        source_fuel larger_source closure_fuel larger_closure
        transfer_fuel larger_transfer branch refined_branch
        Hsource Hclosure Htransfer Hbranch)
      as Hbranch_larger.
    pose proof
      (IH refined_rest Hsource Hclosure Htransfer Hrest)
      as Hrest_larger.
    rewrite Hbranch_larger, Hrest_larger.
    reflexivity.
Qed.

Lemma
  phase1_surface_normalize_recursive_body_choice_one_step_session_choice_spine_fuels_monotone :
  forall source_fuel larger_source closure_fuel larger_closure
    transfer_fuel larger_transfer choice refined,
    source_fuel <= larger_source ->
    closure_fuel <= larger_closure ->
    transfer_fuel <= larger_transfer ->
    phase1_surface_normalize_recursive_body_choice_one_step_session_choice_spine_fuels
      source_fuel closure_fuel transfer_fuel choice = Some refined ->
    phase1_surface_normalize_recursive_body_choice_one_step_session_choice_spine_fuels
      larger_source larger_closure larger_transfer choice = Some refined.
Proof.
  intros source_fuel larger_source closure_fuel larger_closure
    transfer_fuel larger_transfer
    [direction first_branch rest_branches] refined
    Hsource Hclosure Htransfer Hnormalize.
  cbn in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_recursive_body_choice_one_step_session_branch_spine_fuels
      source_fuel closure_fuel transfer_fuel first_branch)
    as [refined_first |] eqn:Hfirst; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_recursive_body_choice_one_step_session_branch_tail_spine_fuels
      source_fuel closure_fuel transfer_fuel rest_branches)
    as [refined_rest |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  pose proof
    (phase1_surface_normalize_recursive_body_choice_one_step_session_branch_spine_fuels_monotone
      source_fuel larger_source closure_fuel larger_closure
      transfer_fuel larger_transfer first_branch refined_first
      Hsource Hclosure Htransfer Hfirst)
    as Hfirst_larger.
  pose proof
    (phase1_surface_normalize_recursive_body_choice_one_step_session_branch_tail_spine_fuels_monotone
      source_fuel larger_source closure_fuel larger_closure
      transfer_fuel larger_transfer rest_branches refined_rest
      Hsource Hclosure Htransfer Hrest)
    as Hrest_larger.
  rewrite Hfirst_larger, Hrest_larger.
  reflexivity.
Qed.

Theorem
  phase1_surface_normalize_recursive_body_choice_one_step_session_spine_fuels_total_from_derivation :
  forall path input rest session,
    Derives phase1_surface_rules path
      (ENonterminal "session_expression") input rest
      (phase1_surface_recursive_body_transfer_recursive_session_spine_tree session) ->
    exists source_fuel closure_fuel transfer_fuel refined,
      phase1_surface_normalize_recursive_body_choice_one_step_session_spine_fuels
        source_fuel closure_fuel transfer_fuel session = Some refined /\
      phase1_surface_recursive_body_choice_one_step_session_spine_tree refined =
        phase1_surface_recursive_body_transfer_recursive_session_spine_tree session.
Proof.
  intros path input rest session Hderive.

  assert (Hbranch :
    forall branch_path branch_input branch_rest branch,
      Derives phase1_surface_rules branch_path
        (ENonterminal "session_branch") branch_input branch_rest
        (phase1_surface_continue_mutual_recursive_session_branch_spine_tree branch) ->
      exists source_fuel closure_fuel transfer_fuel refined_branch,
        phase1_surface_normalize_recursive_body_choice_one_step_session_branch_spine_fuels
          source_fuel closure_fuel transfer_fuel branch = Some refined_branch).
  {
    intros branch_path branch_input branch_rest
      [label params boundary guard continuation] Hbranch_derive.
    destruct
      (derives_nonterminal_exposes_body
        phase1_surface_rules branch_path "session_branch"
        branch_input branch_rest
        (phase1_surface_continue_mutual_recursive_session_branch_spine_tree
          (Phase1ContinueMutualRecursiveBranch
            label params boundary guard continuation))
        Hbranch_derive)
      as [body [subtree [Hlookup [Hnode Hbody]]]].
    rewrite phase1_surface_session_branch_lookup_for_totality in Hlookup.
    inversion Hlookup; subst body.
    unfold phase1_surface_session_branch_expression_for_totality in Hbody.
    cbn [phase1_surface_continue_mutual_recursive_session_branch_spine_tree]
      in Hnode.
    inversion Hnode; subst subtree.
    destruct
      (derives_sequence_expression_exposes_items
        phase1_surface_rules
        (descend branch_path (AtNonterminal "session_branch"))
        [ ENonterminal "identifier";
          phase1_surface_session_branch_params_expression_for_totality;
          phase1_surface_session_branch_boundary_expression_for_totality;
          phase1_surface_session_branch_guard_expression_for_totality;
          ELiteral "=>";
          ENonterminal "session_expression"
        ]
        branch_input branch_rest
        (PTSequence
          [ phase1_surface_identifier_tree label;
            phase1_surface_session_branch_params_tree params;
            phase1_surface_boundary_refined_annotation_tree boundary;
            phase1_surface_guard_refined_annotation_tree guard;
            PTLiteral "=>";
            phase1_surface_continue_mutual_recursive_session_spine_tree continuation
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
        (phase1_surface_continue_mutual_recursive_session_spine_tree continuation) |- _ =>
        destruct
          (phase1_surface_normalize_recursive_one_step_session_spine_total_from_derivation
            continuation_path continuation_input continuation_rest
            continuation Hcontinuation)
          as [shell Hshell];
        pose proof
          (phase1_surface_normalize_recursive_one_step_session_spine_round_trip
            continuation shell Hshell) as Hshell_tree;
        rewrite <- Hshell_tree in Hcontinuation;
        destruct
          (phase1_surface_normalize_recursive_body_one_step_session_spine_fuels_total_from_derivation
            continuation_path continuation_input continuation_rest
            shell Hcontinuation)
          as [body_source_fuel [body_closure_fuel [body_step Hbody]]];
        pose proof
          (phase1_surface_normalize_recursive_body_one_step_session_spine_fuels_round_trip
            body_source_fuel body_closure_fuel shell body_step Hbody)
          as Hbody_tree;
        rewrite <- Hbody_tree in Hcontinuation;
        destruct
          (phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels_total_from_derivation
            continuation_path continuation_input continuation_rest
            body_step Hcontinuation)
          as [recursive_source_fuel
            [recursive_closure_fuel
              [recursive_transfer_fuel
                [converted [Hrecursive Hrecursive_tree]]]]];
        let source_fuel :=
          constr:(Nat.max body_source_fuel recursive_source_fuel) in
        let closure_fuel :=
          constr:(Nat.max body_closure_fuel recursive_closure_fuel) in
        pose proof
          (phase1_surface_normalize_recursive_body_one_step_session_spine_fuels_monotone
            body_source_fuel source_fuel
            body_closure_fuel closure_fuel
            shell body_step
            (Nat.le_max_l body_source_fuel recursive_source_fuel)
            (Nat.le_max_l body_closure_fuel recursive_closure_fuel)
            Hbody)
          as Hbody_lifted;
        pose proof
          (phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels_body_monotone
            recursive_source_fuel source_fuel
            recursive_closure_fuel closure_fuel
            recursive_transfer_fuel body_step converted
            (Nat.le_max_r body_source_fuel recursive_source_fuel)
            (Nat.le_max_r body_closure_fuel recursive_closure_fuel)
            Hrecursive)
          as Hrecursive_lifted;
        exists source_fuel, closure_fuel, recursive_transfer_fuel;
        exists
          {| phase1_recursive_body_choice_branch_label := label;
             phase1_recursive_body_choice_branch_params := params;
             phase1_recursive_body_choice_branch_boundary := boundary;
             phase1_recursive_body_choice_branch_guard := guard;
             phase1_recursive_body_choice_branch_continuation := converted |};
        unfold
          phase1_surface_normalize_recursive_body_choice_one_step_session_branch_spine_fuels;
        cbn;
        unfold
          phase1_surface_normalize_recursive_body_choice_one_step_continuation_fuels;
        rewrite Hshell, Hbody_lifted;
        exact Hrecursive_lifted
    end.
  }

  assert (Htail :
    forall tail_path tail_input tail_rest branches,
      DerivesRepetition phase1_surface_rules tail_path
        phase1_surface_session_branch_suffix_expression_for_totality
        tail_input tail_rest
        (phase1_surface_continue_mutual_recursive_session_branch_tail_spine_trees
          branches) ->
      exists source_fuel closure_fuel transfer_fuel refined_branches,
        phase1_surface_normalize_recursive_body_choice_one_step_session_branch_tail_spine_fuels
          source_fuel closure_fuel transfer_fuel branches = Some refined_branches).
  {
    intros tail_path tail_input tail_rest branches Htail_derive.
    revert tail_input tail_rest Htail_derive.
    induction branches as [|branch branches IHrest];
      intros tail_input tail_rest Htail_derive.
    - cbn in Htail_derive.
      inversion Htail_derive; subst.
      exists 0, 0, 0.
      exists Phase1RecursiveBodyChoiceOneStepBranchTailNil.
      reflexivity.
    - cbn in Htail_derive.
      inversion Htail_derive as
        [|path0 body0 input0 middle0 rest0 tree0 trees0
           Hbody Hprogress Hrest]; subst.
      unfold phase1_surface_session_branch_suffix_expression_for_totality
        in Hbody.
      destruct
        (derives_sequence_expression_exposes_items
          phase1_surface_rules
          (descend tail_path AtRepetitionBody)
          [ ELiteral "|";
            ENonterminal "session_branch"
          ]
          tail_input middle0
          (phase1_surface_session_branch_suffix_tree
            (phase1_surface_continue_mutual_recursive_session_branch_spine_tree
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
      | Hbranch_derive : Derives phase1_surface_rules ?branch_path
          (ENonterminal "session_branch") ?branch_input ?branch_rest
          (phase1_surface_continue_mutual_recursive_session_branch_spine_tree
            branch) |- _ =>
          destruct
            (Hbranch branch_path branch_input branch_rest branch Hbranch_derive)
            as [branch_source_fuel
              [branch_closure_fuel
                [branch_transfer_fuel
                  [refined_branch Hbranch_normalize]]]];
          destruct (IHrest _ _ Hrest)
            as [rest_source_fuel
              [rest_closure_fuel
                [rest_transfer_fuel
                  [refined_rest Hrest_normalize]]]];
          let source_fuel :=
            constr:(Nat.max branch_source_fuel rest_source_fuel) in
          let closure_fuel :=
            constr:(Nat.max branch_closure_fuel rest_closure_fuel) in
          let transfer_fuel :=
            constr:(Nat.max branch_transfer_fuel rest_transfer_fuel) in
          pose proof
            (phase1_surface_normalize_recursive_body_choice_one_step_session_branch_spine_fuels_monotone
              branch_source_fuel source_fuel
              branch_closure_fuel closure_fuel
              branch_transfer_fuel transfer_fuel
              branch refined_branch
              (Nat.le_max_l branch_source_fuel rest_source_fuel)
              (Nat.le_max_l branch_closure_fuel rest_closure_fuel)
              (Nat.le_max_l branch_transfer_fuel rest_transfer_fuel)
              Hbranch_normalize)
            as Hbranch_lifted;
          pose proof
            (phase1_surface_normalize_recursive_body_choice_one_step_session_branch_tail_spine_fuels_monotone
              rest_source_fuel source_fuel
              rest_closure_fuel closure_fuel
              rest_transfer_fuel transfer_fuel
              branches refined_rest
              (Nat.le_max_r branch_source_fuel rest_source_fuel)
              (Nat.le_max_r branch_closure_fuel rest_closure_fuel)
              (Nat.le_max_r branch_transfer_fuel rest_transfer_fuel)
              Hrest_normalize)
            as Hrest_lifted;
          exists source_fuel, closure_fuel, transfer_fuel;
          exists
            (Phase1RecursiveBodyChoiceOneStepBranchTailCons
              refined_branch refined_rest);
          cbn;
          rewrite Hbranch_lifted, Hrest_lifted;
          reflexivity
      end.
  }

  assert (Hchoice :
    forall expected_direction choice_path choice_input choice_rest choice,
      Derives phase1_surface_rules choice_path
        (phase1_surface_session_choice_expression_for_totality expected_direction)
        choice_input choice_rest
        (phase1_surface_continue_mutual_recursive_session_choice_spine_tree choice) ->
      exists source_fuel closure_fuel transfer_fuel refined_choice,
        phase1_surface_normalize_recursive_body_choice_one_step_session_choice_spine_fuels
          source_fuel closure_fuel transfer_fuel choice = Some refined_choice).
  {
    intros expected_direction choice_path choice_input choice_rest
      [direction first_branch rest_branches] Hchoice_derive.
    unfold phase1_surface_session_choice_expression_for_totality
      in Hchoice_derive.
    destruct
      (derives_sequence_expression_exposes_items
        phase1_surface_rules choice_path
        [ ELiteral (phase1_surface_session_choice_keyword expected_direction);
          ELiteral "{";
          ENonterminal "session_branch";
          ERepetition phase1_surface_session_branch_suffix_expression_for_totality;
          ELiteral "}"
        ]
        choice_input choice_rest
        (phase1_surface_continue_mutual_recursive_session_choice_spine_tree
          (Phase1ContinueMutualRecursiveChoice
            direction first_branch rest_branches))
        Hchoice_derive)
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
    | Hfirst : Derives phase1_surface_rules ?first_path
        (ENonterminal "session_branch") ?first_input ?first_rest
        (phase1_surface_continue_mutual_recursive_session_branch_spine_tree
          first_branch),
      Hrest : Derives phase1_surface_rules ?rest_path
        (ERepetition phase1_surface_session_branch_suffix_expression_for_totality)
        ?rest_input ?rest_rest
        (PTRepetition
          (phase1_surface_continue_mutual_recursive_session_branch_tail_spine_trees
            rest_branches)) |- _ =>
        destruct
          (Hbranch first_path first_input first_rest first_branch Hfirst)
          as [first_source_fuel
            [first_closure_fuel
              [first_transfer_fuel
                [refined_first Hfirst_normalize]]]];
        destruct
          (phase1_surface_repetition_derivation_exposes
            rest_path phase1_surface_session_branch_suffix_expression_for_totality
            rest_input rest_rest
            (PTRepetition
              (phase1_surface_continue_mutual_recursive_session_branch_tail_spine_trees
                rest_branches))
            Hrest)
          as [rest_trees [Hrest_tree Hrest_derive]];
        cbn in Hrest_tree;
        inversion Hrest_tree; subst rest_trees;
        destruct
          (Htail rest_path rest_input rest_rest rest_branches Hrest_derive)
          as [rest_source_fuel
            [rest_closure_fuel
              [rest_transfer_fuel
                [refined_rest Hrest_normalize]]]];
        let source_fuel :=
          constr:(Nat.max first_source_fuel rest_source_fuel) in
        let closure_fuel :=
          constr:(Nat.max first_closure_fuel rest_closure_fuel) in
        let transfer_fuel :=
          constr:(Nat.max first_transfer_fuel rest_transfer_fuel) in
        pose proof
          (phase1_surface_normalize_recursive_body_choice_one_step_session_branch_spine_fuels_monotone
            first_source_fuel source_fuel
            first_closure_fuel closure_fuel
            first_transfer_fuel transfer_fuel
            first_branch refined_first
            (Nat.le_max_l first_source_fuel rest_source_fuel)
            (Nat.le_max_l first_closure_fuel rest_closure_fuel)
            (Nat.le_max_l first_transfer_fuel rest_transfer_fuel)
            Hfirst_normalize)
          as Hfirst_lifted;
        pose proof
          (phase1_surface_normalize_recursive_body_choice_one_step_session_branch_tail_spine_fuels_monotone
            rest_source_fuel source_fuel
            rest_closure_fuel closure_fuel
            rest_transfer_fuel transfer_fuel
            rest_branches refined_rest
            (Nat.le_max_r first_source_fuel rest_source_fuel)
            (Nat.le_max_r first_closure_fuel rest_closure_fuel)
            (Nat.le_max_r first_transfer_fuel rest_transfer_fuel)
            Hrest_normalize)
          as Hrest_lifted;
        exists source_fuel, closure_fuel, transfer_fuel;
        exists
          {| phase1_recursive_body_choice_direction := direction;
             phase1_recursive_body_choice_first_branch := refined_first;
             phase1_recursive_body_choice_rest_branches := refined_rest |};
        cbn;
        rewrite Hfirst_lifted, Hrest_lifted;
        reflexivity
    end.
  }

  assert (Hsuccess :
    exists source_fuel closure_fuel transfer_fuel refined,
      phase1_surface_normalize_recursive_body_choice_one_step_session_spine_fuels
        source_fuel closure_fuel transfer_fuel session = Some refined).
  {
    destruct session as [nonreference | reference_tree].
    - destruct nonreference as
        [direction parameter boundary guard continuation
        |choice
        |choice
        |terminal
        |payload
        |payload].
      + exists 0, 0, 0.
        eexists.
        reflexivity.
      + destruct
          (phase1_surface_selected_choice_derivation
            Phase1SessionSelect path input rest
            (phase1_surface_continue_mutual_recursive_session_choice_spine_tree choice)
            Hderive)
          as [choice_path Hchoice_derive].
        destruct
          (Hchoice Phase1SessionSelect choice_path input rest choice Hchoice_derive)
          as [source_fuel
            [closure_fuel [transfer_fuel [refined_choice Hchoice_normalize]]]].
        exists source_fuel, closure_fuel, transfer_fuel.
        exists
          (Phase1RecursiveBodyChoiceOneStepNonreferenceSession
            (Phase1RecursiveBodyChoiceOneStepSelectSession refined_choice)).
        cbn.
        rewrite Hchoice_normalize.
        reflexivity.
      + destruct
          (phase1_surface_selected_choice_derivation
            Phase1SessionOffer path input rest
            (phase1_surface_continue_mutual_recursive_session_choice_spine_tree choice)
            Hderive)
          as [choice_path Hchoice_derive].
        destruct
          (Hchoice Phase1SessionOffer choice_path input rest choice Hchoice_derive)
          as [source_fuel
            [closure_fuel [transfer_fuel [refined_choice Hchoice_normalize]]]].
        exists source_fuel, closure_fuel, transfer_fuel.
        exists
          (Phase1RecursiveBodyChoiceOneStepNonreferenceSession
            (Phase1RecursiveBodyChoiceOneStepOfferSession refined_choice)).
        cbn.
        rewrite Hchoice_normalize.
        reflexivity.
      + exists 0, 0, 0.
        eexists.
        reflexivity.
      + exists 0, 0, 0.
        eexists.
        reflexivity.
      + exists 0, 0, 0.
        eexists.
        reflexivity.
    - exists 0, 0, 0.
      eexists.
      reflexivity.
  }
  destruct Hsuccess as
    [source_fuel [closure_fuel [transfer_fuel [refined Hnormalize]]]].
  exists source_fuel, closure_fuel, transfer_fuel, refined.
  split.
  - exact Hnormalize.
  - eapply
      phase1_surface_normalize_recursive_body_choice_one_step_session_spine_fuels_round_trip.
    exact Hnormalize.
Qed.
