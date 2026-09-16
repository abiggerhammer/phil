From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionEndRecursiveCarrierSpine
  GrammarAstSessionEndCarrierTotality
  GrammarAstSessionMutualRecursiveClosureTotality
  GrammarAstSessionTransferRecursiveClosureTotality
  GrammarAstSessionBranchTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Converse for the structural end-outcome lift from #1075.

  The end-refinement normalizer is structurally recursive and needs no fuel.
  Totality is nevertheless derivation-relative: an arbitrary mutual-recursive
  carrier may contain an arbitrary raw subtree in its End constructor.  A
  certified session derivation supplies the exact `end identifier` derivation
  at every such node.
*)

Lemma phase1_surface_selected_end_derivation :
  forall path input rest selected_tree,
    Derives phase1_surface_rules path
      (ENonterminal "session_expression")
      input rest
      (PTNonterminal "session_expression"
        (PTAlternative 0
          (PTNonterminal "nonreference_session_expression"
            (PTAlternative 4 selected_tree)))) ->
    exists end_path,
      Derives phase1_surface_rules end_path
        phase1_surface_end_session_expression_for_totality
        input rest selected_tree.
Proof.
  intros path input rest selected_tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "session_expression"
      input rest
      (PTNonterminal "session_expression"
        (PTAlternative 0
          (PTNonterminal "nonreference_session_expression"
            (PTAlternative 4 selected_tree))))
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
          (PTAlternative 4 selected_tree)))
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
        (PTAlternative 4 selected_tree))
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
      phase1_surface_rules _
      phase1_surface_nonreference_session_items_for_totality
      input rest (PTAlternative 4 selected_tree)
      Hnonreference_body)
    as [end_index [end_item [selected_end
      [Hend_nth [Hend_tree Hend]]]]].
  cbn in Hend_tree.
  inversion Hend_tree; subst end_index selected_end.
  cbn in Hend_nth.
  inversion Hend_nth; subst end_item.
  eexists.
  exact Hend.
Qed.

Theorem
  phase1_surface_normalize_end_refined_recursive_session_spine_total_from_derivation :
  forall path input rest session,
    Derives phase1_surface_rules path
      (ENonterminal "session_expression") input rest
      (phase1_surface_mutual_recursive_session_spine_tree session) ->
    exists refined,
      phase1_surface_normalize_end_refined_recursive_session_spine session =
        Some refined.
Proof.
  fix IH_session 4.
  intros path input rest session Hderive.

  assert (Hbranch :
    forall branch_path branch_input branch_rest branch,
      Derives phase1_surface_rules branch_path
        (ENonterminal "session_branch") branch_input branch_rest
        (phase1_surface_mutual_recursive_session_branch_spine_tree branch) ->
      exists refined_branch,
        phase1_surface_normalize_end_refined_recursive_session_branch_spine
          branch = Some refined_branch).
  {
    intros branch_path branch_input branch_rest
      [label params boundary guard continuation] Hbranch_derive.
    destruct
      (derives_nonterminal_exposes_body
        phase1_surface_rules branch_path "session_branch"
        branch_input branch_rest
        (phase1_surface_mutual_recursive_session_branch_spine_tree
          (Phase1MutualRecursiveBranch
            label params boundary guard continuation))
        Hbranch_derive)
      as [body [subtree [Hlookup [Hnode Hbody]]]].
    rewrite phase1_surface_session_branch_lookup_for_totality in Hlookup.
    inversion Hlookup; subst body.
    unfold phase1_surface_session_branch_expression_for_totality in Hbody.
    cbn [phase1_surface_mutual_recursive_session_branch_spine_tree] in Hnode.
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
            phase1_surface_mutual_recursive_session_spine_tree continuation
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
        (phase1_surface_mutual_recursive_session_spine_tree continuation) |- _ =>
        destruct
          (IH_session continuation_path continuation_input continuation_rest
            continuation Hcontinuation)
          as [refined_continuation Hcontinuation_normalize];
        exists
          (Phase1EndRefinedRecursiveBranch
            label params boundary guard refined_continuation);
        cbn;
        rewrite Hcontinuation_normalize;
        reflexivity
    end.
  }

  assert (Htail :
    forall tail_path tail_input tail_rest branches,
      DerivesRepetition phase1_surface_rules tail_path
        phase1_surface_session_branch_suffix_expression_for_totality
        tail_input tail_rest
        (phase1_surface_mutual_recursive_session_branch_tail_spine_trees
          branches) ->
      exists refined_branches,
        phase1_surface_normalize_end_refined_recursive_session_branch_tail_spine
          branches = Some refined_branches).
  {
    intros tail_path tail_input tail_rest branches Htail_derive.
    revert tail_input tail_rest Htail_derive.
    induction branches as [|branch branches IHrest];
      intros tail_input tail_rest Htail_derive.
    - cbn in Htail_derive.
      inversion Htail_derive; subst.
      exists Phase1EndRefinedRecursiveBranchTailNil.
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
            (phase1_surface_mutual_recursive_session_branch_spine_tree branch))
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
          (phase1_surface_mutual_recursive_session_branch_spine_tree branch) |- _ =>
          destruct
            (Hbranch branch_path branch_input branch_rest branch Hbranch_derive)
            as [refined_branch Hbranch_normalize];
          destruct (IHrest _ _ Hrest)
            as [refined_rest Hrest_normalize];
          exists
            (Phase1EndRefinedRecursiveBranchTailCons
              refined_branch refined_rest);
          cbn;
          rewrite Hbranch_normalize, Hrest_normalize;
          reflexivity
      end.
  }

  assert (Hchoice :
    forall expected_direction choice_path choice_input choice_rest choice,
      Derives phase1_surface_rules choice_path
        (phase1_surface_session_choice_expression_for_totality expected_direction)
        choice_input choice_rest
        (phase1_surface_mutual_recursive_session_choice_spine_tree choice) ->
      exists refined_choice,
        phase1_surface_normalize_end_refined_recursive_session_choice_spine
          choice = Some refined_choice).
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
        (phase1_surface_mutual_recursive_session_choice_spine_tree
          (Phase1MutualRecursiveChoice direction first_branch rest_branches))
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
        (phase1_surface_mutual_recursive_session_branch_spine_tree first_branch),
      Hrest : Derives phase1_surface_rules ?rest_path
        (ERepetition phase1_surface_session_branch_suffix_expression_for_totality)
        ?rest_input ?rest_rest
        (PTRepetition
          (phase1_surface_mutual_recursive_session_branch_tail_spine_trees
            rest_branches)) |- _ =>
        destruct
          (Hbranch first_path first_input first_rest first_branch Hfirst)
          as [refined_first Hfirst_normalize];
        destruct
          (phase1_surface_repetition_derivation_exposes
            rest_path phase1_surface_session_branch_suffix_expression_for_totality
            rest_input rest_rest
            (PTRepetition
              (phase1_surface_mutual_recursive_session_branch_tail_spine_trees
                rest_branches))
            Hrest)
          as [rest_trees [Hrest_tree Hrest_derive]];
        cbn in Hrest_tree;
        inversion Hrest_tree; subst rest_trees;
        destruct
          (Htail rest_path rest_input rest_rest rest_branches Hrest_derive)
          as [refined_rest Hrest_normalize];
        exists
          (Phase1EndRefinedRecursiveChoice
            direction refined_first refined_rest);
        cbn;
        rewrite Hfirst_normalize, Hrest_normalize;
        reflexivity
    end.
  }

  destruct session as [nonreference | reference_tree].
  - destruct nonreference as
      [direction parameter boundary guard continuation
      |choice
      |choice
      |selected_tree
      |selected_tree
      |selected_tree].
    + let transfer := constr:(
        {| phase1_guard_refined_transfer_direction := direction;
           phase1_guard_refined_transfer_parameter := parameter;
           phase1_guard_refined_transfer_boundary := boundary;
           phase1_guard_refined_transfer_guard := guard;
           phase1_guard_refined_transfer_continuation_tree :=
             phase1_surface_mutual_recursive_session_spine_tree continuation |}) in
      assert (Htransfer_tree :
        phase1_surface_guard_refined_boundary_typed_transfer_session_spine_tree
          (Phase1GuardRefinedBoundaryTypedTransferNonreferenceSession
            (Phase1GuardRefinedBoundaryTypedTransferSession transfer)) =
        phase1_surface_mutual_recursive_session_spine_tree
          (Phase1MutualRecursiveNonreferenceSession
            (Phase1MutualRecursiveTransferSession
              direction parameter boundary guard continuation)))
        by reflexivity;
      destruct
        (phase1_surface_guard_refined_transfer_continuation_derivation_shorter
          path input rest
          (phase1_surface_mutual_recursive_session_spine_tree
            (Phase1MutualRecursiveNonreferenceSession
              (Phase1MutualRecursiveTransferSession
                direction parameter boundary guard continuation)))
          transfer Hderive Htransfer_tree)
        as [continuation_path
          [continuation_input [continuation_rest [Hcontinuation Hshort]]]];
      destruct
        (IH_session continuation_path continuation_input continuation_rest
          continuation Hcontinuation)
        as [refined_continuation Hcontinuation_normalize];
      exists
        (Phase1EndRefinedRecursiveNonreferenceSession
          (Phase1EndRefinedRecursiveTransferSession
            direction parameter boundary guard refined_continuation));
      cbn;
      rewrite Hcontinuation_normalize;
      reflexivity.
    + destruct
        (phase1_surface_selected_choice_derivation
          Phase1SessionSelect path input rest
          (phase1_surface_mutual_recursive_session_choice_spine_tree choice)
          Hderive)
        as [choice_path Hchoice_derive];
      destruct
        (Hchoice Phase1SessionSelect choice_path input rest choice Hchoice_derive)
        as [refined_choice Hchoice_normalize];
      exists
        (Phase1EndRefinedRecursiveNonreferenceSession
          (Phase1EndRefinedRecursiveSelectSession refined_choice));
      cbn;
      rewrite Hchoice_normalize;
      reflexivity.
    + destruct
        (phase1_surface_selected_choice_derivation
          Phase1SessionOffer path input rest
          (phase1_surface_mutual_recursive_session_choice_spine_tree choice)
          Hderive)
        as [choice_path Hchoice_derive];
      destruct
        (Hchoice Phase1SessionOffer choice_path input rest choice Hchoice_derive)
        as [refined_choice Hchoice_normalize];
      exists
        (Phase1EndRefinedRecursiveNonreferenceSession
          (Phase1EndRefinedRecursiveOfferSession refined_choice));
      cbn;
      rewrite Hchoice_normalize;
      reflexivity.
    + destruct
        (phase1_surface_selected_end_derivation
          path input rest selected_tree Hderive)
        as [end_path Hend];
      destruct
        (phase1_surface_normalize_end_session_spine_total_from_derivation
          end_path input rest selected_tree Hend)
        as [terminal [Hterminal Hterminal_tree]];
      exists
        (Phase1EndRefinedRecursiveNonreferenceSession
          (Phase1EndRefinedRecursiveEndSession terminal));
      cbn;
      rewrite Hterminal;
      reflexivity.
    + exists
        (Phase1EndRefinedRecursiveNonreferenceSession
          (Phase1EndRefinedRecursiveRecursiveSession selected_tree)).
      reflexivity.
    + exists
        (Phase1EndRefinedRecursiveNonreferenceSession
          (Phase1EndRefinedRecursiveContinueSession selected_tree)).
      reflexivity.
  - exists (Phase1EndRefinedRecursiveStaticReferenceSession reference_tree).
    reflexivity.
Qed.

Definition phase1_surface_normalize_end_refined_recursive_session_tree_fuel
  (fuel : nat)
  (tree : ParseTree)
  : option Phase1SurfaceEndRefinedRecursiveSessionSpine :=
  match phase1_surface_normalize_mutual_recursive_session_tree_fuel fuel tree with
  | Some session =>
      phase1_surface_normalize_end_refined_recursive_session_spine session
  | None => None
  end.

Theorem
  phase1_surface_normalize_end_refined_recursive_session_tree_fuel_round_trip :
  forall fuel tree refined,
    phase1_surface_normalize_end_refined_recursive_session_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_end_refined_recursive_session_spine_tree refined = tree.
Proof.
  intros fuel tree refined Hnormalize.
  unfold phase1_surface_normalize_end_refined_recursive_session_tree_fuel
    in Hnormalize.
  destruct
    (phase1_surface_normalize_mutual_recursive_session_tree_fuel fuel tree)
    as [session |] eqn:Hsession; try discriminate Hnormalize.
  transitivity (phase1_surface_mutual_recursive_session_spine_tree session).
  - eapply phase1_surface_normalize_end_refined_recursive_session_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_mutual_recursive_session_tree_fuel_round_trip.
    exact Hsession.
Qed.

Theorem
  phase1_surface_normalize_end_refined_recursive_session_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "session_expression") input rest tree ->
    exists fuel refined,
      phase1_surface_normalize_end_refined_recursive_session_tree_fuel
        fuel tree = Some refined /\
      phase1_surface_end_refined_recursive_session_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_mutual_recursive_session_tree_total_from_derivation
      path input rest tree Hderive)
    as [fuel [session [Hsession Hsession_tree]]].
  rewrite <- Hsession_tree in Hderive.
  destruct
    (phase1_surface_normalize_end_refined_recursive_session_spine_total_from_derivation
      path input rest session Hderive)
    as [refined Hrefined].
  exists fuel, refined.
  assert (Hresult :
    phase1_surface_normalize_end_refined_recursive_session_tree_fuel
      fuel tree = Some refined).
  {
    unfold phase1_surface_normalize_end_refined_recursive_session_tree_fuel.
    rewrite Hsession.
    exact Hrefined.
  }
  split.
  - exact Hresult.
  - eapply
      phase1_surface_normalize_end_refined_recursive_session_tree_fuel_round_trip.
    exact Hresult.
Qed.
