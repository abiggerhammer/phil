From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionContinueChoiceOneStepCarrierSpine
  GrammarAstSessionContinueTransferRecursiveCarrierTotality
  GrammarAstSessionMutualRecursiveClosureTotality
  GrammarAstSessionBranchTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the one-step choice composition from #1097. *)

Theorem
  phase1_surface_normalize_continue_choice_one_step_session_spine_total_from_derivation :
  forall path input rest session,
    Derives phase1_surface_rules path
      (ENonterminal "session_expression") input rest
      (phase1_surface_continue_transfer_recursive_session_spine_tree session) ->
    exists refined,
      phase1_surface_normalize_continue_choice_one_step_session_spine session =
        Some refined.
Proof.
  intros path input rest session Hderive.

  assert (Hbranch :
    forall branch_path branch_input branch_rest branch,
      Derives phase1_surface_rules branch_path
        (ENonterminal "session_branch") branch_input branch_rest
        (phase1_surface_end_refined_recursive_session_branch_spine_tree branch) ->
      exists refined_branch,
        phase1_surface_normalize_continue_choice_one_step_session_branch_spine
          branch = Some refined_branch).
  {
    intros branch_path branch_input branch_rest
      [label params boundary guard continuation] Hbranch_derive.
    destruct
      (derives_nonterminal_exposes_body
        phase1_surface_rules branch_path "session_branch"
        branch_input branch_rest
        (phase1_surface_end_refined_recursive_session_branch_spine_tree
          (Phase1EndRefinedRecursiveBranch
            label params boundary guard continuation))
        Hbranch_derive)
      as [body [subtree [Hlookup [Hnode Hbody]]]].
    rewrite phase1_surface_session_branch_lookup_for_totality in Hlookup.
    inversion Hlookup; subst body.
    unfold phase1_surface_session_branch_expression_for_totality in Hbody.
    cbn [phase1_surface_end_refined_recursive_session_branch_spine_tree]
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
            phase1_surface_end_refined_recursive_session_spine_tree continuation
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
        (phase1_surface_end_refined_recursive_session_spine_tree continuation) |- _ =>
        destruct
          (phase1_surface_normalize_continue_transfer_recursive_session_spine_total_from_derivation
            continuation_path continuation_input continuation_rest
            continuation Hcontinuation)
          as [refined_continuation Hcontinuation_normalize];
        exists
          (Phase1ContinueChoiceOneStepBranch
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
        (phase1_surface_end_refined_recursive_session_branch_tail_spine_trees
          branches) ->
      exists refined_branches,
        phase1_surface_normalize_continue_choice_one_step_session_branch_tail_spine
          branches = Some refined_branches).
  {
    intros tail_path tail_input tail_rest branches Htail_derive.
    revert tail_input tail_rest Htail_derive.
    induction branches as [|branch branches IHrest];
      intros tail_input tail_rest Htail_derive.
    - cbn in Htail_derive.
      inversion Htail_derive; subst.
      exists Phase1ContinueChoiceOneStepBranchTailNil.
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
            (phase1_surface_end_refined_recursive_session_branch_spine_tree
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
          (phase1_surface_end_refined_recursive_session_branch_spine_tree
            branch) |- _ =>
          destruct
            (Hbranch branch_path branch_input branch_rest branch Hbranch_derive)
            as [refined_branch Hbranch_normalize];
          destruct (IHrest _ _ Hrest)
            as [refined_rest Hrest_normalize];
          exists
            (Phase1ContinueChoiceOneStepBranchTailCons
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
        (phase1_surface_end_refined_recursive_session_choice_spine_tree choice) ->
      exists refined_choice,
        phase1_surface_normalize_continue_choice_one_step_session_choice_spine
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
        (phase1_surface_end_refined_recursive_session_choice_spine_tree
          (Phase1EndRefinedRecursiveChoice
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
        (phase1_surface_end_refined_recursive_session_branch_spine_tree
          first_branch),
      Hrest : Derives phase1_surface_rules ?rest_path
        (ERepetition phase1_surface_session_branch_suffix_expression_for_totality)
        ?rest_input ?rest_rest
        (PTRepetition
          (phase1_surface_end_refined_recursive_session_branch_tail_spine_trees
            rest_branches)) |- _ =>
        destruct
          (Hbranch first_path first_input first_rest first_branch Hfirst)
          as [refined_first Hfirst_normalize];
        destruct
          (phase1_surface_repetition_derivation_exposes
            rest_path phase1_surface_session_branch_suffix_expression_for_totality
            rest_input rest_rest
            (PTRepetition
              (phase1_surface_end_refined_recursive_session_branch_tail_spine_trees
                rest_branches))
            Hrest)
          as [rest_trees [Hrest_tree Hrest_derive]];
        cbn in Hrest_tree;
        inversion Hrest_tree; subst rest_trees;
        destruct
          (Htail rest_path rest_input rest_rest rest_branches Hrest_derive)
          as [refined_rest Hrest_normalize];
        exists
          (Phase1ContinueChoiceOneStepChoice
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
      |terminal
      |selected_tree
      |payload].
    + exists
        (Phase1ContinueChoiceOneStepNonreferenceSession
          (Phase1ContinueChoiceOneStepTransferSession
            direction parameter boundary guard continuation)).
      reflexivity.
    + destruct
        (phase1_surface_selected_choice_derivation
          Phase1SessionSelect path input rest
          (phase1_surface_end_refined_recursive_session_choice_spine_tree choice)
          Hderive)
        as [choice_path Hchoice_derive].
      destruct
        (Hchoice Phase1SessionSelect choice_path input rest choice Hchoice_derive)
        as [refined_choice Hchoice_normalize].
      exists
        (Phase1ContinueChoiceOneStepNonreferenceSession
          (Phase1ContinueChoiceOneStepSelectSession refined_choice)).
      cbn.
      rewrite Hchoice_normalize.
      reflexivity.
    + destruct
        (phase1_surface_selected_choice_derivation
          Phase1SessionOffer path input rest
          (phase1_surface_end_refined_recursive_session_choice_spine_tree choice)
          Hderive)
        as [choice_path Hchoice_derive].
      destruct
        (Hchoice Phase1SessionOffer choice_path input rest choice Hchoice_derive)
        as [refined_choice Hchoice_normalize].
      exists
        (Phase1ContinueChoiceOneStepNonreferenceSession
          (Phase1ContinueChoiceOneStepOfferSession refined_choice)).
      cbn.
      rewrite Hchoice_normalize.
      reflexivity.
    + exists
        (Phase1ContinueChoiceOneStepNonreferenceSession
          (Phase1ContinueChoiceOneStepEndSession terminal)).
      reflexivity.
    + exists
        (Phase1ContinueChoiceOneStepNonreferenceSession
          (Phase1ContinueChoiceOneStepRecursiveSession selected_tree)).
      reflexivity.
    + exists
        (Phase1ContinueChoiceOneStepNonreferenceSession
          (Phase1ContinueChoiceOneStepContinueSession payload)).
      reflexivity.
  - exists (Phase1ContinueChoiceOneStepStaticReferenceSession reference_tree).
    reflexivity.
Qed.
