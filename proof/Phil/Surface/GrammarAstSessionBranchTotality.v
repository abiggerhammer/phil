From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionBranchSpine
  GrammarAstGenericRequirementsTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the fixed six-field session_branch shell introduced by #1037. *)

Definition phase1_surface_session_branch_params_expression_for_totality
  : EbnfExpression :=
  EOptional
    (ESequence
      [ ELiteral "(";
        EOptional
          (ESequence
            [ ENonterminal "term_param";
              ERepetition
                (ESequence
                  [ ELiteral ",";
                    ENonterminal "term_param"
                  ])
            ]);
        ELiteral ")"
      ]).

Definition phase1_surface_session_branch_boundary_expression_for_totality
  : EbnfExpression :=
  EOptional
    (ESequence
      [ ELiteral "using";
        ENonterminal "static_reference"
      ]).

Definition phase1_surface_session_branch_guard_expression_for_totality
  : EbnfExpression :=
  EOptional
    (ESequence
      [ ELiteral "when";
        ENonterminal "proposition"
      ]).

Definition phase1_surface_session_branch_expression_for_totality
  : EbnfExpression :=
  ESequence
    [ ENonterminal "identifier";
      phase1_surface_session_branch_params_expression_for_totality;
      phase1_surface_session_branch_boundary_expression_for_totality;
      phase1_surface_session_branch_guard_expression_for_totality;
      ELiteral "=>";
      ENonterminal "session_expression"
    ].

Lemma phase1_surface_session_branch_lookup_for_totality :
  lookupRule "session_branch" phase1_surface_rules =
    Some phase1_surface_session_branch_expression_for_totality.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_expect_optional_total_from_derivation :
  forall path body input rest tree,
    Derives phase1_surface_rules path (EOptional body) input rest tree ->
    exists value,
      phase1_surface_expect_optional tree = Some value.
Proof.
  intros path body input rest tree Hderive.
  destruct
    (optional_derivation_exposes_presence
      phase1_surface_rules path body input rest tree Hderive)
    as [[_ Hnone] | [body_tree [Hsome Hbody]]].
  - exists None.
    rewrite Hnone.
    reflexivity.
  - exists (Some body_tree).
    rewrite Hsome.
    reflexivity.
Qed.

Theorem phase1_surface_normalize_session_branch_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "session_branch") input rest tree ->
    exists branch,
      phase1_surface_normalize_session_branch_spine tree = Some branch /\
      phase1_surface_session_branch_spine_tree branch = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "session_branch"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_session_branch_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  unfold phase1_surface_session_branch_expression_for_totality in Hbody.
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
      input rest subtree Hbody)
    as [trees [Hsubtree Hitems]].
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
      (ENonterminal "identifier") _ _ ?label_tree,
    Hparams : Derives phase1_surface_rules _
      phase1_surface_session_branch_params_expression_for_totality
      _ _ ?params_tree,
    Hboundary : Derives phase1_surface_rules _
      phase1_surface_session_branch_boundary_expression_for_totality
      _ _ ?boundary_tree,
    Hguard : Derives phase1_surface_rules _
      phase1_surface_session_branch_guard_expression_for_totality
      _ _ ?guard_tree,
    Harrow : Derives phase1_surface_rules _
      (ELiteral "=>") _ _ ?arrow_tree,
    Hcontinuation : Derives phase1_surface_rules _
      (ENonterminal "session_expression") _ _ ?continuation_tree |- _ =>
      pose proof
        (phase1_surface_validate_named_node_total_from_derivation
          "identifier" _ _ _ label_tree Hlabel) as Hlabel_validate;
      unfold phase1_surface_session_branch_params_expression_for_totality
        in Hparams;
      destruct
        (phase1_surface_expect_optional_total_from_derivation
          _ _ _ _ params_tree Hparams)
        as [params Hparams_expect];
      unfold phase1_surface_session_branch_boundary_expression_for_totality
        in Hboundary;
      destruct
        (phase1_surface_expect_optional_total_from_derivation
          _ _ _ _ boundary_tree Hboundary)
        as [boundary Hboundary_expect];
      unfold phase1_surface_session_branch_guard_expression_for_totality
        in Hguard;
      destruct
        (phase1_surface_expect_optional_total_from_derivation
          _ _ _ _ guard_tree Hguard)
        as [guard Hguard_expect];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "=>" _ _ arrow_tree Harrow)
        as [arrow_tail [_ [_ Harrow_tree]]];
      pose proof
        (phase1_surface_validate_named_node_total_from_derivation
          "session_expression" _ _ _ continuation_tree Hcontinuation)
        as Hcontinuation_validate;
      let branch := constr:(
        {| phase1_session_branch_label_tree := label_tree;
           phase1_session_branch_params_tree := params_tree;
           phase1_session_branch_boundary_tree := boundary_tree;
           phase1_session_branch_guard_tree := guard_tree;
           phase1_session_branch_continuation_tree := continuation_tree |}) in
      assert (Hnormalize :
        phase1_surface_normalize_session_branch_spine tree = Some branch);
      [ rewrite Htree, Hsubtree, Harrow_tree;
        unfold phase1_surface_normalize_session_branch_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_sequence,
          phase1_surface_exact6,
          phase1_surface_expect_literal;
        cbn;
        repeat rewrite String.eqb_refl;
        rewrite Hlabel_validate;
        rewrite Hparams_expect;
        rewrite Hboundary_expect;
        rewrite Hguard_expect;
        rewrite Hcontinuation_validate;
        reflexivity
      | exists branch;
        split;
        [ exact Hnormalize
        | eapply phase1_surface_normalize_session_branch_spine_round_trip;
          exact Hnormalize ] ]
  end.
Qed.
