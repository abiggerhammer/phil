From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstNamedPostfixExpressionSpine
  GrammarAstSourceHeaderTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Converse for the named-postfix-expression shell refinement introduced by
  #1380.

  The carrier refines the leading qualified_name and records whether the
  optional named-postfix tail is present while retaining any present tail body
  as its exact certified ParseTree.  This file proves that normalization is
  total for every derivable named_postfix_expression tree.
*)

Definition phase1_surface_named_postfix_projection_expression_for_totality
  : EbnfExpression :=
  ESequence [ELiteral "."; ENonterminal "identifier"].

Definition phase1_surface_named_postfix_tail_body_expression_for_totality
  : EbnfExpression :=
  EAlternative
    [ ESequence
        [ ENonterminal "static_arguments";
          EOptional (ENonterminal "term_arguments");
          ERepetition
            phase1_surface_named_postfix_projection_expression_for_totality
        ];
      ESequence
        [ ENonterminal "term_arguments";
          ERepetition
            phase1_surface_named_postfix_projection_expression_for_totality
        ]
    ].

Definition phase1_surface_named_postfix_tail_expression_for_totality
  : EbnfExpression :=
  EOptional phase1_surface_named_postfix_tail_body_expression_for_totality.

Definition phase1_surface_named_postfix_expression_for_totality
  : EbnfExpression :=
  ESequence
    [ ENonterminal "qualified_name";
      phase1_surface_named_postfix_tail_expression_for_totality
    ].

Lemma phase1_surface_named_postfix_expression_lookup_for_totality :
  lookupRule "named_postfix_expression" phase1_surface_rules =
    Some phase1_surface_named_postfix_expression_for_totality.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_expect_named_postfix_tail_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_named_postfix_tail_expression_for_totality
      input rest tree ->
    exists tail,
      phase1_surface_expect_optional tree = Some tail.
Proof.
  intros path input rest tree Hderive.
  unfold phase1_surface_named_postfix_tail_expression_for_totality in Hderive.
  destruct
    (optional_derivation_exposes_presence
      phase1_surface_rules path
      phase1_surface_named_postfix_tail_body_expression_for_totality
      input rest tree Hderive)
    as [[_ Hnone] | [body_tree [Hsome Hbody]]].
  - exists None.
    rewrite Hnone.
    reflexivity.
  - exists (Some body_tree).
    rewrite Hsome.
    reflexivity.
Qed.

Theorem phase1_surface_normalize_named_postfix_expression_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "named_postfix_expression") input rest tree ->
    exists expression,
      phase1_surface_normalize_named_postfix_expression_spine tree =
        Some expression /\
      phase1_surface_named_postfix_expression_spine_tree expression = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "named_postfix_expression"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_named_postfix_expression_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  unfold phase1_surface_named_postfix_expression_for_totality in Hbody.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "named_postfix_expression"))
      [ ENonterminal "qualified_name";
        phase1_surface_named_postfix_tail_expression_for_totality
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
  | Hname : Derives phase1_surface_rules _
      (ENonterminal "qualified_name") _ _ ?name_tree,
    Htail : Derives phase1_surface_rules _
      phase1_surface_named_postfix_tail_expression_for_totality
      _ _ ?tail_tree |- _ =>
      destruct
        (phase1_surface_normalize_qualified_name_total_from_derivation
          _ _ _ name_tree Hname)
        as [name Hname_normalize];
      destruct
        (phase1_surface_expect_named_postfix_tail_total_from_derivation
          _ _ _ tail_tree Htail)
        as [tail Htail_expect];
      let expression := constr:(
        {| phase1_named_postfix_expression_spine_name := name;
           phase1_named_postfix_expression_spine_tail := tail |}) in
      assert (Hnormalize :
        phase1_surface_normalize_named_postfix_expression_spine tree =
          Some expression);
      [ rewrite Htree, Hsubtree;
        unfold phase1_surface_normalize_named_postfix_expression_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_sequence,
          phase1_surface_exact2;
        cbn;
        rewrite String.eqb_refl;
        rewrite Hname_normalize;
        rewrite Htail_expect;
        reflexivity
      | exists expression;
        split;
        [ exact Hnormalize
        | eapply
            phase1_surface_normalize_named_postfix_expression_spine_round_trip;
          exact Hnormalize ] ]
  end.
Qed.
