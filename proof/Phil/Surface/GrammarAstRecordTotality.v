From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstRecordSpine
  GrammarAstTopLevelTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Converse for the proof-side record spine introduced by #934.

  GrammarAstRecordSpine proves that successful normalization of the outer
  record_decl shape is lossless.  This file proves that normalization cannot
  fail on an ordinary certified Grammar-v1 derivation of record_decl.  Shared
  generic/mode/requirement/field payloads remain opaque ParseTree values here.
*)

Lemma phase1_surface_record_decl_lookup_for_totality :
  exists generic_expr mode_expr requirements_expr fields_expr,
    lookupRule "record_decl" phase1_surface_rules =
      Some
        (ESequence
          [ ELiteral "record";
            ENonterminal "identifier";
            generic_expr;
            mode_expr;
            requirements_expr;
            ELiteral "{";
            fields_expr;
            ELiteral "}"
          ]).
Proof.
  vm_compute.
  do 4 eexists.
  reflexivity.
Qed.

Theorem phase1_surface_normalize_record_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "record_decl")
      input rest tree ->
    exists record,
      phase1_surface_normalize_record_spine tree = Some record /\
      phase1_surface_record_spine_tree record = tree.
Proof.
  intros path input rest tree Hderive.
  destruct phase1_surface_record_decl_lookup_for_totality
    as [generic_expr [mode_expr [requirements_expr [fields_expr Hlookup_exact]]]].
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "record_decl"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite Hlookup_exact in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "record_decl"))
      [ ELiteral "record";
        ENonterminal "identifier";
        generic_expr;
        mode_expr;
        requirements_expr;
        ELiteral "{";
        fields_expr;
        ELiteral "}"
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
  | Hkeyword : Derives phase1_surface_rules _
      (ELiteral "record") _ _ ?keyword_tree,
    Hname : Derives phase1_surface_rules _
      (ENonterminal "identifier") _ _ ?name_tree,
    Hgeneric : Derives phase1_surface_rules _
      generic_expr _ _ ?generic_tree,
    Hmode : Derives phase1_surface_rules _
      mode_expr _ _ ?mode_tree,
    Hrequirements : Derives phase1_surface_rules _
      requirements_expr _ _ ?requirements_tree,
    Hopen : Derives phase1_surface_rules _
      (ELiteral "{") _ _ ?open_tree,
    Hfields : Derives phase1_surface_rules _
      fields_expr _ _ ?fields_tree,
    Hclose : Derives phase1_surface_rules _
      (ELiteral "}") _ _ ?close_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "record" _ _ keyword_tree Hkeyword)
        as [keyword_tail [_ [_ Hkeyword_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "{" _ _ open_tree Hopen)
        as [open_tail [_ [_ Hopen_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "}" _ _ close_tree Hclose)
        as [close_tail [_ [_ Hclose_tree]]];
      destruct
        (phase1_surface_normalize_identifier_total_from_derivation
          _ _ _ name_tree Hname)
        as [name Hname_normalize];
      exists
        {| phase1_record_spine_name := name;
           phase1_record_spine_generic_params_tree := generic_tree;
           phase1_record_spine_mode_tree := mode_tree;
           phase1_record_spine_requirements_tree := requirements_tree;
           phase1_record_spine_fields_tree := fields_tree |};
      split;
      [ rewrite Htree, Hsubtree, Hkeyword_tree, Hopen_tree, Hclose_tree;
        unfold phase1_surface_normalize_record_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_sequence,
          phase1_surface_exact8,
          phase1_surface_expect_literal;
        cbn;
        rewrite Hname_normalize;
        reflexivity
      | eapply phase1_surface_normalize_record_spine_round_trip;
        rewrite Htree, Hsubtree, Hkeyword_tree, Hopen_tree, Hclose_tree;
        unfold phase1_surface_normalize_record_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_sequence,
          phase1_surface_exact8,
          phase1_surface_expect_literal;
        cbn;
        rewrite Hname_normalize;
        reflexivity ]
  end.
Qed.
