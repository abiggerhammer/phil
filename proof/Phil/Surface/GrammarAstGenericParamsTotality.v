From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstGenericParamsSpine
  GrammarAstRecordTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the shared generic-parameter correspondence introduced by #938. *)

Definition phase1_surface_generic_kind_items_for_totality
  : list EbnfExpression :=
  [ ELiteral "Type";
    ELiteral "Nat";
    ELiteral "Session";
    ELiteral "Message";
    ELiteral "Effects";
    ESequence [ELiteral "provider"; ENonterminal "type_expression"];
    ESequence [ELiteral "callable"; ENonterminal "type_expression"];
    ESequence [ELiteral "boundary"; ENonterminal "type_expression"];
    ESequence [ELiteral "architecture"; ENonterminal "type_expression"]
  ].

Lemma phase1_surface_generic_kind_lookup_for_totality :
  lookupRule "generic_kind" phase1_surface_rules =
    Some (EAlternative phase1_surface_generic_kind_items_for_totality).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_generic_param_lookup_for_totality :
  lookupRule "generic_param" phase1_surface_rules =
    Some
      (ESequence
        [ ENonterminal "identifier";
          ELiteral ":";
          ENonterminal "generic_kind"
        ]).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_generic_params_lookup_for_totality :
  lookupRule "generic_params" phase1_surface_rules =
    Some
      (ESequence
        [ ELiteral "[";
          ENonterminal "generic_param";
          ERepetition
            (ESequence
              [ ELiteral ",";
                ENonterminal "generic_param"
              ]);
          ELiteral "]"
        ]).
Proof.
  vm_compute.
  reflexivity.
Qed.

Definition phase1_surface_generic_kind_expression_for_totality
  (tag : Phase1SurfaceGenericKindTag) : EbnfExpression :=
  match tag with
  | Phase1TypeGenericKind => ELiteral "Type"
  | Phase1NatGenericKind => ELiteral "Nat"
  | Phase1SessionGenericKind => ELiteral "Session"
  | Phase1MessageGenericKind => ELiteral "Message"
  | Phase1EffectsGenericKind => ELiteral "Effects"
  | Phase1ProviderGenericKind =>
      ESequence [ELiteral "provider"; ENonterminal "type_expression"]
  | Phase1CallableGenericKind =>
      ESequence [ELiteral "callable"; ENonterminal "type_expression"]
  | Phase1BoundaryGenericKind =>
      ESequence [ELiteral "boundary"; ENonterminal "type_expression"]
  | Phase1ArchitectureGenericKind =>
      ESequence [ELiteral "architecture"; ENonterminal "type_expression"]
  end.

Lemma phase1_surface_generic_kind_item_matches_tag :
  forall index item,
    nth_error phase1_surface_generic_kind_items_for_totality index = Some item ->
    exists tag,
      phase1_surface_generic_kind_tag_of_index index = Some tag /\
      item = phase1_surface_generic_kind_expression_for_totality tag.
Proof.
  intros index item Hnth.
  destruct index as [|index]; cbn in Hnth.
  - inversion Hnth; subst item.
    exists Phase1TypeGenericKind. split; reflexivity.
  - destruct index as [|index]; cbn in Hnth.
    + inversion Hnth; subst item.
      exists Phase1NatGenericKind. split; reflexivity.
    + destruct index as [|index]; cbn in Hnth.
      * inversion Hnth; subst item.
        exists Phase1SessionGenericKind. split; reflexivity.
      * destruct index as [|index]; cbn in Hnth.
        -- inversion Hnth; subst item.
           exists Phase1MessageGenericKind. split; reflexivity.
        -- destruct index as [|index]; cbn in Hnth.
           ++ inversion Hnth; subst item.
              exists Phase1EffectsGenericKind. split; reflexivity.
           ++ destruct index as [|index]; cbn in Hnth.
              ** inversion Hnth; subst item.
                 exists Phase1ProviderGenericKind. split; reflexivity.
              ** destruct index as [|index]; cbn in Hnth.
                 --- inversion Hnth; subst item.
                     exists Phase1CallableGenericKind. split; reflexivity.
                 --- destruct index as [|index]; cbn in Hnth.
                     +++ inversion Hnth; subst item.
                         exists Phase1BoundaryGenericKind. split; reflexivity.
                     +++ destruct index as [|index]; cbn in Hnth.
                         *** inversion Hnth; subst item.
                             exists Phase1ArchitectureGenericKind.
                             split; reflexivity.
                         *** discriminate Hnth.
Qed.

Lemma phase1_surface_validate_typed_generic_kind_total_from_derivation :
  forall keyword path input rest tree,
    Derives phase1_surface_rules path
      (ESequence [ELiteral keyword; ENonterminal "type_expression"])
      input rest tree ->
    phase1_surface_validate_typed_generic_kind keyword tree = Some tt.
Proof.
  intros keyword path input rest tree Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ELiteral keyword; ENonterminal "type_expression"]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
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
      (ELiteral keyword) _ _ ?keyword_tree,
    Htype : Derives phase1_surface_rules _
      (ENonterminal "type_expression") _ _ ?type_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ keyword _ _ keyword_tree Hkeyword)
        as [keyword_tail [_ [_ Hkeyword_tree]]];
      destruct
        (derives_nonterminal_exposes_body
          phase1_surface_rules _ "type_expression"
          _ _ type_tree Htype)
        as [type_body [type_subtree [_ [Htype_tree Htype_body]]]];
      rewrite Htree;
      rewrite Hkeyword_tree;
      rewrite Htype_tree;
      unfold phase1_surface_validate_typed_generic_kind,
        phase1_surface_expect_sequence,
        phase1_surface_exact2,
        phase1_surface_expect_literal,
        phase1_surface_expect_nonterminal;
      cbn;
      rewrite String.eqb_refl;
      reflexivity
  end.
Qed.

Lemma phase1_surface_validate_generic_kind_selected_total_from_derivation :
  forall tag path input rest tree,
    Derives phase1_surface_rules path
      (phase1_surface_generic_kind_expression_for_totality tag)
      input rest tree ->
    phase1_surface_validate_generic_kind_selected tag tree = Some tt.
Proof.
  intros tag path input rest tree Hderive.
  destruct tag; cbn in Hderive |- *.
  - destruct
      (literal_derivation_is_exact
        phase1_surface_rules path "Type" input rest tree Hderive)
      as [tail [_ [_ Htree]]].
    rewrite Htree. reflexivity.
  - destruct
      (literal_derivation_is_exact
        phase1_surface_rules path "Nat" input rest tree Hderive)
      as [tail [_ [_ Htree]]].
    rewrite Htree. reflexivity.
  - destruct
      (literal_derivation_is_exact
        phase1_surface_rules path "Session" input rest tree Hderive)
      as [tail [_ [_ Htree]]].
    rewrite Htree. reflexivity.
  - destruct
      (literal_derivation_is_exact
        phase1_surface_rules path "Message" input rest tree Hderive)
      as [tail [_ [_ Htree]]].
    rewrite Htree. reflexivity.
  - destruct
      (literal_derivation_is_exact
        phase1_surface_rules path "Effects" input rest tree Hderive)
      as [tail [_ [_ Htree]]].
    rewrite Htree. reflexivity.
  - eapply phase1_surface_validate_typed_generic_kind_total_from_derivation.
    exact Hderive.
  - eapply phase1_surface_validate_typed_generic_kind_total_from_derivation.
    exact Hderive.
  - eapply phase1_surface_validate_typed_generic_kind_total_from_derivation.
    exact Hderive.
  - eapply phase1_surface_validate_typed_generic_kind_total_from_derivation.
    exact Hderive.
Qed.

Lemma phase1_surface_normalize_generic_kind_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "generic_kind")
      input rest tree ->
    exists kind,
      phase1_surface_normalize_generic_kind_spine tree = Some kind /\
      phase1_surface_generic_kind_spine_tree kind = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "generic_kind"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_generic_kind_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "generic_kind"))
      phase1_surface_generic_kind_items_for_totality
      input rest subtree Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  destruct
    (phase1_surface_generic_kind_item_matches_tag index item Hnth)
    as [tag [Htag Hitem]].
  subst item.
  pose proof
    (phase1_surface_validate_generic_kind_selected_total_from_derivation
      tag
      (descend
        (descend path (AtNonterminal "generic_kind"))
        (AtAlternative index))
      input rest selected Hselected) as Hvalidate.
  let kind := constr:(
    {| phase1_generic_kind_spine_tag := tag;
       phase1_generic_kind_spine_selected_tree := selected |}) in
  assert (Hnormalize :
    phase1_surface_normalize_generic_kind_spine tree = Some kind).
  {
    rewrite Htree.
    rewrite Hsubtree.
    unfold phase1_surface_normalize_generic_kind_spine,
      phase1_surface_expect_nonterminal,
      phase1_surface_expect_alternative.
    cbn.
    rewrite Htag.
    rewrite Hvalidate.
    reflexivity.
  }
  exists kind.
  split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_generic_kind_spine_round_trip.
    exact Hnormalize.
Qed.

Lemma phase1_surface_normalize_generic_param_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "generic_param")
      input rest tree ->
    exists parameter,
      phase1_surface_normalize_generic_param_spine tree = Some parameter /\
      phase1_surface_generic_param_spine_tree parameter = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "generic_param"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_generic_param_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "generic_param"))
      [ ENonterminal "identifier";
        ELiteral ":";
        ENonterminal "generic_kind"
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
      (ENonterminal "identifier") _ _ ?name_tree,
    Hcolon : Derives phase1_surface_rules _
      (ELiteral ":") _ _ ?colon_tree,
    Hkind : Derives phase1_surface_rules _
      (ENonterminal "generic_kind") _ _ ?kind_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ ":" _ _ colon_tree Hcolon)
        as [colon_tail [_ [_ Hcolon_tree]]];
      destruct
        (phase1_surface_normalize_identifier_total_from_derivation
          _ _ _ name_tree Hname)
        as [name Hname_normalize];
      destruct
        (phase1_surface_normalize_generic_kind_spine_total_from_derivation
          _ _ _ kind_tree Hkind)
        as [kind [Hkind_normalize Hkind_round_trip]];
      let parameter := constr:(
        {| phase1_generic_param_spine_name := name;
           phase1_generic_param_spine_kind := kind |}) in
      assert (Hnormalize :
        phase1_surface_normalize_generic_param_spine tree = Some parameter);
      [ rewrite Htree, Hsubtree, Hcolon_tree;
        unfold phase1_surface_normalize_generic_param_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_sequence,
          phase1_surface_exact3,
          phase1_surface_expect_literal;
        cbn;
        rewrite Hname_normalize;
        rewrite Hkind_normalize;
        reflexivity
      | exists parameter;
        split;
        [ exact Hnormalize
        | eapply phase1_surface_normalize_generic_param_spine_round_trip;
          exact Hnormalize ] ]
  end.
Qed.

Lemma phase1_surface_normalize_generic_param_suffix_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ESequence [ELiteral ","; ENonterminal "generic_param"])
      input rest tree ->
    exists parameter,
      phase1_surface_normalize_generic_param_suffix tree = Some parameter /\
      phase1_surface_generic_param_suffix_tree parameter = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ELiteral ","; ENonterminal "generic_param"]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hcomma : Derives phase1_surface_rules _
      (ELiteral ",") _ _ ?comma_tree,
    Hparameter : Derives phase1_surface_rules _
      (ENonterminal "generic_param") _ _ ?parameter_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "," _ _ comma_tree Hcomma)
        as [comma_tail [_ [_ Hcomma_tree]]];
      destruct
        (phase1_surface_normalize_generic_param_spine_total_from_derivation
          _ _ _ parameter_tree Hparameter)
        as [parameter [Hparameter_normalize Hparameter_round_trip]];
      assert (Hnormalize :
        phase1_surface_normalize_generic_param_suffix tree = Some parameter);
      [ rewrite Htree, Hcomma_tree;
        unfold phase1_surface_normalize_generic_param_suffix,
          phase1_surface_expect_sequence,
          phase1_surface_exact2,
          phase1_surface_expect_literal;
        cbn;
        rewrite Hparameter_normalize;
        reflexivity
      | exists parameter;
        split;
        [ exact Hnormalize
        | eapply phase1_surface_normalize_generic_param_suffix_round_trip;
          exact Hnormalize ] ]
  end.
Qed.

Lemma phase1_surface_normalize_generic_param_suffixes_total_from_repetition :
  forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body = ESequence [ELiteral ","; ENonterminal "generic_param"] ->
    exists parameters,
      phase1_surface_normalize_generic_param_suffixes trees = Some parameters.
Proof.
  intros path body input rest trees Hderive.
  induction Hderive as
    [path body input
    |path body input middle rest tree trees
       Hbody Hprogress Hrest IHrest];
    intros Hbody_shape.
  - exists [].
    reflexivity.
  - subst body.
    destruct
      (phase1_surface_normalize_generic_param_suffix_total_from_derivation
        (descend path AtRepetitionBody)
        input middle tree Hbody)
      as [parameter [Hparameter Hparameter_round_trip]].
    destruct (IHrest eq_refl) as [parameters Hparameters].
    exists (parameter :: parameters).
    cbn.
    rewrite Hparameter.
    rewrite Hparameters.
    reflexivity.
Qed.

Lemma phase1_surface_normalize_generic_params_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "generic_params")
      input rest tree ->
    exists parameters,
      phase1_surface_normalize_generic_params_spine tree = Some parameters /\
      phase1_surface_generic_params_spine_tree parameters = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "generic_params"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_generic_params_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "generic_params"))
      [ ELiteral "[";
        ENonterminal "generic_param";
        ERepetition
          (ESequence [ELiteral ","; ENonterminal "generic_param"]);
        ELiteral "]"
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
  | Hopen : Derives phase1_surface_rules _
      (ELiteral "[") _ _ ?open_tree,
    Hfirst : Derives phase1_surface_rules _
      (ENonterminal "generic_param") _ _ ?first_tree,
    Hrest : Derives phase1_surface_rules _
      (ERepetition
        (ESequence [ELiteral ","; ENonterminal "generic_param"]))
      _ _ ?rest_tree,
    Hclose : Derives phase1_surface_rules _
      (ELiteral "]") _ _ ?close_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "[" _ _ open_tree Hopen)
        as [open_tail [_ [_ Hopen_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "]" _ _ close_tree Hclose)
        as [close_tail [_ [_ Hclose_tree]]];
      destruct
        (phase1_surface_normalize_generic_param_spine_total_from_derivation
          _ _ _ first_tree Hfirst)
        as [first [Hfirst_normalize Hfirst_round_trip]];
      destruct
        (phase1_surface_repetition_derivation_exposes
          _
          (ESequence [ELiteral ","; ENonterminal "generic_param"])
          _ _ rest_tree Hrest)
        as [rest_trees [Hrest_tree Hrest_body]];
      destruct
        (phase1_surface_normalize_generic_param_suffixes_total_from_repetition
          _
          (ESequence [ELiteral ","; ENonterminal "generic_param"])
          _ _ rest_trees Hrest_body eq_refl)
        as [rest_parameters Hrest_normalize];
      let parameters := constr:(
        {| phase1_generic_params_spine_first := first;
           phase1_generic_params_spine_rest := rest_parameters |}) in
      assert (Hnormalize :
        phase1_surface_normalize_generic_params_spine tree = Some parameters);
      [ rewrite Htree, Hsubtree, Hopen_tree, Hrest_tree, Hclose_tree;
        unfold phase1_surface_normalize_generic_params_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_sequence,
          phase1_surface_exact4,
          phase1_surface_expect_literal,
          phase1_surface_expect_repetition;
        cbn;
        rewrite Hfirst_normalize;
        rewrite Hrest_normalize;
        reflexivity
      | exists parameters;
        split;
        [ exact Hnormalize
        | eapply phase1_surface_normalize_generic_params_spine_round_trip;
          exact Hnormalize ] ]
  end.
Qed.

Lemma phase1_surface_normalize_optional_generic_params_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (EOptional (ENonterminal "generic_params"))
      input rest tree ->
    exists parameters,
      phase1_surface_normalize_optional_generic_params tree = Some parameters /\
      phase1_surface_optional_generic_params_tree parameters = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (optional_derivation_exposes_presence
      phase1_surface_rules path
      (ENonterminal "generic_params")
      input rest tree Hderive)
    as [[_ Hnone] | [body [Hsome Hbody]]].
  - assert (Hnormalize :
      phase1_surface_normalize_optional_generic_params tree = Some None).
    {
      rewrite Hnone.
      reflexivity.
    }
    exists None.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_optional_generic_params_round_trip.
      exact Hnormalize.
  - destruct
      (phase1_surface_normalize_generic_params_spine_total_from_derivation
        (descend path AtOptionalBody)
        input rest body Hbody)
      as [parameters [Hparameters Hparameters_round_trip]].
    assert (Hnormalize :
      phase1_surface_normalize_optional_generic_params tree =
        Some (Some parameters)).
    {
      rewrite Hsome.
      unfold phase1_surface_normalize_optional_generic_params,
        phase1_surface_expect_optional.
      cbn.
      rewrite Hparameters.
      reflexivity.
    }
    exists (Some parameters).
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_optional_generic_params_round_trip.
      exact Hnormalize.
Qed.

Lemma phase1_surface_record_decl_generic_lookup_for_totality :
  exists mode_expr requirements_expr fields_expr,
    lookupRule "record_decl" phase1_surface_rules =
      Some
        (ESequence
          [ ELiteral "record";
            ENonterminal "identifier";
            EOptional (ENonterminal "generic_params");
            mode_expr;
            requirements_expr;
            ELiteral "{";
            fields_expr;
            ELiteral "}"
          ]).
Proof.
  vm_compute.
  do 3 eexists.
  reflexivity.
Qed.

Theorem phase1_surface_normalize_record_generic_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "record_decl")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_record_generic_tree tree = Some refined /\
      phase1_surface_record_generic_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct phase1_surface_record_decl_generic_lookup_for_totality
    as [mode_expr [requirements_expr [fields_expr Hlookup_exact]]].
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
        EOptional (ENonterminal "generic_params");
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
      (EOptional (ENonterminal "generic_params")) _ _ ?generic_tree,
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
      destruct
        (phase1_surface_normalize_optional_generic_params_total_from_derivation
          _ _ _ generic_tree Hgeneric)
        as [parameters [Hgeneric_normalize Hgeneric_round_trip]];
      let refined := constr:(
        {| phase1_record_generic_spine_name := name;
           phase1_record_generic_spine_generic_params := parameters;
           phase1_record_generic_spine_mode_tree := mode_tree;
           phase1_record_generic_spine_requirements_tree := requirements_tree;
           phase1_record_generic_spine_fields_tree := fields_tree |}) in
      assert (Hnormalize :
        phase1_surface_normalize_record_generic_tree tree = Some refined).
      {
        rewrite Htree.
        rewrite Hsubtree.
        rewrite Hkeyword_tree.
        rewrite Hopen_tree.
        rewrite Hclose_tree.
        unfold phase1_surface_normalize_record_generic_tree,
          phase1_surface_normalize_record_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_sequence,
          phase1_surface_exact8,
          phase1_surface_expect_literal,
          phase1_surface_normalize_record_generic_spine.
        cbn.
        rewrite Hname_normalize.
        rewrite Hgeneric_normalize.
        reflexivity.
      }
      exists refined.
      split.
      + exact Hnormalize.
      + eapply phase1_surface_normalize_record_generic_tree_round_trip.
        exact Hnormalize
  end.
Qed.
