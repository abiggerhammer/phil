From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstGenericParamKindTypeSpine
  GrammarAstGenericKindTypeTotality
  GrammarAstGenericParamsTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the generic-parameter kind-type lift from #1193. *)

Lemma
  phase1_surface_normalize_generic_param_kind_type_layers_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "generic_param")
      input rest tree ->
    exists base refined,
      phase1_surface_normalize_generic_param_spine tree = Some base /\
      phase1_surface_normalize_generic_param_kind_type_spine base =
        Some refined /\
      phase1_surface_generic_param_kind_type_spine_tree refined = tree.
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
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "generic_param")) 0
      (ENonterminal "identifier")
      [ ELiteral ":"; ENonterminal "generic_kind" ]
      input rest trees Hitems)
    as [after_name [name_tree [tail1
      [Htrees [Hname Htail1]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "generic_param")) 1
      (ELiteral ":")
      [ ENonterminal "generic_kind" ]
      after_name rest tail1 Htail1)
    as [after_colon [colon_tree [tail2
      [Htail1_trees [Hcolon Htail2]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "generic_param")) 2
      (ENonterminal "generic_kind") []
      after_colon rest tail2 Htail2)
    as [after_kind [kind_tree [nil_trees
      [Htail2_trees [Hkind Hnil]]]]].
  rewrite Htrees, Htail1_trees, Htail2_trees in Hsubtree.
  inversion Hnil; subst nil_trees.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ ":" _ _ colon_tree Hcolon)
    as [colon_tail [_ [_ Hcolon_tree]]].
  destruct
    (phase1_surface_normalize_identifier_total_from_derivation
      _ _ _ name_tree Hname)
    as [name Hname_normalize].
  destruct
    (phase1_surface_normalize_generic_kind_spine_total_from_derivation
      _ _ _ kind_tree Hkind)
    as [kind [Hkind_normalize Hkind_round_trip]].
  destruct
    (phase1_surface_normalize_generic_kind_type_tree_total_from_derivation
      _ _ _ kind_tree Hkind)
    as [refined_kind [Hrefined_kind_tree Hrefined_kind_round_trip]].
  assert (Hrefined_kind :
    phase1_surface_normalize_generic_kind_type_spine kind =
      Some refined_kind).
  {
    unfold phase1_surface_normalize_generic_kind_type_tree
      in Hrefined_kind_tree.
    rewrite Hkind_normalize in Hrefined_kind_tree.
    exact Hrefined_kind_tree.
  }
  pose (base :=
    {| phase1_generic_param_spine_name := name;
       phase1_generic_param_spine_kind := kind |}).
  pose (refined :=
    {| phase1_generic_param_kind_type_spine_name := name;
       phase1_generic_param_kind_type_spine_kind := refined_kind |}).
  assert (Hbase :
    phase1_surface_normalize_generic_param_spine tree = Some base).
  {
    rewrite Htree, Hsubtree, Hcolon_tree.
    unfold phase1_surface_normalize_generic_param_spine,
      phase1_surface_expect_nonterminal,
      phase1_surface_expect_sequence,
      phase1_surface_exact3,
      phase1_surface_expect_literal.
    cbn.
    rewrite Hname_normalize, Hkind_normalize.
    reflexivity.
  }
  assert (Hrefined :
    phase1_surface_normalize_generic_param_kind_type_spine base =
      Some refined).
  {
    unfold phase1_surface_normalize_generic_param_kind_type_spine.
    unfold base.
    cbn.
    rewrite Hrefined_kind.
    unfold refined.
    reflexivity.
  }
  exists base, refined.
  repeat split; try assumption.
  transitivity (phase1_surface_generic_param_spine_tree base).
  - eapply
      phase1_surface_normalize_generic_param_kind_type_spine_round_trip.
    exact Hrefined.
  - eapply phase1_surface_normalize_generic_param_spine_round_trip.
    exact Hbase.
Qed.

Lemma
  phase1_surface_normalize_generic_param_kind_type_suffix_layers_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ESequence [ELiteral ","; ENonterminal "generic_param"])
      input rest tree ->
    exists base refined,
      phase1_surface_normalize_generic_param_suffix tree = Some base /\
      phase1_surface_normalize_generic_param_kind_type_spine base =
        Some refined /\
      phase1_surface_generic_param_kind_type_suffix_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral ","; ENonterminal "generic_param" ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 0
      (ELiteral ",") [ENonterminal "generic_param"]
      input rest trees Hitems)
    as [after_comma [comma_tree [tail_trees
      [Htrees [Hcomma Htail]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 1
      (ENonterminal "generic_param") []
      after_comma rest tail_trees Htail)
    as [after_parameter [parameter_tree [nil_trees
      [Htail_trees [Hparameter Hnil]]]]].
  rewrite Htrees, Htail_trees in Htree.
  inversion Hnil; subst nil_trees.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "," _ _ comma_tree Hcomma)
    as [comma_tail [_ [_ Hcomma_tree]]].
  destruct
    (phase1_surface_normalize_generic_param_kind_type_layers_total_from_derivation
      _ _ _ parameter_tree Hparameter)
    as [base [refined [Hbase [Hrefined Hround_trip]]]].
  assert (Hsuffix :
    phase1_surface_normalize_generic_param_suffix tree = Some base).
  {
    rewrite Htree, Hcomma_tree.
    unfold phase1_surface_normalize_generic_param_suffix,
      phase1_surface_expect_sequence,
      phase1_surface_exact2,
      phase1_surface_expect_literal.
    cbn.
    rewrite Hbase.
    reflexivity.
  }
  exists base, refined.
  split.
  - exact Hsuffix.
  - split.
    + exact Hrefined.
    + unfold phase1_surface_generic_param_kind_type_suffix_tree.
      rewrite Htree, Hcomma_tree, Hround_trip.
      reflexivity.
Qed.

Lemma
  phase1_surface_normalize_generic_param_kind_type_suffixes_layers_total_from_repetition :
  forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body = ESequence [ELiteral ","; ENonterminal "generic_param"] ->
    exists bases refined,
      phase1_surface_normalize_generic_param_suffixes trees = Some bases /\
      phase1_surface_normalize_generic_param_kind_type_values bases =
        Some refined.
Proof.
  intros path body input rest trees Hderive.
  induction Hderive as
    [path body input
    |path body input middle rest tree trees
       Hbody Hprogress Hrest IHrest];
    intros Hbody_shape.
  - exists [], [].
    split; reflexivity.
  - subst body.
    destruct
      (phase1_surface_normalize_generic_param_kind_type_suffix_layers_total_from_derivation
        (descend path AtRepetitionBody)
        input middle tree Hbody)
      as [base [refined [Hbase [Hrefined Hround_trip]]]].
    destruct (IHrest eq_refl)
      as [bases [refined_rest [Hbases Hrefined_rest]]].
    exists (base :: bases), (refined :: refined_rest).
    split.
    + cbn. rewrite Hbase, Hbases. reflexivity.
    + cbn. rewrite Hrefined, Hrefined_rest. reflexivity.
Qed.

Theorem
  phase1_surface_normalize_generic_params_kind_type_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "generic_params")
      input rest tree ->
    exists base refined,
      phase1_surface_normalize_generic_params_spine tree = Some base /\
      phase1_surface_normalize_generic_params_kind_type_spine base =
        Some refined /\
      phase1_surface_generic_params_kind_type_spine_tree refined = tree.
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
  destruct
    (derives_sequence_cons_exposes_head_exact _ _ _ _ _ _ _ _ Hitems)
    as [after_open [open_tree [tail1
      [Htrees [Hopen Htail1]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact _ _ _ _ _ _ _ _ Htail1)
    as [after_first [first_tree [tail2
      [Htail1_trees [Hfirst Htail2]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact _ _ _ _ _ _ _ _ Htail2)
    as [after_rest [rest_tree [tail3
      [Htail2_trees [Hrest Htail3]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact _ _ _ _ _ _ _ _ Htail3)
    as [after_close [close_tree [nil_trees
      [Htail3_trees [Hclose Hnil]]]]].
  rewrite Htrees, Htail1_trees, Htail2_trees, Htail3_trees in Hsubtree.
  inversion Hnil; subst nil_trees.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "[" _ _ open_tree Hopen)
    as [open_tail [_ [_ Hopen_tree]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "]" _ _ close_tree Hclose)
    as [close_tail [_ [_ Hclose_tree]]].
  destruct
    (phase1_surface_normalize_generic_param_kind_type_layers_total_from_derivation
      _ _ _ first_tree Hfirst)
    as [base_first [refined_first
      [Hbase_first [Hrefined_first Hfirst_round_trip]]]].
  destruct
    (phase1_surface_repetition_derivation_exposes
      _
      (ESequence [ELiteral ","; ENonterminal "generic_param"])
      _ _ rest_tree Hrest)
    as [rest_trees [Hrest_tree Hrest_body]].
  destruct
    (phase1_surface_normalize_generic_param_kind_type_suffixes_layers_total_from_repetition
      _
      (ESequence [ELiteral ","; ENonterminal "generic_param"])
      _ _ rest_trees Hrest_body eq_refl)
    as [base_rest [refined_rest [Hbase_rest Hrefined_rest]]].
  pose (base :=
    {| phase1_generic_params_spine_first := base_first;
       phase1_generic_params_spine_rest := base_rest |}).
  pose (refined :=
    {| phase1_generic_params_kind_type_spine_first := refined_first;
       phase1_generic_params_kind_type_spine_rest := refined_rest |}).
  assert (Hbase :
    phase1_surface_normalize_generic_params_spine tree = Some base).
  {
    rewrite Htree, Hsubtree, Hopen_tree, Hrest_tree, Hclose_tree.
    unfold phase1_surface_normalize_generic_params_spine,
      phase1_surface_expect_nonterminal,
      phase1_surface_expect_sequence,
      phase1_surface_exact4,
      phase1_surface_expect_literal,
      phase1_surface_expect_repetition.
    cbn.
    rewrite Hbase_first, Hbase_rest.
    reflexivity.
  }
  assert (Hrefined :
    phase1_surface_normalize_generic_params_kind_type_spine base =
      Some refined).
  {
    unfold phase1_surface_normalize_generic_params_kind_type_spine.
    unfold base.
    cbn.
    rewrite Hrefined_first, Hrefined_rest.
    unfold refined.
    reflexivity.
  }
  exists base, refined.
  repeat split; try assumption.
  transitivity (phase1_surface_generic_params_spine_tree base).
  - eapply
      phase1_surface_normalize_generic_params_kind_type_spine_round_trip.
    exact Hrefined.
  - eapply phase1_surface_normalize_generic_params_spine_round_trip.
    exact Hbase.
Qed.

Definition phase1_surface_normalize_optional_generic_params_kind_type_tree
  (tree : ParseTree)
  : option (option Phase1SurfaceGenericParamsKindTypeSpine) :=
  match phase1_surface_normalize_optional_generic_params tree with
  | Some parameters =>
      phase1_surface_normalize_optional_generic_params_kind_type parameters
  | None => None
  end.

Theorem
  phase1_surface_normalize_optional_generic_params_kind_type_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_optional_generic_params_kind_type_tree tree =
      Some refined ->
    phase1_surface_optional_generic_params_kind_type_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_optional_generic_params_kind_type_tree
    in Hnormalize.
  destruct (phase1_surface_normalize_optional_generic_params tree)
    as [parameters |] eqn:Hparameters; try discriminate Hnormalize.
  transitivity (phase1_surface_optional_generic_params_tree parameters).
  - eapply
      phase1_surface_normalize_optional_generic_params_kind_type_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_optional_generic_params_round_trip.
    exact Hparameters.
Qed.

Theorem
  phase1_surface_normalize_optional_generic_params_kind_type_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (EOptional (ENonterminal "generic_params"))
      input rest tree ->
    exists base refined,
      phase1_surface_normalize_optional_generic_params tree = Some base /\
      phase1_surface_normalize_optional_generic_params_kind_type base =
        Some refined /\
      phase1_surface_optional_generic_params_kind_type_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (optional_derivation_exposes_presence
      phase1_surface_rules path
      (ENonterminal "generic_params")
      input rest tree Hderive)
    as [[_ Hnone] | [body [Hsome Hbody]]].
  - exists None, None.
    split.
    + rewrite Hnone. reflexivity.
    + split.
      * reflexivity.
      * rewrite Hnone. reflexivity.
  - destruct
      (phase1_surface_normalize_generic_params_kind_type_tree_total_from_derivation
        (descend path AtOptionalBody)
        input rest body Hbody)
      as [base [refined [Hbase [Hrefined Hround_trip]]]].
    assert (Hbase_optional :
      phase1_surface_normalize_optional_generic_params tree =
        Some (Some base)).
    {
      rewrite Hsome.
      unfold phase1_surface_normalize_optional_generic_params,
        phase1_surface_expect_optional.
      cbn.
      rewrite Hbase.
      reflexivity.
    }
    assert (Hrefined_optional :
      phase1_surface_normalize_optional_generic_params_kind_type (Some base) =
        Some (Some refined)).
    {
      cbn.
      rewrite Hrefined.
      reflexivity.
    }
    exists (Some base), (Some refined).
    split.
    + exact Hbase_optional.
    + split.
      * exact Hrefined_optional.
      * rewrite Hsome.
        cbn.
        exact (f_equal PTOptionalSome Hround_trip).
Qed.
