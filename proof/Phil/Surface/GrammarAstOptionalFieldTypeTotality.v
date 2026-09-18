From Phil.Surface Require Import
  GrammarAstOptionalFieldTypeSpine
  GrammarAstFieldTypeListTotality
  GrammarAstRecordFieldsTotality.

(* Converse for the optional-fields type refinement from #1166. *)

Theorem phase1_surface_normalize_optional_field_type_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_optional_fields_expression_for_totality
      input rest tree ->
    exists base refined,
      phase1_surface_normalize_optional_fields tree = Some base /\
      phase1_surface_normalize_optional_field_type_list base = Some refined /\
      phase1_surface_optional_field_type_list_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  unfold phase1_surface_optional_fields_expression_for_totality in Hderive.
  destruct
    (optional_derivation_exposes_presence
      phase1_surface_rules path
      phase1_surface_field_list_expression_for_totality
      input rest tree Hderive)
    as [[_ Hnone] | [body [Hsome Hbody]]].
  - exists None, None.
    split.
    + rewrite Hnone.
      reflexivity.
    + split.
      * reflexivity.
      * rewrite Hnone.
        reflexivity.
  - destruct
      (phase1_surface_normalize_field_type_list_layers_total_from_derivation
        (descend path AtOptionalBody)
        input rest body Hbody)
      as [base [refined [Hbase [Hrefined Hrefined_tree]]]].
    assert (Hbase_optional :
      phase1_surface_normalize_optional_fields tree = Some (Some base)).
    {
      rewrite Hsome.
      unfold phase1_surface_normalize_optional_fields,
        phase1_surface_expect_optional.
      cbn.
      rewrite Hbase.
      reflexivity.
    }
    assert (Hrefined_optional :
      phase1_surface_normalize_optional_field_type_list (Some base) =
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
        exact (f_equal PTOptionalSome Hrefined_tree).
Qed.
