From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstGenericRequirementsSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Final shared record payload refinement for PHIL-SURFACE-GRAMMAR-CORR-001.

  The requirements-refined record carrier still retains the record field slot
  as a certified ParseTree.  This layer normalizes field_decl names, preserves
  each nested type_expression payload exactly, normalizes comma-separated field
  lists including the optional trailing comma, and then refines the record
  carrier to hold that normalized structure.
*)

Record Phase1SurfaceFieldSpine : Type := {
  phase1_field_spine_name : string;
  phase1_field_spine_type_tree : ParseTree
}.

Definition phase1_surface_field_spine_tree
  (field : Phase1SurfaceFieldSpine) : ParseTree :=
  PTNonterminal "field_decl"
    (PTSequence
      [ phase1_surface_identifier_tree (phase1_field_spine_name field);
        PTLiteral ":";
        phase1_field_spine_type_tree field
      ]).

Definition phase1_surface_normalize_field_spine
  (tree : ParseTree) : option Phase1SurfaceFieldSpine :=
  match phase1_surface_expect_nonterminal "field_decl" tree with
  | Some body =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact3 items with
          | Some (name_tree, colon_tree, type_tree) =>
              match phase1_surface_normalize_identifier name_tree,
                    phase1_surface_expect_literal ":" colon_tree,
                    phase1_surface_validate_named_node "type_expression" type_tree with
              | Some name, Some tt, Some tt =>
                  Some
                    {| phase1_field_spine_name := name;
                       phase1_field_spine_type_tree := type_tree |}
              | _, _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_field_spine_round_trip :
  forall tree field,
    phase1_surface_normalize_field_spine tree = Some field ->
    phase1_surface_field_spine_tree field = tree.
Proof.
  intros tree field Hnormalize.
  unfold phase1_surface_normalize_field_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "field_decl" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_sequence body)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact3 items)
    as [[[name_tree colon_tree] type_tree] |] eqn:Hitems;
    try discriminate Hnormalize.
  destruct (phase1_surface_normalize_identifier name_tree)
    as [name |] eqn:Hname; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal ":" colon_tree)
    as [[] |] eqn:Hcolon; try discriminate Hnormalize.
  destruct (phase1_surface_validate_named_node "type_expression" type_tree)
    as [[] |] eqn:Htype; try discriminate Hnormalize.
  inversion Hnormalize; subst field.
  unfold phase1_surface_field_spine_tree.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    "field_decl" tree body Hnode).
  rewrite (phase1_surface_expect_sequence_round_trip body items Hsequence).
  rewrite (phase1_surface_exact3_round_trip
    items name_tree colon_tree type_tree Hitems).
  rewrite (phase1_surface_normalize_identifier_round_trip
    name_tree name Hname).
  rewrite (phase1_surface_expect_literal_round_trip ":" colon_tree Hcolon).
  reflexivity.
Qed.

Definition phase1_surface_field_suffix_tree
  (field : Phase1SurfaceFieldSpine) : ParseTree :=
  PTSequence
    [ PTLiteral ",";
      phase1_surface_field_spine_tree field
    ].

Definition phase1_surface_normalize_field_suffix
  (tree : ParseTree) : option Phase1SurfaceFieldSpine :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact2 items with
      | Some (comma_tree, field_tree) =>
          match phase1_surface_expect_literal "," comma_tree,
                phase1_surface_normalize_field_spine field_tree with
          | Some tt, Some field => Some field
          | _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_field_suffix_round_trip :
  forall tree field,
    phase1_surface_normalize_field_suffix tree = Some field ->
    phase1_surface_field_suffix_tree field = tree.
Proof.
  intros tree field Hnormalize.
  unfold phase1_surface_normalize_field_suffix in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items)
    as [[comma_tree field_tree] |] eqn:Hitems; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "," comma_tree)
    as [[] |] eqn:Hcomma; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_field_spine field_tree)
    as [actual |] eqn:Hfield; try discriminate Hnormalize.
  inversion Hnormalize; subst field.
  unfold phase1_surface_field_suffix_tree.
  rewrite (phase1_surface_expect_sequence_round_trip tree items Hsequence).
  rewrite (phase1_surface_exact2_round_trip items comma_tree field_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip "," comma_tree Hcomma).
  rewrite (phase1_surface_normalize_field_spine_round_trip
    field_tree actual Hfield).
  reflexivity.
Qed.

Fixpoint phase1_surface_normalize_field_suffixes
  (trees : list ParseTree) : option (list Phase1SurfaceFieldSpine) :=
  match trees with
  | [] => Some []
  | tree :: rest =>
      match phase1_surface_normalize_field_suffix tree,
            phase1_surface_normalize_field_suffixes rest with
      | Some field, Some fields => Some (field :: fields)
      | _, _ => None
      end
  end.

Theorem phase1_surface_normalize_field_suffixes_round_trip :
  forall trees fields,
    phase1_surface_normalize_field_suffixes trees = Some fields ->
    map phase1_surface_field_suffix_tree fields = trees.
Proof.
  intros trees.
  induction trees as [|tree rest IH]; intros fields Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst fields.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_field_suffix tree)
      as [field |] eqn:Hfield; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_field_suffixes rest)
      as [rest_fields |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst fields.
    cbn.
    f_equal.
    + eapply phase1_surface_normalize_field_suffix_round_trip.
      exact Hfield.
    + eapply IH.
      exact Hrest.
Qed.

Definition phase1_surface_trailing_comma_tree
  (present : bool) : ParseTree :=
  if present
  then PTOptionalSome (PTLiteral ",")
  else PTOptionalNone.

Definition phase1_surface_normalize_trailing_comma
  (tree : ParseTree) : option bool :=
  match phase1_surface_expect_optional tree with
  | Some None => Some false
  | Some (Some comma_tree) =>
      match phase1_surface_expect_literal "," comma_tree with
      | Some tt => Some true
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_trailing_comma_round_trip :
  forall tree present,
    phase1_surface_normalize_trailing_comma tree = Some present ->
    phase1_surface_trailing_comma_tree present = tree.
Proof.
  intros tree present Hnormalize.
  unfold phase1_surface_normalize_trailing_comma in Hnormalize.
  destruct (phase1_surface_expect_optional tree)
    as [[comma_tree |] |] eqn:Hoptional; try discriminate Hnormalize.
  - destruct (phase1_surface_expect_literal "," comma_tree)
      as [[] |] eqn:Hcomma; try discriminate Hnormalize.
    inversion Hnormalize; subst present.
    unfold phase1_surface_trailing_comma_tree.
    rewrite (phase1_surface_expect_optional_round_trip
      tree (Some comma_tree) Hoptional).
    rewrite (phase1_surface_expect_literal_round_trip "," comma_tree Hcomma).
    reflexivity.
  - inversion Hnormalize; subst present.
    unfold phase1_surface_trailing_comma_tree.
    rewrite (phase1_surface_expect_optional_round_trip tree None Hoptional).
    reflexivity.
Qed.

Record Phase1SurfaceFieldListSpine : Type := {
  phase1_field_list_spine_first : Phase1SurfaceFieldSpine;
  phase1_field_list_spine_rest : list Phase1SurfaceFieldSpine;
  phase1_field_list_spine_trailing_comma : bool
}.

Definition phase1_surface_field_list_spine_tree
  (fields : Phase1SurfaceFieldListSpine) : ParseTree :=
  PTSequence
    [ phase1_surface_field_spine_tree
        (phase1_field_list_spine_first fields);
      PTRepetition
        (map phase1_surface_field_suffix_tree
          (phase1_field_list_spine_rest fields));
      phase1_surface_trailing_comma_tree
        (phase1_field_list_spine_trailing_comma fields)
    ].

Definition phase1_surface_normalize_field_list_spine
  (tree : ParseTree) : option Phase1SurfaceFieldListSpine :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact3 items with
      | Some (first_tree, rest_tree, trailing_tree) =>
          match phase1_surface_normalize_field_spine first_tree,
                phase1_surface_expect_repetition rest_tree,
                phase1_surface_normalize_trailing_comma trailing_tree with
          | Some first, Some rest_trees, Some trailing =>
              match phase1_surface_normalize_field_suffixes rest_trees with
              | Some rest =>
                  Some
                    {| phase1_field_list_spine_first := first;
                       phase1_field_list_spine_rest := rest;
                       phase1_field_list_spine_trailing_comma := trailing |}
              | None => None
              end
          | _, _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_field_list_spine_round_trip :
  forall tree fields,
    phase1_surface_normalize_field_list_spine tree = Some fields ->
    phase1_surface_field_list_spine_tree fields = tree.
Proof.
  intros tree fields Hnormalize.
  unfold phase1_surface_normalize_field_list_spine in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact3 items)
    as [[[first_tree rest_tree] trailing_tree] |] eqn:Hitems;
    try discriminate Hnormalize.
  destruct (phase1_surface_normalize_field_spine first_tree)
    as [first |] eqn:Hfirst; try discriminate Hnormalize.
  destruct (phase1_surface_expect_repetition rest_tree)
    as [rest_trees |] eqn:Hrest_trees; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_trailing_comma trailing_tree)
    as [trailing |] eqn:Htrailing; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_field_suffixes rest_trees)
    as [rest |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst fields.
  unfold phase1_surface_field_list_spine_tree.
  rewrite (phase1_surface_expect_sequence_round_trip tree items Hsequence).
  rewrite (phase1_surface_exact3_round_trip
    items first_tree rest_tree trailing_tree Hitems).
  rewrite (phase1_surface_normalize_field_spine_round_trip
    first_tree first Hfirst).
  rewrite (phase1_surface_expect_repetition_round_trip
    rest_tree rest_trees Hrest_trees).
  rewrite (phase1_surface_normalize_field_suffixes_round_trip
    rest_trees rest Hrest).
  rewrite (phase1_surface_normalize_trailing_comma_round_trip
    trailing_tree trailing Htrailing).
  reflexivity.
Qed.

Definition phase1_surface_optional_fields_tree
  (fields : option Phase1SurfaceFieldListSpine) : ParseTree :=
  match fields with
  | None => PTOptionalNone
  | Some value => PTOptionalSome (phase1_surface_field_list_spine_tree value)
  end.

Definition phase1_surface_normalize_optional_fields
  (tree : ParseTree) : option (option Phase1SurfaceFieldListSpine) :=
  match phase1_surface_expect_optional tree with
  | Some None => Some None
  | Some (Some body) =>
      match phase1_surface_normalize_field_list_spine body with
      | Some fields => Some (Some fields)
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_optional_fields_round_trip :
  forall tree fields,
    phase1_surface_normalize_optional_fields tree = Some fields ->
    phase1_surface_optional_fields_tree fields = tree.
Proof.
  intros tree fields Hnormalize.
  unfold phase1_surface_normalize_optional_fields in Hnormalize.
  destruct (phase1_surface_expect_optional tree)
    as [[body |] |] eqn:Hoptional; try discriminate Hnormalize.
  - destruct (phase1_surface_normalize_field_list_spine body)
      as [actual |] eqn:Hfields; try discriminate Hnormalize.
    inversion Hnormalize; subst fields.
    unfold phase1_surface_optional_fields_tree.
    rewrite (phase1_surface_expect_optional_round_trip
      tree (Some body) Hoptional).
    rewrite (phase1_surface_normalize_field_list_spine_round_trip
      body actual Hfields).
    reflexivity.
  - inversion Hnormalize; subst fields.
    unfold phase1_surface_optional_fields_tree.
    rewrite (phase1_surface_expect_optional_round_trip tree None Hoptional).
    reflexivity.
Qed.

Record Phase1SurfaceRecordFieldsSpine : Type := {
  phase1_record_fields_spine_name : string;
  phase1_record_fields_spine_generic_params : option Phase1SurfaceGenericParamsSpine;
  phase1_record_fields_spine_mode : option Phase1SurfaceStructuralMode;
  phase1_record_fields_spine_requirements : option Phase1SurfaceGenericRequirementsSpine;
  phase1_record_fields_spine_fields : option Phase1SurfaceFieldListSpine
}.

Definition phase1_surface_record_fields_spine_tree
  (record : Phase1SurfaceRecordFieldsSpine) : ParseTree :=
  PTNonterminal "record_decl"
    (PTSequence
      [ PTLiteral "record";
        phase1_surface_identifier_tree
          (phase1_record_fields_spine_name record);
        phase1_surface_optional_generic_params_tree
          (phase1_record_fields_spine_generic_params record);
        phase1_surface_optional_mode_tree
          (phase1_record_fields_spine_mode record);
        phase1_surface_optional_generic_requirements_tree
          (phase1_record_fields_spine_requirements record);
        PTLiteral "{";
        phase1_surface_optional_fields_tree
          (phase1_record_fields_spine_fields record);
        PTLiteral "}"
      ]).

Definition phase1_surface_normalize_record_fields_spine
  (record : Phase1SurfaceRecordRequirementsSpine)
  : option Phase1SurfaceRecordFieldsSpine :=
  match phase1_surface_normalize_optional_fields
          (phase1_record_requirements_spine_fields_tree record) with
  | Some fields =>
      Some
        {| phase1_record_fields_spine_name :=
             phase1_record_requirements_spine_name record;
           phase1_record_fields_spine_generic_params :=
             phase1_record_requirements_spine_generic_params record;
           phase1_record_fields_spine_mode :=
             phase1_record_requirements_spine_mode record;
           phase1_record_fields_spine_requirements :=
             phase1_record_requirements_spine_requirements record;
           phase1_record_fields_spine_fields := fields |}
  | None => None
  end.

Theorem phase1_surface_normalize_record_fields_spine_round_trip :
  forall record refined,
    phase1_surface_normalize_record_fields_spine record = Some refined ->
    phase1_surface_record_fields_spine_tree refined =
      phase1_surface_record_requirements_spine_tree record.
Proof.
  intros [name generic_params mode requirements fields_tree]
    refined Hnormalize.
  cbn in Hnormalize.
  destruct (phase1_surface_normalize_optional_fields fields_tree)
    as [fields |] eqn:Hfields; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  unfold phase1_surface_record_fields_spine_tree,
    phase1_surface_record_requirements_spine_tree.
  cbn.
  rewrite (phase1_surface_normalize_optional_fields_round_trip
    fields_tree fields Hfields).
  reflexivity.
Qed.

Definition phase1_surface_normalize_record_fields_tree
  (tree : ParseTree) : option Phase1SurfaceRecordFieldsSpine :=
  match phase1_surface_normalize_record_requirements_tree tree with
  | Some record => phase1_surface_normalize_record_fields_spine record
  | None => None
  end.

Theorem phase1_surface_normalize_record_fields_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_record_fields_tree tree = Some refined ->
    phase1_surface_record_fields_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_record_fields_tree in Hnormalize.
  destruct (phase1_surface_normalize_record_requirements_tree tree)
    as [record |] eqn:Hrecord; try discriminate Hnormalize.
  transitivity (phase1_surface_record_requirements_spine_tree record).
  - eapply phase1_surface_normalize_record_fields_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_record_requirements_tree_round_trip.
    exact Hrecord.
Qed.
