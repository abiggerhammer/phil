From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstRecordSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Shared generic-parameter correspondence for PHIL-SURFACE-GRAMMAR-CORR-001.

  The record declaration carrier from #934 retains the optional generic_params
  slot as a certified ParseTree.  This layer normalizes that shared syntax:
  generic-kind choice becomes a closed nine-way tag, parameter names become
  exact identifier strings, generic parameter lists become ordered nonempty
  semantic spines, and the record carrier is refined to hold the normalized
  optional generic-parameter value.

  Nested type_expression payloads of provider/callable/boundary/architecture
  generic kinds deliberately remain certified ParseTree values for the later
  type-payload correspondence tranche.
*)

Inductive Phase1SurfaceGenericKindTag : Type :=
| Phase1TypeGenericKind
| Phase1NatGenericKind
| Phase1SessionGenericKind
| Phase1MessageGenericKind
| Phase1EffectsGenericKind
| Phase1ProviderGenericKind
| Phase1CallableGenericKind
| Phase1BoundaryGenericKind
| Phase1ArchitectureGenericKind.

Definition phase1_surface_generic_kind_tag_index
  (tag : Phase1SurfaceGenericKindTag) : nat :=
  match tag with
  | Phase1TypeGenericKind => 0
  | Phase1NatGenericKind => 1
  | Phase1SessionGenericKind => 2
  | Phase1MessageGenericKind => 3
  | Phase1EffectsGenericKind => 4
  | Phase1ProviderGenericKind => 5
  | Phase1CallableGenericKind => 6
  | Phase1BoundaryGenericKind => 7
  | Phase1ArchitectureGenericKind => 8
  end.

Definition phase1_surface_generic_kind_tag_of_index
  (index : nat) : option Phase1SurfaceGenericKindTag :=
  match index with
  | 0 => Some Phase1TypeGenericKind
  | 1 => Some Phase1NatGenericKind
  | 2 => Some Phase1SessionGenericKind
  | 3 => Some Phase1MessageGenericKind
  | 4 => Some Phase1EffectsGenericKind
  | 5 => Some Phase1ProviderGenericKind
  | 6 => Some Phase1CallableGenericKind
  | 7 => Some Phase1BoundaryGenericKind
  | 8 => Some Phase1ArchitectureGenericKind
  | _ => None
  end.

Lemma phase1_surface_generic_kind_tag_index_round_trip :
  forall index tag,
    phase1_surface_generic_kind_tag_of_index index = Some tag ->
    phase1_surface_generic_kind_tag_index tag = index.
Proof.
  intros index tag Htag.
  destruct index as [|index]; cbn in Htag.
  - inversion Htag; reflexivity.
  - destruct index as [|index]; cbn in Htag.
    + inversion Htag; reflexivity.
    + destruct index as [|index]; cbn in Htag.
      * inversion Htag; reflexivity.
      * destruct index as [|index]; cbn in Htag.
        -- inversion Htag; reflexivity.
        -- destruct index as [|index]; cbn in Htag.
           ++ inversion Htag; reflexivity.
           ++ destruct index as [|index]; cbn in Htag.
              ** inversion Htag; reflexivity.
              ** destruct index as [|index]; cbn in Htag.
                 --- inversion Htag; reflexivity.
                 --- destruct index as [|index]; cbn in Htag.
                     +++ inversion Htag; reflexivity.
                     +++ destruct index as [|index]; cbn in Htag.
                         *** inversion Htag; reflexivity.
                         *** discriminate Htag.
Qed.

Definition phase1_surface_validate_typed_generic_kind
  (keyword : string)
  (tree : ParseTree) : option unit :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact2 items with
      | Some (keyword_tree, type_tree) =>
          match phase1_surface_expect_literal keyword keyword_tree,
                phase1_surface_expect_nonterminal "type_expression" type_tree with
          | Some tt, Some _ => Some tt
          | _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Definition phase1_surface_validate_generic_kind_selected
  (tag : Phase1SurfaceGenericKindTag)
  (tree : ParseTree) : option unit :=
  match tag with
  | Phase1TypeGenericKind => phase1_surface_expect_literal "Type" tree
  | Phase1NatGenericKind => phase1_surface_expect_literal "Nat" tree
  | Phase1SessionGenericKind => phase1_surface_expect_literal "Session" tree
  | Phase1MessageGenericKind => phase1_surface_expect_literal "Message" tree
  | Phase1EffectsGenericKind => phase1_surface_expect_literal "Effects" tree
  | Phase1ProviderGenericKind =>
      phase1_surface_validate_typed_generic_kind "provider" tree
  | Phase1CallableGenericKind =>
      phase1_surface_validate_typed_generic_kind "callable" tree
  | Phase1BoundaryGenericKind =>
      phase1_surface_validate_typed_generic_kind "boundary" tree
  | Phase1ArchitectureGenericKind =>
      phase1_surface_validate_typed_generic_kind "architecture" tree
  end.

Record Phase1SurfaceGenericKindSpine : Type := {
  phase1_generic_kind_spine_tag : Phase1SurfaceGenericKindTag;
  phase1_generic_kind_spine_selected_tree : ParseTree
}.

Definition phase1_surface_generic_kind_spine_tree
  (kind : Phase1SurfaceGenericKindSpine) : ParseTree :=
  PTNonterminal "generic_kind"
    (PTAlternative
      (phase1_surface_generic_kind_tag_index
        (phase1_generic_kind_spine_tag kind))
      (phase1_generic_kind_spine_selected_tree kind)).

Definition phase1_surface_normalize_generic_kind_spine
  (tree : ParseTree) : option Phase1SurfaceGenericKindSpine :=
  match phase1_surface_expect_nonterminal "generic_kind" tree with
  | Some body =>
      match phase1_surface_expect_alternative body with
      | Some (index, selected) =>
          match phase1_surface_generic_kind_tag_of_index index with
          | Some tag =>
              match phase1_surface_validate_generic_kind_selected tag selected with
              | Some tt =>
                  Some
                    {| phase1_generic_kind_spine_tag := tag;
                       phase1_generic_kind_spine_selected_tree := selected |}
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_generic_kind_spine_round_trip :
  forall tree kind,
    phase1_surface_normalize_generic_kind_spine tree = Some kind ->
    phase1_surface_generic_kind_spine_tree kind = tree.
Proof.
  intros tree kind Hnormalize.
  unfold phase1_surface_normalize_generic_kind_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "generic_kind" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_alternative body)
    as [[index selected] |] eqn:Halternative; try discriminate Hnormalize.
  destruct (phase1_surface_generic_kind_tag_of_index index)
    as [tag |] eqn:Htag; try discriminate Hnormalize.
  destruct (phase1_surface_validate_generic_kind_selected tag selected)
    as [[] |] eqn:Hselected; try discriminate Hnormalize.
  inversion Hnormalize; subst kind.
  unfold phase1_surface_generic_kind_spine_tree.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    "generic_kind" tree body Hnode).
  rewrite (phase1_surface_expect_alternative_round_trip
    body index selected Halternative).
  rewrite (phase1_surface_generic_kind_tag_index_round_trip index tag Htag).
  reflexivity.
Qed.

Record Phase1SurfaceGenericParamSpine : Type := {
  phase1_generic_param_spine_name : string;
  phase1_generic_param_spine_kind : Phase1SurfaceGenericKindSpine
}.

Definition phase1_surface_generic_param_spine_tree
  (parameter : Phase1SurfaceGenericParamSpine) : ParseTree :=
  PTNonterminal "generic_param"
    (PTSequence
      [ phase1_surface_identifier_tree
          (phase1_generic_param_spine_name parameter);
        PTLiteral ":";
        phase1_surface_generic_kind_spine_tree
          (phase1_generic_param_spine_kind parameter)
      ]).

Definition phase1_surface_normalize_generic_param_spine
  (tree : ParseTree) : option Phase1SurfaceGenericParamSpine :=
  match phase1_surface_expect_nonterminal "generic_param" tree with
  | Some body =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact3 items with
          | Some (name_tree, colon_tree, kind_tree) =>
              match phase1_surface_expect_literal ":" colon_tree with
              | Some tt =>
                  match phase1_surface_normalize_identifier name_tree,
                        phase1_surface_normalize_generic_kind_spine kind_tree with
                  | Some name, Some kind =>
                      Some
                        {| phase1_generic_param_spine_name := name;
                           phase1_generic_param_spine_kind := kind |}
                  | _, _ => None
                  end
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_generic_param_spine_round_trip :
  forall tree parameter,
    phase1_surface_normalize_generic_param_spine tree = Some parameter ->
    phase1_surface_generic_param_spine_tree parameter = tree.
Proof.
  intros tree parameter Hnormalize.
  unfold phase1_surface_normalize_generic_param_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "generic_param" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_sequence body)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact3 items)
    as [[[name_tree colon_tree] kind_tree] |] eqn:Hitems;
    try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal ":" colon_tree)
    as [[] |] eqn:Hcolon; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_identifier name_tree)
    as [name |] eqn:Hname; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_generic_kind_spine kind_tree)
    as [kind |] eqn:Hkind; try discriminate Hnormalize.
  inversion Hnormalize; subst parameter.
  unfold phase1_surface_generic_param_spine_tree.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    "generic_param" tree body Hnode).
  rewrite (phase1_surface_expect_sequence_round_trip body items Hsequence).
  rewrite (phase1_surface_exact3_round_trip
    items name_tree colon_tree kind_tree Hitems).
  rewrite (phase1_surface_normalize_identifier_round_trip name_tree name Hname).
  rewrite (phase1_surface_expect_literal_round_trip ":" colon_tree Hcolon).
  rewrite (phase1_surface_normalize_generic_kind_spine_round_trip
    kind_tree kind Hkind).
  reflexivity.
Qed.

Definition phase1_surface_generic_param_suffix_tree
  (parameter : Phase1SurfaceGenericParamSpine) : ParseTree :=
  PTSequence
    [ PTLiteral ",";
      phase1_surface_generic_param_spine_tree parameter
    ].

Definition phase1_surface_normalize_generic_param_suffix
  (tree : ParseTree) : option Phase1SurfaceGenericParamSpine :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact2 items with
      | Some (comma_tree, parameter_tree) =>
          match phase1_surface_expect_literal "," comma_tree with
          | Some tt => phase1_surface_normalize_generic_param_spine parameter_tree
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_generic_param_suffix_round_trip :
  forall tree parameter,
    phase1_surface_normalize_generic_param_suffix tree = Some parameter ->
    phase1_surface_generic_param_suffix_tree parameter = tree.
Proof.
  intros tree parameter Hnormalize.
  unfold phase1_surface_normalize_generic_param_suffix in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items)
    as [[comma_tree parameter_tree] |] eqn:Hitems;
    try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "," comma_tree)
    as [[] |] eqn:Hcomma; try discriminate Hnormalize.
  pose proof
    (phase1_surface_normalize_generic_param_spine_round_trip
      parameter_tree parameter Hnormalize) as Hparameter.
  rewrite (phase1_surface_expect_sequence_round_trip tree items Hsequence).
  rewrite (phase1_surface_exact2_round_trip
    items comma_tree parameter_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip "," comma_tree Hcomma).
  rewrite Hparameter.
  reflexivity.
Qed.

Fixpoint phase1_surface_normalize_generic_param_suffixes
  (trees : list ParseTree) : option (list Phase1SurfaceGenericParamSpine) :=
  match trees with
  | [] => Some []
  | tree :: rest =>
      match phase1_surface_normalize_generic_param_suffix tree,
            phase1_surface_normalize_generic_param_suffixes rest with
      | Some parameter, Some parameters => Some (parameter :: parameters)
      | _, _ => None
      end
  end.

Theorem phase1_surface_normalize_generic_param_suffixes_round_trip :
  forall trees parameters,
    phase1_surface_normalize_generic_param_suffixes trees = Some parameters ->
    map phase1_surface_generic_param_suffix_tree parameters = trees.
Proof.
  intros trees.
  induction trees as [|tree rest IH]; intros parameters Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_generic_param_suffix tree)
      as [parameter |] eqn:Htree; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_generic_param_suffixes rest)
      as [rest_parameters |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst.
    cbn.
    f_equal.
    + eapply phase1_surface_normalize_generic_param_suffix_round_trip.
      exact Htree.
    + eapply IH.
      exact Hrest.
Qed.

Record Phase1SurfaceGenericParamsSpine : Type := {
  phase1_generic_params_spine_first : Phase1SurfaceGenericParamSpine;
  phase1_generic_params_spine_rest : list Phase1SurfaceGenericParamSpine
}.

Definition phase1_surface_generic_params_spine_tree
  (parameters : Phase1SurfaceGenericParamsSpine) : ParseTree :=
  PTNonterminal "generic_params"
    (PTSequence
      [ PTLiteral "[";
        phase1_surface_generic_param_spine_tree
          (phase1_generic_params_spine_first parameters);
        PTRepetition
          (map phase1_surface_generic_param_suffix_tree
            (phase1_generic_params_spine_rest parameters));
        PTLiteral "]"
      ]).

Definition phase1_surface_normalize_generic_params_spine
  (tree : ParseTree) : option Phase1SurfaceGenericParamsSpine :=
  match phase1_surface_expect_nonterminal "generic_params" tree with
  | Some body =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact4 items with
          | Some (open_tree, first_tree, rest_tree, close_tree) =>
              match phase1_surface_expect_literal "[" open_tree,
                    phase1_surface_expect_repetition rest_tree,
                    phase1_surface_expect_literal "]" close_tree with
              | Some tt, Some rest_trees, Some tt =>
                  match phase1_surface_normalize_generic_param_spine first_tree,
                        phase1_surface_normalize_generic_param_suffixes rest_trees with
                  | Some first, Some rest =>
                      Some
                        {| phase1_generic_params_spine_first := first;
                           phase1_generic_params_spine_rest := rest |}
                  | _, _ => None
                  end
              | _, _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_generic_params_spine_round_trip :
  forall tree parameters,
    phase1_surface_normalize_generic_params_spine tree = Some parameters ->
    phase1_surface_generic_params_spine_tree parameters = tree.
Proof.
  intros tree parameters Hnormalize.
  unfold phase1_surface_normalize_generic_params_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "generic_params" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_sequence body)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact4 items)
    as [[[[open_tree first_tree] rest_tree] close_tree] |]
      eqn:Hitems; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "[" open_tree)
    as [[] |] eqn:Hopen; try discriminate Hnormalize.
  destruct (phase1_surface_expect_repetition rest_tree)
    as [rest_trees |] eqn:Hrepetition; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "]" close_tree)
    as [[] |] eqn:Hclose; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_generic_param_spine first_tree)
    as [first |] eqn:Hfirst; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_generic_param_suffixes rest_trees)
    as [rest |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst parameters.
  unfold phase1_surface_generic_params_spine_tree.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    "generic_params" tree body Hnode).
  rewrite (phase1_surface_expect_sequence_round_trip body items Hsequence).
  rewrite (phase1_surface_exact4_round_trip
    items open_tree first_tree rest_tree close_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip "[" open_tree Hopen).
  rewrite (phase1_surface_normalize_generic_param_spine_round_trip
    first_tree first Hfirst).
  rewrite (phase1_surface_expect_repetition_round_trip
    rest_tree rest_trees Hrepetition).
  rewrite (phase1_surface_normalize_generic_param_suffixes_round_trip
    rest_trees rest Hrest).
  rewrite (phase1_surface_expect_literal_round_trip "]" close_tree Hclose).
  reflexivity.
Qed.

Definition phase1_surface_optional_generic_params_tree
  (parameters : option Phase1SurfaceGenericParamsSpine) : ParseTree :=
  match parameters with
  | None => PTOptionalNone
  | Some value => PTOptionalSome (phase1_surface_generic_params_spine_tree value)
  end.

Definition phase1_surface_normalize_optional_generic_params
  (tree : ParseTree) : option (option Phase1SurfaceGenericParamsSpine) :=
  match phase1_surface_expect_optional tree with
  | Some None => Some None
  | Some (Some body) =>
      match phase1_surface_normalize_generic_params_spine body with
      | Some parameters => Some (Some parameters)
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_optional_generic_params_round_trip :
  forall tree parameters,
    phase1_surface_normalize_optional_generic_params tree = Some parameters ->
    phase1_surface_optional_generic_params_tree parameters = tree.
Proof.
  intros tree parameters Hnormalize.
  unfold phase1_surface_normalize_optional_generic_params in Hnormalize.
  destruct (phase1_surface_expect_optional tree)
    as [[body |] |] eqn:Hoptional; try discriminate Hnormalize.
  - destruct (phase1_surface_normalize_generic_params_spine body)
      as [actual |] eqn:Hparams; try discriminate Hnormalize.
    inversion Hnormalize; subst parameters.
    unfold phase1_surface_optional_generic_params_tree.
    rewrite (phase1_surface_expect_optional_round_trip
      tree (Some body) Hoptional).
    rewrite (phase1_surface_normalize_generic_params_spine_round_trip
      body actual Hparams).
    reflexivity.
  - inversion Hnormalize; subst parameters.
    unfold phase1_surface_optional_generic_params_tree.
    rewrite (phase1_surface_expect_optional_round_trip tree None Hoptional).
    reflexivity.
Qed.

Record Phase1SurfaceRecordGenericSpine : Type := {
  phase1_record_generic_spine_name : string;
  phase1_record_generic_spine_generic_params : option Phase1SurfaceGenericParamsSpine;
  phase1_record_generic_spine_mode_tree : ParseTree;
  phase1_record_generic_spine_requirements_tree : ParseTree;
  phase1_record_generic_spine_fields_tree : ParseTree
}.

Definition phase1_surface_record_generic_spine_tree
  (record : Phase1SurfaceRecordGenericSpine) : ParseTree :=
  PTNonterminal "record_decl"
    (PTSequence
      [ PTLiteral "record";
        phase1_surface_identifier_tree
          (phase1_record_generic_spine_name record);
        phase1_surface_optional_generic_params_tree
          (phase1_record_generic_spine_generic_params record);
        phase1_record_generic_spine_mode_tree record;
        phase1_record_generic_spine_requirements_tree record;
        PTLiteral "{";
        phase1_record_generic_spine_fields_tree record;
        PTLiteral "}"
      ]).

Definition phase1_surface_normalize_record_generic_spine
  (record : Phase1SurfaceRecordSpine)
  : option Phase1SurfaceRecordGenericSpine :=
  match phase1_surface_normalize_optional_generic_params
          (phase1_record_spine_generic_params_tree record) with
  | Some parameters =>
      Some
        {| phase1_record_generic_spine_name := phase1_record_spine_name record;
           phase1_record_generic_spine_generic_params := parameters;
           phase1_record_generic_spine_mode_tree := phase1_record_spine_mode_tree record;
           phase1_record_generic_spine_requirements_tree :=
             phase1_record_spine_requirements_tree record;
           phase1_record_generic_spine_fields_tree :=
             phase1_record_spine_fields_tree record |}
  | None => None
  end.

Theorem phase1_surface_normalize_record_generic_spine_round_trip :
  forall record refined,
    phase1_surface_normalize_record_generic_spine record = Some refined ->
    phase1_surface_record_generic_spine_tree refined =
      phase1_surface_record_spine_tree record.
Proof.
  intros [name generic_tree mode_tree requirements_tree fields_tree]
    refined Hnormalize.
  cbn in Hnormalize.
  destruct (phase1_surface_normalize_optional_generic_params generic_tree)
    as [parameters |] eqn:Hgeneric; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  unfold phase1_surface_record_generic_spine_tree,
    phase1_surface_record_spine_tree.
  cbn.
  rewrite (phase1_surface_normalize_optional_generic_params_round_trip
    generic_tree parameters Hgeneric).
  reflexivity.
Qed.

Definition phase1_surface_normalize_record_generic_tree
  (tree : ParseTree) : option Phase1SurfaceRecordGenericSpine :=
  match phase1_surface_normalize_record_spine tree with
  | Some record => phase1_surface_normalize_record_generic_spine record
  | None => None
  end.

Theorem phase1_surface_normalize_record_generic_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_record_generic_tree tree = Some refined ->
    phase1_surface_record_generic_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_record_generic_tree in Hnormalize.
  destruct (phase1_surface_normalize_record_spine tree)
    as [record |] eqn:Hrecord; try discriminate Hnormalize.
  transitivity (phase1_surface_record_spine_tree record).
  - eapply phase1_surface_normalize_record_generic_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_record_spine_round_trip.
    exact Hrecord.
Qed.
