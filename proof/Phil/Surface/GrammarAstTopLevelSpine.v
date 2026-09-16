From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSourceHeader
  GrammarAstSourceSpine
  GrammarParserProductionKernel.

Import ListNotations.
Open Scope string_scope.

(*
  Third universal proof-side AST correspondence carrier for
  PHIL-SURFACE-GRAMMAR-CORR-001.

  The source-header layer normalizes module/import structure and retains each
  top_level_decl as an opaque ParseTree.  This layer descends one grammar level:
  attributes become exact semantic name/value pairs and declaration choice
  becomes a closed fifteen-way tag while the selected declaration payload tree
  remains opaque for declaration-family-specific successor slices.
*)

Inductive Phase1SurfaceDeclarationTag : Type :=
| Phase1RecordDeclaration
| Phase1DataDeclaration
| Phase1TypeAliasDeclaration
| Phase1ClaimDeclaration
| Phase1CallableContractDeclaration
| Phase1FunctionDeclaration
| Phase1ProviderContractDeclaration
| Phase1ProviderImplementationDeclaration
| Phase1OpaqueProviderImplementationDeclaration
| Phase1ProtocolDeclaration
| Phase1CapabilityDeclaration
| Phase1BoundaryDeclaration
| Phase1ArchitectureDeclaration
| Phase1ComponentDeclaration
| Phase1ProgramDeclaration.

Definition phase1_surface_declaration_tag_index
  (tag : Phase1SurfaceDeclarationTag) : nat :=
  match tag with
  | Phase1RecordDeclaration => 0
  | Phase1DataDeclaration => 1
  | Phase1TypeAliasDeclaration => 2
  | Phase1ClaimDeclaration => 3
  | Phase1CallableContractDeclaration => 4
  | Phase1FunctionDeclaration => 5
  | Phase1ProviderContractDeclaration => 6
  | Phase1ProviderImplementationDeclaration => 7
  | Phase1OpaqueProviderImplementationDeclaration => 8
  | Phase1ProtocolDeclaration => 9
  | Phase1CapabilityDeclaration => 10
  | Phase1BoundaryDeclaration => 11
  | Phase1ArchitectureDeclaration => 12
  | Phase1ComponentDeclaration => 13
  | Phase1ProgramDeclaration => 14
  end.

Definition phase1_surface_declaration_tag_name
  (tag : Phase1SurfaceDeclarationTag) : string :=
  match tag with
  | Phase1RecordDeclaration => "record_decl"
  | Phase1DataDeclaration => "data_decl"
  | Phase1TypeAliasDeclaration => "type_alias_decl"
  | Phase1ClaimDeclaration => "claim_decl"
  | Phase1CallableContractDeclaration => "callable_contract_decl"
  | Phase1FunctionDeclaration => "function_decl"
  | Phase1ProviderContractDeclaration => "provider_contract_decl"
  | Phase1ProviderImplementationDeclaration => "provider_implementation_decl"
  | Phase1OpaqueProviderImplementationDeclaration =>
      "opaque_provider_implementation_decl"
  | Phase1ProtocolDeclaration => "protocol_decl"
  | Phase1CapabilityDeclaration => "capability_decl"
  | Phase1BoundaryDeclaration => "boundary_decl"
  | Phase1ArchitectureDeclaration => "architecture_decl"
  | Phase1ComponentDeclaration => "component_decl"
  | Phase1ProgramDeclaration => "program_decl"
  end.

Definition phase1_surface_declaration_tag_of_index
  (index : nat) : option Phase1SurfaceDeclarationTag :=
  match index with
  | 0 => Some Phase1RecordDeclaration
  | 1 => Some Phase1DataDeclaration
  | 2 => Some Phase1TypeAliasDeclaration
  | 3 => Some Phase1ClaimDeclaration
  | 4 => Some Phase1CallableContractDeclaration
  | 5 => Some Phase1FunctionDeclaration
  | 6 => Some Phase1ProviderContractDeclaration
  | 7 => Some Phase1ProviderImplementationDeclaration
  | 8 => Some Phase1OpaqueProviderImplementationDeclaration
  | 9 => Some Phase1ProtocolDeclaration
  | 10 => Some Phase1CapabilityDeclaration
  | 11 => Some Phase1BoundaryDeclaration
  | 12 => Some Phase1ArchitectureDeclaration
  | 13 => Some Phase1ComponentDeclaration
  | 14 => Some Phase1ProgramDeclaration
  | _ => None
  end.

Lemma phase1_surface_declaration_tag_index_round_trip :
  forall index tag,
    phase1_surface_declaration_tag_of_index index = Some tag ->
    phase1_surface_declaration_tag_index tag = index.
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
                         *** destruct index as [|index]; cbn in Htag.
                             ---- inversion Htag; reflexivity.
                             ---- destruct index as [|index]; cbn in Htag.
                                  ++++ inversion Htag; reflexivity.
                                  ++++ destruct index as [|index]; cbn in Htag.
                                       ***** inversion Htag; reflexivity.
                                       ***** destruct index as [|index]; cbn in Htag.
                                             ------ inversion Htag; reflexivity.
                                             ------ destruct index as [|index]; cbn in Htag.
                                                    ++++++ inversion Htag; reflexivity.
                                                    ++++++ destruct index as [|index]; cbn in Htag.
                                                           ******* inversion Htag; reflexivity.
                                                           ******* discriminate Htag.
Qed.

Definition phase1_surface_expect_alternative
  (tree : ParseTree) : option (nat * ParseTree) :=
  match tree with
  | PTAlternative index branch => Some (index, branch)
  | _ => None
  end.

Lemma phase1_surface_expect_alternative_round_trip :
  forall tree index branch,
    phase1_surface_expect_alternative tree = Some (index, branch) ->
    tree = PTAlternative index branch.
Proof.
  intros tree index branch Hexpect.
  destruct tree;
    cbn in Hexpect; try discriminate Hexpect.
  inversion Hexpect; subst.
  reflexivity.
Qed.

Definition phase1_surface_exact5 {A : Type}
  (items : list A) : option (A * A * A * A * A) :=
  match items with
  | [a; b; c; d; e] => Some (a, b, c, d, e)
  | _ => None
  end.

Lemma phase1_surface_exact5_round_trip {A : Type} :
  forall (items : list A) (a b c d e : A),
    phase1_surface_exact5 items = Some (a, b, c, d, e) ->
    items = [a; b; c; d; e].
Proof.
  intros items a b c d e Hitems.
  destruct items as [|v vs]; cbn in Hitems; try discriminate Hitems.
  destruct vs as [|w ws]; cbn in Hitems; try discriminate Hitems.
  destruct ws as [|x xs]; cbn in Hitems; try discriminate Hitems.
  destruct xs as [|y ys]; cbn in Hitems; try discriminate Hitems.
  destruct ys as [|z zs]; cbn in Hitems; try discriminate Hitems.
  destruct zs as [|extra rest]; cbn in Hitems; try discriminate Hitems.
  inversion Hitems; subst.
  reflexivity.
Qed.

Record Phase1SurfaceAttributeSpine : Type := {
  phase1_attribute_spine_name : string;
  phase1_attribute_spine_value : string
}.

Record Phase1SurfaceDeclarationSpine : Type := {
  phase1_declaration_spine_tag : Phase1SurfaceDeclarationTag;
  phase1_declaration_spine_selected_tree : ParseTree
}.

Record Phase1SurfaceTopLevelSpine : Type := {
  phase1_top_level_spine_attributes : list Phase1SurfaceAttributeSpine;
  phase1_top_level_spine_declaration : Phase1SurfaceDeclarationSpine
}.

Record Phase1SurfaceSourceTopLevel : Type := {
  phase1_source_top_level_module : option Phase1SurfaceNameList;
  phase1_source_top_level_imports : list Phase1SurfaceImportHeader;
  phase1_source_top_level_declarations : list Phase1SurfaceTopLevelSpine
}.

Definition phase1_surface_metadata_string_tree
  (value : string) : ParseTree :=
  PTNonterminal "metadata_string_literal"
    (PTLexical "STRING_LITERAL" value).

Definition phase1_surface_normalize_metadata_string
  (tree : ParseTree) : option string :=
  match phase1_surface_expect_nonterminal "metadata_string_literal" tree with
  | Some body => phase1_surface_expect_lexical "STRING_LITERAL" body
  | None => None
  end.

Lemma phase1_surface_normalize_metadata_string_round_trip :
  forall tree value,
    phase1_surface_normalize_metadata_string tree = Some value ->
    phase1_surface_metadata_string_tree value = tree.
Proof.
  intros tree value Hnormalize.
  unfold phase1_surface_normalize_metadata_string in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "metadata_string_literal" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_lexical "STRING_LITERAL" body)
    as [actual |] eqn:Hlex; try discriminate Hnormalize.
  inversion Hnormalize; subst actual.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    "metadata_string_literal" tree body Hnode).
  rewrite (phase1_surface_expect_lexical_round_trip
    "STRING_LITERAL" body value Hlex).
  reflexivity.
Qed.

Definition phase1_surface_attribute_spine_tree
  (attribute : Phase1SurfaceAttributeSpine) : ParseTree :=
  PTNonterminal "attribute"
    (PTSequence
      [ PTLiteral "@";
        phase1_surface_identifier_tree
          (phase1_attribute_spine_name attribute);
        PTLiteral "(";
        phase1_surface_metadata_string_tree
          (phase1_attribute_spine_value attribute);
        PTLiteral ")"
      ]).

Definition phase1_surface_normalize_attribute_spine
  (tree : ParseTree) : option Phase1SurfaceAttributeSpine :=
  match phase1_surface_expect_nonterminal "attribute" tree with
  | Some body =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact5 items with
          | Some (at_tree, name_tree, open_tree, value_tree, close_tree) =>
              match phase1_surface_expect_literal "@" at_tree,
                    phase1_surface_expect_literal "(" open_tree,
                    phase1_surface_expect_literal ")" close_tree with
              | Some tt, Some tt, Some tt =>
                  match phase1_surface_normalize_identifier name_tree,
                        phase1_surface_normalize_metadata_string value_tree with
                  | Some name, Some value =>
                      Some
                        {| phase1_attribute_spine_name := name;
                           phase1_attribute_spine_value := value |}
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

Lemma phase1_surface_normalize_attribute_spine_round_trip :
  forall tree attribute,
    phase1_surface_normalize_attribute_spine tree = Some attribute ->
    phase1_surface_attribute_spine_tree attribute = tree.
Proof.
  intros tree attribute Hnormalize.
  unfold phase1_surface_normalize_attribute_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "attribute" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_sequence body)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact5 items)
    as [[[[[at_tree name_tree] open_tree] value_tree] close_tree] |]
      eqn:Hitems; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "@" at_tree)
    as [[] |] eqn:Hat; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "(" open_tree)
    as [[] |] eqn:Hopen; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal ")" close_tree)
    as [[] |] eqn:Hclose; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_identifier name_tree)
    as [name |] eqn:Hname; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_metadata_string value_tree)
    as [value |] eqn:Hvalue; try discriminate Hnormalize.
  inversion Hnormalize; subst attribute.
  unfold phase1_surface_attribute_spine_tree.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    "attribute" tree body Hnode).
  rewrite (phase1_surface_expect_sequence_round_trip body items Hsequence).
  rewrite (phase1_surface_exact5_round_trip
    items at_tree name_tree open_tree value_tree close_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip "@" at_tree Hat).
  rewrite <- (phase1_surface_normalize_identifier_round_trip
    name_tree name Hname).
  rewrite (phase1_surface_expect_literal_round_trip "(" open_tree Hopen).
  rewrite <- (phase1_surface_normalize_metadata_string_round_trip
    value_tree value Hvalue).
  rewrite (phase1_surface_expect_literal_round_trip ")" close_tree Hclose).
  reflexivity.
Qed.

Fixpoint phase1_surface_normalize_attribute_spines
  (trees : list ParseTree) : option (list Phase1SurfaceAttributeSpine) :=
  match trees with
  | [] => Some []
  | tree :: rest =>
      match phase1_surface_normalize_attribute_spine tree,
            phase1_surface_normalize_attribute_spines rest with
      | Some attribute, Some attributes => Some (attribute :: attributes)
      | _, _ => None
      end
  end.

Lemma phase1_surface_normalize_attribute_spines_round_trip :
  forall trees attributes,
    phase1_surface_normalize_attribute_spines trees = Some attributes ->
    map phase1_surface_attribute_spine_tree attributes = trees.
Proof.
  intros trees.
  induction trees as [|tree rest IH]; intros attributes Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_attribute_spine tree)
      as [attribute |] eqn:Htree; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_attribute_spines rest)
      as [rest_attributes |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst.
    cbn.
    f_equal.
    + eapply phase1_surface_normalize_attribute_spine_round_trip.
      exact Htree.
    + eapply IH.
      reflexivity.
Qed.

Definition phase1_surface_declaration_spine_tree
  (declaration : Phase1SurfaceDeclarationSpine) : ParseTree :=
  PTNonterminal "declaration"
    (PTAlternative
      (phase1_surface_declaration_tag_index
        (phase1_declaration_spine_tag declaration))
      (phase1_declaration_spine_selected_tree declaration)).

Definition phase1_surface_normalize_declaration_spine
  (tree : ParseTree) : option Phase1SurfaceDeclarationSpine :=
  match phase1_surface_expect_nonterminal "declaration" tree with
  | Some body =>
      match phase1_surface_expect_alternative body with
      | Some (index, selected) =>
          match phase1_surface_declaration_tag_of_index index with
          | Some tag =>
              match phase1_surface_expect_nonterminal
                      (phase1_surface_declaration_tag_name tag)
                      selected with
              | Some _ =>
                  Some
                    {| phase1_declaration_spine_tag := tag;
                       phase1_declaration_spine_selected_tree := selected |}
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Lemma phase1_surface_normalize_declaration_spine_round_trip :
  forall tree declaration,
    phase1_surface_normalize_declaration_spine tree = Some declaration ->
    phase1_surface_declaration_spine_tree declaration = tree.
Proof.
  intros tree declaration Hnormalize.
  unfold phase1_surface_normalize_declaration_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "declaration" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_alternative body)
    as [[index selected] |] eqn:Halternative; try discriminate Hnormalize.
  destruct (phase1_surface_declaration_tag_of_index index)
    as [tag |] eqn:Htag; try discriminate Hnormalize.
  destruct (phase1_surface_expect_nonterminal
    (phase1_surface_declaration_tag_name tag) selected)
    as [selected_body |] eqn:Hselected; try discriminate Hnormalize.
  inversion Hnormalize; subst declaration.
  unfold phase1_surface_declaration_spine_tree.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    "declaration" tree body Hnode).
  rewrite (phase1_surface_expect_alternative_round_trip
    body index selected Halternative).
  rewrite <- (phase1_surface_declaration_tag_index_round_trip
    index tag Htag).
  reflexivity.
Qed.

Definition phase1_surface_top_level_spine_tree
  (top_level : Phase1SurfaceTopLevelSpine) : ParseTree :=
  PTNonterminal "top_level_decl"
    (PTSequence
      [ PTRepetition
          (map phase1_surface_attribute_spine_tree
            (phase1_top_level_spine_attributes top_level));
        phase1_surface_declaration_spine_tree
          (phase1_top_level_spine_declaration top_level)
      ]).

Definition phase1_surface_normalize_top_level_spine
  (tree : ParseTree) : option Phase1SurfaceTopLevelSpine :=
  match phase1_surface_expect_nonterminal "top_level_decl" tree with
  | Some body =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact2 items with
          | Some (attribute_tree, declaration_tree) =>
              match phase1_surface_expect_repetition attribute_tree with
              | Some attribute_trees =>
                  match phase1_surface_normalize_attribute_spines attribute_trees,
                        phase1_surface_normalize_declaration_spine declaration_tree with
                  | Some attributes, Some declaration =>
                      Some
                        {| phase1_top_level_spine_attributes := attributes;
                           phase1_top_level_spine_declaration := declaration |}
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

Lemma phase1_surface_normalize_top_level_spine_round_trip :
  forall tree top_level,
    phase1_surface_normalize_top_level_spine tree = Some top_level ->
    phase1_surface_top_level_spine_tree top_level = tree.
Proof.
  intros tree top_level Hnormalize.
  unfold phase1_surface_normalize_top_level_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "top_level_decl" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_sequence body)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items)
    as [[attribute_tree declaration_tree] |] eqn:Hitems;
    try discriminate Hnormalize.
  destruct (phase1_surface_expect_repetition attribute_tree)
    as [attribute_trees |] eqn:Hrepetition; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_attribute_spines attribute_trees)
    as [attributes |] eqn:Hattributes; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_declaration_spine declaration_tree)
    as [declaration |] eqn:Hdeclaration; try discriminate Hnormalize.
  inversion Hnormalize; subst top_level.
  unfold phase1_surface_top_level_spine_tree.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    "top_level_decl" tree body Hnode).
  rewrite (phase1_surface_expect_sequence_round_trip body items Hsequence).
  rewrite (phase1_surface_exact2_round_trip
    items attribute_tree declaration_tree Hitems).
  rewrite (phase1_surface_expect_repetition_round_trip
    attribute_tree attribute_trees Hrepetition).
  rewrite <- (phase1_surface_normalize_attribute_spines_round_trip
    attribute_trees attributes Hattributes).
  rewrite <- (phase1_surface_normalize_declaration_spine_round_trip
    declaration_tree declaration Hdeclaration).
  reflexivity.
Qed.

Fixpoint phase1_surface_normalize_top_level_spines
  (trees : list ParseTree) : option (list Phase1SurfaceTopLevelSpine) :=
  match trees with
  | [] => Some []
  | tree :: rest =>
      match phase1_surface_normalize_top_level_spine tree,
            phase1_surface_normalize_top_level_spines rest with
      | Some top_level, Some top_levels => Some (top_level :: top_levels)
      | _, _ => None
      end
  end.

Lemma phase1_surface_normalize_top_level_spines_round_trip :
  forall trees top_levels,
    phase1_surface_normalize_top_level_spines trees = Some top_levels ->
    map phase1_surface_top_level_spine_tree top_levels = trees.
Proof.
  intros trees.
  induction trees as [|tree rest IH]; intros top_levels Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_top_level_spine tree)
      as [top_level |] eqn:Htree; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_top_level_spines rest)
      as [rest_top_levels |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst.
    cbn.
    f_equal.
    + eapply phase1_surface_normalize_top_level_spine_round_trip.
      exact Htree.
    + eapply IH.
      reflexivity.
Qed.

Definition phase1_surface_source_top_level_tree
  (source : Phase1SurfaceSourceTopLevel) : ParseTree :=
  PTNonterminal phase1_surface_start
    (PTSequence
      [ match phase1_source_top_level_module source with
        | None => PTOptionalNone
        | Some name => PTOptionalSome (phase1_surface_module_decl_tree name)
        end;
        PTRepetition
          (map phase1_surface_import_decl_tree
            (phase1_source_top_level_imports source));
        PTRepetition
          (map phase1_surface_top_level_spine_tree
            (phase1_source_top_level_declarations source))
      ]).

Definition phase1_surface_normalize_source_top_level
  (header : Phase1SurfaceSourceHeader) : option Phase1SurfaceSourceTopLevel :=
  match phase1_surface_normalize_top_level_spines
          (phase1_source_header_top_levels header) with
  | Some top_levels =>
      Some
        {| phase1_source_top_level_module :=
             phase1_source_header_module header;
           phase1_source_top_level_imports :=
             phase1_source_header_imports header;
           phase1_source_top_level_declarations := top_levels |}
  | None => None
  end.

Theorem phase1_surface_normalize_source_top_level_round_trip :
  forall header source,
    phase1_surface_normalize_source_top_level header = Some source ->
    phase1_surface_source_top_level_tree source =
      phase1_surface_source_header_tree header.
Proof.
  intros header source Hnormalize.
  destruct header as [module_name import_headers top_level_trees].
  unfold phase1_surface_normalize_source_top_level in Hnormalize.
  cbn in Hnormalize.
  destruct (phase1_surface_normalize_top_level_spines top_level_trees)
    as [top_levels |] eqn:Htop_levels; try discriminate Hnormalize.
  inversion Hnormalize; subst source.
  cbn.
  rewrite <- (phase1_surface_normalize_top_level_spines_round_trip
    top_level_trees top_levels Htop_levels).
  reflexivity.
Qed.

Definition phase1_surface_normalize_source_top_level_tree
  (tree : ParseTree) : option Phase1SurfaceSourceTopLevel :=
  match phase1_surface_normalize_source_header_tree tree with
  | Some header => phase1_surface_normalize_source_top_level header
  | None => None
  end.

Theorem phase1_surface_normalize_source_top_level_tree_round_trip :
  forall tree source,
    phase1_surface_normalize_source_top_level_tree tree = Some source ->
    phase1_surface_source_top_level_tree source = tree.
Proof.
  intros tree source Hnormalize.
  unfold phase1_surface_normalize_source_top_level_tree in Hnormalize.
  destruct (phase1_surface_normalize_source_header_tree tree)
    as [header |] eqn:Hheader; try discriminate Hnormalize.
  transitivity (phase1_surface_source_header_tree header).
  - eapply phase1_surface_normalize_source_top_level_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_source_header_tree_round_trip.
    exact Hheader.
Qed.

Definition phase1_surface_reference_source_top_level
  (tokens : list ConcreteToken) : option Phase1SurfaceSourceTopLevel :=
  match phase1_surface_reference_parse tokens with
  | Some ([], ResultTree tree) =>
      phase1_surface_normalize_source_top_level_tree tree
  | _ => None
  end.

Theorem phase1_surface_reference_source_top_level_sound :
  forall tokens source,
    phase1_surface_reference_source_top_level tokens = Some source ->
    exists tree,
      phase1_surface_reference_parse tokens = Some ([], ResultTree tree) /\
      phase1_surface_source_top_level_tree source = tree /\
      Phase1CompleteDerivation tokens tree.
Proof.
  intros tokens source Hnormalize.
  unfold phase1_surface_reference_source_top_level in Hnormalize.
  destruct (phase1_surface_reference_parse tokens)
    as [[rest result] |] eqn:Hparse; try discriminate Hnormalize.
  destruct rest as [|token rest]; try discriminate Hnormalize.
  destruct result as [tree | trees]; try discriminate Hnormalize.
  exists tree.
  split.
  - reflexivity.
  - split.
    + eapply phase1_surface_normalize_source_top_level_tree_round_trip.
      exact Hnormalize.
    + unfold phase1_surface_reference_parse in Hparse.
      eapply phase1_surface_predictive_parse_fuel_ordinary_sound.
      exact Hparse.
Qed.
