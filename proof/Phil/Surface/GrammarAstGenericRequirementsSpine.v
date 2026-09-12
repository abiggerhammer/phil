From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstStructuralModeSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Shared generic-requirement correspondence for PHIL-SURFACE-GRAMMAR-CORR-001.

  The structural-mode-refined record carrier still retains generic_requirements
  as a certified ParseTree.  This layer normalizes the closed thirteen-way
  generic_requirement choice, preserves each selected payload tree exactly,
  normalizes the ordered requirement list and its optional wrapper, and then
  refines the record carrier to hold that shared normalized value.

  Nested proposition, type_expression, and effect_set_expression payloads stay
  as certified ParseTree values for their dedicated recursive correspondence
  layers.  The selected requirement shape is nevertheless validated here so
  the tag cannot be paired with a tree from a different grammar alternative.
*)

Inductive Phase1SurfaceGenericRequirementTag : Type :=
| Phase1StructuralRequirement
| Phase1PropositionRequirement
| Phase1ProviderRequirement
| Phase1CallableRequirement
| Phase1BoundaryRequirement
| Phase1ArchitectureRequirement
| Phase1EffectsRequirement
| Phase1AuthorityRequirement
| Phase1BoundaryRepresentationRequirement
| Phase1RepresentationRequirement
| Phase1PlacementRequirement
| Phase1CostRequirement
| Phase1EnvironmentRequirement.

Definition phase1_surface_generic_requirement_tag_index
  (tag : Phase1SurfaceGenericRequirementTag) : nat :=
  match tag with
  | Phase1StructuralRequirement => 0
  | Phase1PropositionRequirement => 1
  | Phase1ProviderRequirement => 2
  | Phase1CallableRequirement => 3
  | Phase1BoundaryRequirement => 4
  | Phase1ArchitectureRequirement => 5
  | Phase1EffectsRequirement => 6
  | Phase1AuthorityRequirement => 7
  | Phase1BoundaryRepresentationRequirement => 8
  | Phase1RepresentationRequirement => 9
  | Phase1PlacementRequirement => 10
  | Phase1CostRequirement => 11
  | Phase1EnvironmentRequirement => 12
  end.

Definition phase1_surface_generic_requirement_tag_of_index
  (index : nat) : option Phase1SurfaceGenericRequirementTag :=
  match index with
  | 0 => Some Phase1StructuralRequirement
  | 1 => Some Phase1PropositionRequirement
  | 2 => Some Phase1ProviderRequirement
  | 3 => Some Phase1CallableRequirement
  | 4 => Some Phase1BoundaryRequirement
  | 5 => Some Phase1ArchitectureRequirement
  | 6 => Some Phase1EffectsRequirement
  | 7 => Some Phase1AuthorityRequirement
  | 8 => Some Phase1BoundaryRepresentationRequirement
  | 9 => Some Phase1RepresentationRequirement
  | 10 => Some Phase1PlacementRequirement
  | 11 => Some Phase1CostRequirement
  | 12 => Some Phase1EnvironmentRequirement
  | _ => None
  end.

Lemma phase1_surface_generic_requirement_tag_index_round_trip :
  forall index tag,
    phase1_surface_generic_requirement_tag_of_index index = Some tag ->
    phase1_surface_generic_requirement_tag_index tag = index.
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
                                             ------ discriminate Htag.
Qed.

Definition phase1_surface_validate_named_node
  (name : string) (tree : ParseTree) : option unit :=
  match phase1_surface_expect_nonterminal name tree with
  | Some _ => Some tt
  | None => None
  end.

Definition phase1_surface_validate_structural_requirement
  (tree : ParseTree) : option unit :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact5 items with
      | Some (keyword_tree, name_tree, colon_tree, required_tree, terminator_tree) =>
          match phase1_surface_expect_literal "structural" keyword_tree,
                phase1_surface_validate_named_node "identifier" name_tree,
                phase1_surface_expect_literal ":" colon_tree,
                phase1_surface_validate_named_node "identifier" required_tree,
                phase1_surface_expect_literal ";" terminator_tree with
          | Some tt, Some tt, Some tt, Some tt, Some tt => Some tt
          | _, _, _, _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Definition phase1_surface_validate_proposition_requirement
  (keyword : string) (tree : ParseTree) : option unit :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact3 items with
      | Some (keyword_tree, proposition_tree, terminator_tree) =>
          match phase1_surface_expect_literal keyword keyword_tree,
                phase1_surface_validate_named_node "proposition" proposition_tree,
                phase1_surface_expect_literal ";" terminator_tree with
          | Some tt, Some tt, Some tt => Some tt
          | _, _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Definition phase1_surface_validate_named_type_requirement
  (keyword : string) (tree : ParseTree) : option unit :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact5 items with
      | Some (keyword_tree, name_tree, colon_tree, type_tree, terminator_tree) =>
          match phase1_surface_expect_literal keyword keyword_tree,
                phase1_surface_validate_named_node "identifier" name_tree,
                phase1_surface_expect_literal ":" colon_tree,
                phase1_surface_validate_named_node "type_expression" type_tree,
                phase1_surface_expect_literal ";" terminator_tree with
          | Some tt, Some tt, Some tt, Some tt, Some tt => Some tt
          | _, _, _, _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Definition phase1_surface_validate_effects_requirement
  (tree : ParseTree) : option unit :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact5 items with
      | Some (keyword_tree, name_tree, within_tree, effects_tree, terminator_tree) =>
          match phase1_surface_expect_literal "effects" keyword_tree,
                phase1_surface_validate_named_node "identifier" name_tree,
                phase1_surface_expect_literal "within" within_tree,
                phase1_surface_validate_named_node "effect_set_expression" effects_tree,
                phase1_surface_expect_literal ";" terminator_tree with
          | Some tt, Some tt, Some tt, Some tt, Some tt => Some tt
          | _, _, _, _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Definition phase1_surface_validate_type_only_requirement
  (keyword : string) (tree : ParseTree) : option unit :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact3 items with
      | Some (keyword_tree, type_tree, terminator_tree) =>
          match phase1_surface_expect_literal keyword keyword_tree,
                phase1_surface_validate_named_node "type_expression" type_tree,
                phase1_surface_expect_literal ";" terminator_tree with
          | Some tt, Some tt, Some tt => Some tt
          | _, _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Definition phase1_surface_validate_boundary_representation_requirement
  (tree : ParseTree) : option unit :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact4 items with
      | Some (boundary_tree, representation_tree, type_tree, terminator_tree) =>
          match phase1_surface_expect_literal "boundary" boundary_tree,
                phase1_surface_expect_literal "representation" representation_tree,
                phase1_surface_validate_named_node "type_expression" type_tree,
                phase1_surface_expect_literal ";" terminator_tree with
          | Some tt, Some tt, Some tt, Some tt => Some tt
          | _, _, _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Definition phase1_surface_validate_generic_requirement_selected
  (tag : Phase1SurfaceGenericRequirementTag)
  (tree : ParseTree) : option unit :=
  match tag with
  | Phase1StructuralRequirement =>
      phase1_surface_validate_structural_requirement tree
  | Phase1PropositionRequirement =>
      phase1_surface_validate_proposition_requirement "proposition" tree
  | Phase1ProviderRequirement =>
      phase1_surface_validate_named_type_requirement "provider" tree
  | Phase1CallableRequirement =>
      phase1_surface_validate_named_type_requirement "callable" tree
  | Phase1BoundaryRequirement =>
      phase1_surface_validate_named_type_requirement "boundary" tree
  | Phase1ArchitectureRequirement =>
      phase1_surface_validate_named_type_requirement "architecture" tree
  | Phase1EffectsRequirement =>
      phase1_surface_validate_effects_requirement tree
  | Phase1AuthorityRequirement =>
      phase1_surface_validate_type_only_requirement "authority" tree
  | Phase1BoundaryRepresentationRequirement =>
      phase1_surface_validate_boundary_representation_requirement tree
  | Phase1RepresentationRequirement =>
      phase1_surface_validate_proposition_requirement "representation" tree
  | Phase1PlacementRequirement =>
      phase1_surface_validate_proposition_requirement "placement" tree
  | Phase1CostRequirement =>
      phase1_surface_validate_proposition_requirement "cost" tree
  | Phase1EnvironmentRequirement =>
      phase1_surface_validate_proposition_requirement "environment" tree
  end.

Record Phase1SurfaceGenericRequirementSpine : Type := {
  phase1_generic_requirement_spine_tag : Phase1SurfaceGenericRequirementTag;
  phase1_generic_requirement_spine_selected_tree : ParseTree
}.

Definition phase1_surface_generic_requirement_spine_tree
  (requirement : Phase1SurfaceGenericRequirementSpine) : ParseTree :=
  PTNonterminal "generic_requirement"
    (PTAlternative
      (phase1_surface_generic_requirement_tag_index
        (phase1_generic_requirement_spine_tag requirement))
      (phase1_generic_requirement_spine_selected_tree requirement)).

Definition phase1_surface_normalize_generic_requirement_spine
  (tree : ParseTree) : option Phase1SurfaceGenericRequirementSpine :=
  match phase1_surface_expect_nonterminal "generic_requirement" tree with
  | Some body =>
      match phase1_surface_expect_alternative body with
      | Some (index, selected) =>
          match phase1_surface_generic_requirement_tag_of_index index with
          | Some tag =>
              match phase1_surface_validate_generic_requirement_selected tag selected with
              | Some tt =>
                  Some
                    {| phase1_generic_requirement_spine_tag := tag;
                       phase1_generic_requirement_spine_selected_tree := selected |}
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_generic_requirement_spine_round_trip :
  forall tree requirement,
    phase1_surface_normalize_generic_requirement_spine tree = Some requirement ->
    phase1_surface_generic_requirement_spine_tree requirement = tree.
Proof.
  intros tree requirement Hnormalize.
  unfold phase1_surface_normalize_generic_requirement_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "generic_requirement" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_alternative body)
    as [[index selected] |] eqn:Halternative; try discriminate Hnormalize.
  destruct (phase1_surface_generic_requirement_tag_of_index index)
    as [tag |] eqn:Htag; try discriminate Hnormalize.
  destruct (phase1_surface_validate_generic_requirement_selected tag selected)
    as [[] |] eqn:Hselected; try discriminate Hnormalize.
  inversion Hnormalize; subst requirement.
  unfold phase1_surface_generic_requirement_spine_tree.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    "generic_requirement" tree body Hnode).
  rewrite (phase1_surface_expect_alternative_round_trip
    body index selected Halternative).
  rewrite (phase1_surface_generic_requirement_tag_index_round_trip
    index tag Htag).
  reflexivity.
Qed.

Fixpoint phase1_surface_normalize_generic_requirement_spines
  (trees : list ParseTree) : option (list Phase1SurfaceGenericRequirementSpine) :=
  match trees with
  | [] => Some []
  | tree :: rest =>
      match phase1_surface_normalize_generic_requirement_spine tree,
            phase1_surface_normalize_generic_requirement_spines rest with
      | Some requirement, Some requirements =>
          Some (requirement :: requirements)
      | _, _ => None
      end
  end.

Theorem phase1_surface_normalize_generic_requirement_spines_round_trip :
  forall trees requirements,
    phase1_surface_normalize_generic_requirement_spines trees = Some requirements ->
    map phase1_surface_generic_requirement_spine_tree requirements = trees.
Proof.
  intros trees.
  induction trees as [|tree rest IH]; intros requirements Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst requirements.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_generic_requirement_spine tree)
      as [requirement |] eqn:Htree; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_generic_requirement_spines rest)
      as [rest_requirements |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst requirements.
    cbn.
    f_equal.
    + eapply phase1_surface_normalize_generic_requirement_spine_round_trip.
      exact Htree.
    + eapply IH.
      exact Hrest.
Qed.

Record Phase1SurfaceGenericRequirementsSpine : Type := {
  phase1_generic_requirements_spine_entries :
    list Phase1SurfaceGenericRequirementSpine
}.

Definition phase1_surface_generic_requirements_spine_tree
  (requirements : Phase1SurfaceGenericRequirementsSpine) : ParseTree :=
  PTNonterminal "generic_requirements"
    (PTSequence
      [ PTLiteral "requires";
        PTLiteral "{";
        PTRepetition
          (map phase1_surface_generic_requirement_spine_tree
            (phase1_generic_requirements_spine_entries requirements));
        PTLiteral "}"
      ]).

Definition phase1_surface_normalize_generic_requirements_spine
  (tree : ParseTree) : option Phase1SurfaceGenericRequirementsSpine :=
  match phase1_surface_expect_nonterminal "generic_requirements" tree with
  | Some body =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact4 items with
          | Some (requires_tree, open_tree, entries_tree, close_tree) =>
              match phase1_surface_expect_literal "requires" requires_tree,
                    phase1_surface_expect_literal "{" open_tree,
                    phase1_surface_expect_repetition entries_tree,
                    phase1_surface_expect_literal "}" close_tree with
              | Some tt, Some tt, Some entries, Some tt =>
                  match phase1_surface_normalize_generic_requirement_spines entries with
                  | Some requirements =>
                      Some
                        {| phase1_generic_requirements_spine_entries := requirements |}
                  | None => None
                  end
              | _, _, _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_generic_requirements_spine_round_trip :
  forall tree requirements,
    phase1_surface_normalize_generic_requirements_spine tree = Some requirements ->
    phase1_surface_generic_requirements_spine_tree requirements = tree.
Proof.
  intros tree requirements Hnormalize.
  unfold phase1_surface_normalize_generic_requirements_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "generic_requirements" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_sequence body)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact4 items)
    as [[[[requires_tree open_tree] entries_tree] close_tree] |]
      eqn:Hitems; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "requires" requires_tree)
    as [[] |] eqn:Hrequires; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "{" open_tree)
    as [[] |] eqn:Hopen; try discriminate Hnormalize.
  destruct (phase1_surface_expect_repetition entries_tree)
    as [entries |] eqn:Hentries; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "}" close_tree)
    as [[] |] eqn:Hclose; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_generic_requirement_spines entries)
    as [normalized |] eqn:Hnormalized; try discriminate Hnormalize.
  inversion Hnormalize; subst requirements.
  unfold phase1_surface_generic_requirements_spine_tree.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    "generic_requirements" tree body Hnode).
  rewrite (phase1_surface_expect_sequence_round_trip body items Hsequence).
  rewrite (phase1_surface_exact4_round_trip
    items requires_tree open_tree entries_tree close_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip
    "requires" requires_tree Hrequires).
  rewrite (phase1_surface_expect_literal_round_trip "{" open_tree Hopen).
  rewrite (phase1_surface_expect_repetition_round_trip
    entries_tree entries Hentries).
  rewrite (phase1_surface_normalize_generic_requirement_spines_round_trip
    entries normalized Hnormalized).
  rewrite (phase1_surface_expect_literal_round_trip "}" close_tree Hclose).
  reflexivity.
Qed.

Definition phase1_surface_optional_generic_requirements_tree
  (requirements : option Phase1SurfaceGenericRequirementsSpine) : ParseTree :=
  match requirements with
  | None => PTOptionalNone
  | Some value =>
      PTOptionalSome (phase1_surface_generic_requirements_spine_tree value)
  end.

Definition phase1_surface_normalize_optional_generic_requirements
  (tree : ParseTree) : option (option Phase1SurfaceGenericRequirementsSpine) :=
  match phase1_surface_expect_optional tree with
  | Some None => Some None
  | Some (Some body) =>
      match phase1_surface_normalize_generic_requirements_spine body with
      | Some requirements => Some (Some requirements)
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_optional_generic_requirements_round_trip :
  forall tree requirements,
    phase1_surface_normalize_optional_generic_requirements tree = Some requirements ->
    phase1_surface_optional_generic_requirements_tree requirements = tree.
Proof.
  intros tree requirements Hnormalize.
  unfold phase1_surface_normalize_optional_generic_requirements in Hnormalize.
  destruct (phase1_surface_expect_optional tree)
    as [[body |] |] eqn:Hoptional; try discriminate Hnormalize.
  - destruct (phase1_surface_normalize_generic_requirements_spine body)
      as [actual |] eqn:Hrequirements; try discriminate Hnormalize.
    inversion Hnormalize; subst requirements.
    unfold phase1_surface_optional_generic_requirements_tree.
    rewrite (phase1_surface_expect_optional_round_trip
      tree (Some body) Hoptional).
    rewrite (phase1_surface_normalize_generic_requirements_spine_round_trip
      body actual Hrequirements).
    reflexivity.
  - inversion Hnormalize; subst requirements.
    unfold phase1_surface_optional_generic_requirements_tree.
    rewrite (phase1_surface_expect_optional_round_trip tree None Hoptional).
    reflexivity.
Qed.

Record Phase1SurfaceRecordRequirementsSpine : Type := {
  phase1_record_requirements_spine_name : string;
  phase1_record_requirements_spine_generic_params : option Phase1SurfaceGenericParamsSpine;
  phase1_record_requirements_spine_mode : option Phase1SurfaceStructuralMode;
  phase1_record_requirements_spine_requirements : option Phase1SurfaceGenericRequirementsSpine;
  phase1_record_requirements_spine_fields_tree : ParseTree
}.

Definition phase1_surface_record_requirements_spine_tree
  (record : Phase1SurfaceRecordRequirementsSpine) : ParseTree :=
  PTNonterminal "record_decl"
    (PTSequence
      [ PTLiteral "record";
        phase1_surface_identifier_tree
          (phase1_record_requirements_spine_name record);
        phase1_surface_optional_generic_params_tree
          (phase1_record_requirements_spine_generic_params record);
        phase1_surface_optional_mode_tree
          (phase1_record_requirements_spine_mode record);
        phase1_surface_optional_generic_requirements_tree
          (phase1_record_requirements_spine_requirements record);
        PTLiteral "{";
        phase1_record_requirements_spine_fields_tree record;
        PTLiteral "}"
      ]).

Definition phase1_surface_normalize_record_requirements_spine
  (record : Phase1SurfaceRecordModeSpine)
  : option Phase1SurfaceRecordRequirementsSpine :=
  match phase1_surface_normalize_optional_generic_requirements
          (phase1_record_mode_spine_requirements_tree record) with
  | Some requirements =>
      Some
        {| phase1_record_requirements_spine_name :=
             phase1_record_mode_spine_name record;
           phase1_record_requirements_spine_generic_params :=
             phase1_record_mode_spine_generic_params record;
           phase1_record_requirements_spine_mode :=
             phase1_record_mode_spine_mode record;
           phase1_record_requirements_spine_requirements := requirements;
           phase1_record_requirements_spine_fields_tree :=
             phase1_record_mode_spine_fields_tree record |}
  | None => None
  end.

Theorem phase1_surface_normalize_record_requirements_spine_round_trip :
  forall record refined,
    phase1_surface_normalize_record_requirements_spine record = Some refined ->
    phase1_surface_record_requirements_spine_tree refined =
      phase1_surface_record_mode_spine_tree record.
Proof.
  intros [name generic_params mode requirements_tree fields_tree]
    refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_optional_generic_requirements requirements_tree)
    as [requirements |] eqn:Hrequirements; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  unfold phase1_surface_record_requirements_spine_tree,
    phase1_surface_record_mode_spine_tree.
  cbn.
  rewrite (phase1_surface_normalize_optional_generic_requirements_round_trip
    requirements_tree requirements Hrequirements).
  reflexivity.
Qed.

Definition phase1_surface_normalize_record_requirements_tree
  (tree : ParseTree) : option Phase1SurfaceRecordRequirementsSpine :=
  match phase1_surface_normalize_record_mode_tree tree with
  | Some record => phase1_surface_normalize_record_requirements_spine record
  | None => None
  end.

Theorem phase1_surface_normalize_record_requirements_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_record_requirements_tree tree = Some refined ->
    phase1_surface_record_requirements_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_record_requirements_tree in Hnormalize.
  destruct (phase1_surface_normalize_record_mode_tree tree)
    as [record |] eqn:Hrecord; try discriminate Hnormalize.
  transitivity (phase1_surface_record_mode_spine_tree record).
  - eapply phase1_surface_normalize_record_requirements_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_record_mode_tree_round_trip.
    exact Hrecord.
Qed.
