From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstEffectSetRecursiveGroupingExamples
  GrammarAstGenericRequirementRecursiveGroupingExamples
  GrammarAstGenericRequirementsRecursiveGroupingSpine
  GrammarAstGenericRequirementsRecursiveGroupingSpineTotality.

Import ListNotations.
Open Scope string_scope.

(* PHIL-SURFACE-GRAMMAR-CORR-001: distinguish absent requirements,
   present-empty braces, and ordered multiple recursive-grouping entries. *)

Definition phase1_generic_requirements_grouping_empty_tree : ParseTree :=
  PTNonterminal "generic_requirements"
    (PTSequence
      [PTLiteral "requires"; PTLiteral "{"; PTRepetition []; PTLiteral "}"]).

Definition phase1_generic_requirements_grouping_two_tree : ParseTree :=
  PTNonterminal "generic_requirements"
    (PTSequence
      [PTLiteral "requires"; PTLiteral "{";
       PTRepetition
         [phase1_generic_requirement_grouping_example
           phase1_effect_set_grouping_example_reference_choice;
          phase1_generic_requirement_grouping_example
           (phase1_effect_set_grouping_example_literal_choice
             (phase1_effect_set_grouping_example_literal []))];
       PTLiteral "}"]).

Example phase1_generic_requirements_grouping_empty_is_present :
  phase1_surface_normalize_generic_requirements_recursive_grouping_tree
    phase1_generic_requirements_grouping_empty_tree =
    Some {| phase1_generic_requirements_recursive_grouping_spine_entries := [] |}.
Proof. vm_compute. reflexivity. Qed.

Example phase1_generic_requirements_grouping_optional_absent :
  phase1_surface_normalize_optional_generic_requirements_recursive_grouping_tree
    PTOptionalNone = Some None.
Proof. reflexivity. Qed.

Example phase1_generic_requirements_grouping_optional_present_empty :
  phase1_surface_normalize_optional_generic_requirements_recursive_grouping_tree
    (PTOptionalSome phase1_generic_requirements_grouping_empty_tree) =
    Some (Some
      {| phase1_generic_requirements_recursive_grouping_spine_entries := [] |}).
Proof. vm_compute. reflexivity. Qed.

Example phase1_generic_requirements_grouping_preserves_order_and_erasure :
  match phase1_surface_normalize_generic_requirements_recursive_grouping_tree
    phase1_generic_requirements_grouping_two_tree with
  | Some refined =>
      List.length (phase1_generic_requirements_recursive_grouping_spine_entries refined) = 2 /\
      phase1_surface_generic_requirements_recursive_grouping_spine_tree refined =
        phase1_generic_requirements_grouping_two_tree
  | None => False
  end.
Proof. vm_compute. split; reflexivity. Qed.

Example phase1_generic_requirements_grouping_rejects_wrong_item :
  phase1_surface_normalize_generic_requirements_recursive_grouping_tree
    (PTNonterminal "generic_requirements"
      (PTSequence
        [PTLiteral "requires"; PTLiteral "{";
         PTRepetition [PTLiteral "not a generic requirement"]; PTLiteral "}"])) =
    None.
Proof. vm_compute. reflexivity. Qed.
