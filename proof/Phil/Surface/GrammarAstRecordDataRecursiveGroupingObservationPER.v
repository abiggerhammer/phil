From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingImplementationRepresentation
  GrammarAstRecordDataRecursiveGroupingTaggedAdmission
  GrammarAstRecordDataRecursiveGroupingProductionObservables
  GrammarAstRecordDataRecursiveGroupingObservationSeparation.

Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: observations induce a partial
  equivalence relation on admitted public Record/Data tag+tree keys.
  This is explicitly partial: a failed admission is not related even to
  itself. It is strictly coarser than exact-key equality, and preserves
  declaration family but not every source distinction.

  The relatedness witness carries BOTH successful admissions, so no
  malformed public intermediate can be certified by a bare projection.
  This is proof-side only, not production Haskell AST binding, G2/G4,
  or Phase 1 closure. No grammar or trusted-definition changes.
*)

Definition phase1_surface_recursive_grouping_observation_related
  (left right : Phase1SurfaceDeclarationSpine) : Prop :=
  exists left_refined right_refined,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      left = Some left_refined /\
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      right = Some right_refined /\
    phase1_surface_observe_recursive_grouping_record_data left_refined =
      phase1_surface_observe_recursive_grouping_record_data right_refined.

Theorem phase1_surface_recursive_grouping_observation_related_reflexive_on_admission :
  forall declaration refined,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      declaration = Some refined ->
    phase1_surface_recursive_grouping_observation_related
      declaration declaration.
Proof.
  intros declaration refined Hadmit.
  exists refined, refined.
  repeat split; [exact Hadmit | exact Hadmit | reflexivity].
Qed.

Theorem phase1_surface_recursive_grouping_observation_related_symmetric :
  forall left right,
    phase1_surface_recursive_grouping_observation_related left right ->
    phase1_surface_recursive_grouping_observation_related right left.
Proof.
  intros left right
    [left_refined [right_refined [Hleft [Hright Hobserved]]]].
  exists right_refined, left_refined.
  repeat split; [exact Hright | exact Hleft |].
  symmetry.
  exact Hobserved.
Qed.

Theorem phase1_surface_recursive_grouping_observation_related_transitive :
  forall left middle right,
    phase1_surface_recursive_grouping_observation_related left middle ->
    phase1_surface_recursive_grouping_observation_related middle right ->
    phase1_surface_recursive_grouping_observation_related left right.
Proof.
  intros left middle right
    [left_refined [middle_refined [Hleft [Hmiddle Hlm]]]]
    [middle_refined' [right_refined [Hmiddle' [Hright Hmr]]]].
  rewrite Hmiddle in Hmiddle'.
  inversion Hmiddle'; subst middle_refined'.
  exists left_refined, right_refined.
  repeat split; [exact Hleft | exact Hright |].
  etransitivity; eassumption.
Qed.

Theorem phase1_surface_recursive_grouping_observation_related_preserves_tag :
  forall left right,
    phase1_surface_recursive_grouping_observation_related left right ->
    phase1_declaration_spine_tag left = phase1_declaration_spine_tag right.
Proof.
  intros left right
    [left_refined [right_refined [Hleft [Hright Hobserved]]]].
  eapply phase1_surface_admitted_observation_equality_preserves_tag;
    eassumption.
Qed.

Theorem phase1_surface_recursive_grouping_observation_related_not_exact_key_equality :
  exists left right,
    phase1_surface_recursive_grouping_observation_related left right /\
    left <> right.
Proof.
  destruct phase1_surface_admitted_observation_collides_on_distinct_exact_keys
    as [left_refined [right_refined
      [Hleft [Hright [Hobserved Hkeys]]]]].
  exists
    (phase1_surface_recursive_grouping_implementation_declaration_spine
      left_refined),
    (phase1_surface_recursive_grouping_implementation_declaration_spine
      right_refined).
  split.
  - exists left_refined, right_refined.
    repeat split; assumption.
  - exact Hkeys.
Qed.

Example phase1_surface_recursive_grouping_observation_malformed_reflexivity_rejected :
  forall declaration,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      declaration = None ->
    ~ phase1_surface_recursive_grouping_observation_related
        declaration declaration.
Proof.
  intros declaration Hreject
    [left_refined [right_refined [Hleft _]]].
  rewrite Hreject in Hleft.
  discriminate Hleft.
Qed.
