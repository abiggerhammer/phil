From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingImplementationRepresentation
  GrammarAstRecordDataRecursiveGroupingTaggedAdmission
  GrammarAstRecordDataRecursiveGroupingProductionObservables
  GrammarAstRecordDataRecursiveGroupingDerivedObservables
  GrammarAstRecordDataRecursiveGroupingObservationPER
  GrammarAstRecordDataRecursiveGroupingObservationAdmittedQuotient.

Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: connect canonical Grammar-v1
  Record/Data derivations and successful public admission to actual
  certified representatives of observation equivalence classes.
  Certificates cannot fabricate an admission, and distinct declaration
  families cannot become equivalent. Observations remain lossy:
  equality here does not imply exact tag/tree-key equality.
  Proof-side only: no production AST binding, G2/G4, added trust,
  Grammar-v1 changes, or Phase 1 closure.
*)

Theorem phase1_surface_admitted_observation_representative_iff_success :
  forall key,
    (exists entry : Phase1SurfaceAdmittedObservationKey,
      phase1_admitted_observation_key entry = key) <->
    (exists refined,
      phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
        key = Some refined).
Proof.
  intro key.
  split.
  - intros [entry Hkey].
    exists (phase1_admitted_observation_refined entry).
    rewrite <- Hkey.
    exact (phase1_admitted_observation_certificate entry).
  - intros [refined Hnormalize].
    exists
      {| phase1_admitted_observation_key := key;
         phase1_admitted_observation_refined := refined;
         phase1_admitted_observation_certificate := Hnormalize |}.
    reflexivity.
Qed.

Theorem phase1_surface_admitted_observation_same_key_equiv :
  forall left right : Phase1SurfaceAdmittedObservationKey,
    phase1_admitted_observation_key left =
      phase1_admitted_observation_key right ->
    phase1_surface_admitted_observation_equiv left right.
Proof.
  intros left right Hsame.
  pose proof (phase1_admitted_observation_certificate left) as Hleft.
  pose proof (phase1_admitted_observation_certificate right) as Hright.
  rewrite Hsame in Hleft.
  rewrite Hright in Hleft.
  injection Hleft as Heq.
  unfold phase1_surface_admitted_observation_equiv,
    phase1_surface_admitted_observation.
  now rewrite Heq.
Qed.

Theorem phase1_surface_public_related_has_admitted_observation_representatives :
  forall left right,
    phase1_surface_recursive_grouping_observation_related left right ->
    exists left_entry right_entry : Phase1SurfaceAdmittedObservationKey,
      phase1_admitted_observation_key left_entry = left /\
      phase1_admitted_observation_key right_entry = right /\
      phase1_surface_admitted_observation_equiv left_entry right_entry.
Proof.
  intros left right
    [left_refined [right_refined [Hleft [Hright Hobserved]]]].
  exists
    {| phase1_admitted_observation_key := left;
       phase1_admitted_observation_refined := left_refined;
       phase1_admitted_observation_certificate := Hleft |},
    {| phase1_admitted_observation_key := right;
       phase1_admitted_observation_refined := right_refined;
       phase1_admitted_observation_certificate := Hright |}.
  split; [reflexivity |].
  split; [reflexivity |].
  exact Hobserved.
Qed.

Theorem phase1_surface_derived_record_has_admitted_equivalence_representative :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "record_decl")
      input rest tree ->
    exists entry : Phase1SurfaceAdmittedObservationKey,
      phase1_admitted_observation_key entry =
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := tree |} /\
      phase1_surface_recursive_grouping_observed_tag
        (phase1_surface_admitted_observation entry) =
        Phase1RecordDeclaration.
Proof.
  intros path input rest tree Hderive.
  destruct (phase1_surface_derived_record_has_admitted_observation
    path input rest tree Hderive)
    as [refined [observed [Hnormalize [Hobserved [Htag _]]]]].
  exists
    {| phase1_admitted_observation_key :=
         {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
            phase1_declaration_spine_selected_tree := tree |};
       phase1_admitted_observation_refined := refined;
       phase1_admitted_observation_certificate := Hnormalize |}.
  split; [reflexivity |].
  unfold phase1_surface_admitted_observation.
  simpl.
  rewrite <- Hobserved.
  exact Htag.
Qed.

Theorem phase1_surface_derived_data_has_admitted_equivalence_representative :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "data_decl")
      input rest tree ->
    exists entry : Phase1SurfaceAdmittedObservationKey,
      phase1_admitted_observation_key entry =
        {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := tree |} /\
      phase1_surface_recursive_grouping_observed_tag
        (phase1_surface_admitted_observation entry) =
        Phase1DataDeclaration.
Proof.
  intros path input rest tree Hderive.
  destruct (phase1_surface_derived_data_has_admitted_observation
    path input rest tree Hderive)
    as [refined [observed [Hnormalize [Hobserved [Htag _]]]]].
  exists
    {| phase1_admitted_observation_key :=
         {| phase1_declaration_spine_tag := Phase1DataDeclaration;
            phase1_declaration_spine_selected_tree := tree |};
       phase1_admitted_observation_refined := refined;
       phase1_admitted_observation_certificate := Hnormalize |}.
  split; [reflexivity |].
  unfold phase1_surface_admitted_observation.
  simpl.
  rewrite <- Hobserved.
  exact Htag.
Qed.

Theorem phase1_surface_admitted_record_data_equivalence_classes_disjoint :
  forall left right : Phase1SurfaceAdmittedObservationKey,
    phase1_declaration_spine_tag
      (phase1_admitted_observation_key left) = Phase1RecordDeclaration ->
    phase1_declaration_spine_tag
      (phase1_admitted_observation_key right) = Phase1DataDeclaration ->
    ~ phase1_surface_admitted_observation_equiv left right.
Proof.
  intros left right Hrecord Hdata Hequiv.
  pose proof
    (phase1_surface_admitted_observation_equiv_preserves_tag
      left right Hequiv) as Htag.
  rewrite Hrecord, Hdata in Htag.
  discriminate Htag.
Qed.
