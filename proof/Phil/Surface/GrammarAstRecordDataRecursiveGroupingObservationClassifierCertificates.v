From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingImplementationRepresentation
  GrammarAstRecordDataRecursiveGroupingProductionObservables
  GrammarAstRecordDataRecursiveGroupingObservationPER
  GrammarAstRecordDataRecursiveGroupingObservationAdmittedQuotient
  GrammarAstRecordDataRecursiveGroupingObservationAdmittedDerivations
  GrammarAstRecordDataRecursiveGroupingObservationClassifier.

Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: make the option-valued public
  Record/Data classifier agree with every successful admission
  certificate, and establish a nonvacuous computational test for
  observational relatedness. Canonical Grammar-v1 Record/Data
  derivations obtain successful classifications.

  Equality of two None results never supplies an observation class.
  Classifier equality on admitted certificates is observational,
  not exact public tag/tree-key equality. These results are proof-side
  only: no new admission, grammar/TCB change, production AST binding,
  G2/G4 correspondence, or Phase 1 closure.
*)

Theorem phase1_surface_classifier_matches_admitted_certificate :
  forall entry : Phase1SurfaceAdmittedObservationKey,
    phase1_surface_normalized_observation
      (phase1_admitted_observation_key entry) =
    Some (phase1_surface_admitted_observation entry).
Proof.
  intro entry.
  unfold phase1_surface_normalized_observation,
    phase1_surface_admitted_observation.
  now rewrite (phase1_admitted_observation_certificate entry).
Qed.

Theorem phase1_surface_classifier_some_iff_certified_observation :
  forall key observed,
    phase1_surface_normalized_observation key = Some observed <->
    exists entry : Phase1SurfaceAdmittedObservationKey,
      phase1_admitted_observation_key entry = key /\
      phase1_surface_admitted_observation entry = observed.
Proof.
  intros key observed.
  split.
  - intro Hsome.
    unfold phase1_surface_normalized_observation in Hsome.
    destruct (phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      key) as [refined |] eqn:Hnormalize; try discriminate Hsome.
    inversion Hsome; subst observed.
    exists
      {| phase1_admitted_observation_key := key;
         phase1_admitted_observation_refined := refined;
         phase1_admitted_observation_certificate := Hnormalize |}.
    split; reflexivity.
  - intros [entry [Hkey Hobserved]].
    rewrite <- Hkey.
    rewrite phase1_surface_classifier_matches_admitted_certificate.
    now rewrite Hobserved.
Qed.

Theorem phase1_surface_classifier_certified_equiv_iff_same_result :
  forall left right : Phase1SurfaceAdmittedObservationKey,
    phase1_surface_admitted_observation_equiv left right <->
    phase1_surface_normalized_observation
      (phase1_admitted_observation_key left) =
    phase1_surface_normalized_observation
      (phase1_admitted_observation_key right).
Proof.
  intros left right.
  rewrite (phase1_surface_classifier_matches_admitted_certificate left).
  rewrite (phase1_surface_classifier_matches_admitted_certificate right).
  unfold phase1_surface_admitted_observation_equiv.
  split; intro Heq.
  - now rewrite Heq.
  - injection Heq as Hobserved.
    exact Hobserved.
Qed.

Theorem phase1_surface_classifier_nonempty_equality_iff_related :
  forall left right,
    (phase1_surface_normalized_observation left =
       phase1_surface_normalized_observation right /\
     phase1_surface_normalized_observation left <> None) <->
    phase1_surface_recursive_grouping_observation_related left right.
Proof.
  intros left right.
  split.
  - intros [Heq Hnonempty].
    destruct (phase1_surface_normalized_observation left)
      as [observed |] eqn:Hleft.
    + apply (proj2
        (phase1_surface_normalized_observation_related_iff_same_success
          left right)).
      exists observed.
      split; [exact Hleft |].
      rewrite <- Heq.
      exact Hleft.
    + exfalso.
      apply Hnonempty.
      exact Hleft.
  - intro Hrelated.
    destruct (proj1
      (phase1_surface_normalized_observation_related_iff_same_success
        left right) Hrelated) as [observed [Hleft Hright]].
    split.
    + now rewrite Hleft, Hright.
    + rewrite Hleft.
      discriminate.
Qed.

Theorem phase1_surface_derived_record_classifier_success :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "record_decl")
      input rest tree ->
    exists observed,
      phase1_surface_normalized_observation
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := tree |} = Some observed.
Proof.
  intros path input rest tree Hderive.
  destruct (phase1_surface_derived_record_has_admitted_equivalence_representative
    path input rest tree Hderive) as [entry [Hkey _]].
  exists (phase1_surface_admitted_observation entry).
  rewrite <- Hkey.
  apply phase1_surface_classifier_matches_admitted_certificate.
Qed.

Theorem phase1_surface_derived_data_classifier_success :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "data_decl")
      input rest tree ->
    exists observed,
      phase1_surface_normalized_observation
        {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := tree |} = Some observed.
Proof.
  intros path input rest tree Hderive.
  destruct (phase1_surface_derived_data_has_admitted_equivalence_representative
    path input rest tree Hderive) as [entry [Hkey _]].
  exists (phase1_surface_admitted_observation entry).
  rewrite <- Hkey.
  apply phase1_surface_classifier_matches_admitted_certificate.
Qed.
