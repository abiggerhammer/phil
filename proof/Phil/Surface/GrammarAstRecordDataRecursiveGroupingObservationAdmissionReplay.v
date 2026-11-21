From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingImplementationRepresentation
  GrammarAstRecordDataRecursiveGroupingImplementationAdmissionExamples
  GrammarAstRecordDataRecursiveGroupingTaggedAdmission
  GrammarAstRecordDataRecursiveGroupingTaggedAdmissionStability
  GrammarAstRecordDataRecursiveGroupingProductionObservables
  GrammarAstRecordDataRecursiveGroupingObservationAdmittedQuotient
  GrammarAstRecordDataRecursiveGroupingObservationAdmittedDerivations
  GrammarAstRecordDataRecursiveGroupingObservationClassifier.

Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: the proof-side observation classifier
  remains coherent under the exact admitted Record/Data representation
  reconstruction. In particular an admitted certificate cannot change
  either its public key or observation when replayed, and derivation
  witnesses have an observation-stable replay.

  The replay precondition is actual successful normalization, NOT
  arbitrary public carrier construction. Observation equality does
  not imply exact-key equality. No Grammar-v1/TCB/production AST
  binding change, G2/G4 completion, or Phase 1 closeout is claimed.
*)

Theorem phase1_surface_observation_admitted_replay_exact_key :
  forall key refined,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      key = Some refined ->
    phase1_surface_recursive_grouping_implementation_declaration_spine
      refined = key.
Proof.
  intros key refined Hnormal.
  exact (phase1_surface_recursive_grouping_implementation_tagged_round_trip
    key refined Hnormal).
Qed.

Theorem phase1_surface_observation_admitted_replay_stable :
  forall key refined,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      key = Some refined ->
    phase1_surface_normalized_observation
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        refined) =
    phase1_surface_normalized_observation key.
Proof.
  intros key refined Hnormal.
  rewrite (phase1_surface_observation_admitted_replay_exact_key
    key refined Hnormal).
  reflexivity.
Qed.

Theorem phase1_surface_observation_admitted_replay_value :
  forall key refined,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      key = Some refined ->
    phase1_surface_normalized_observation
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        refined) =
    Some (phase1_surface_observe_recursive_grouping_record_data refined).
Proof.
  intros key refined Hnormal.
  unfold phase1_surface_normalized_observation.
  rewrite (phase1_surface_recursive_grouping_tagged_admission_replay
    key refined Hnormal).
  reflexivity.
Qed.

Theorem phase1_surface_observation_admitted_certificate_replay :
  forall entry : Phase1SurfaceAdmittedObservationKey,
    phase1_surface_normalized_observation
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        (phase1_admitted_observation_refined entry)) =
    Some (phase1_surface_admitted_observation entry).
Proof.
  intro entry.
  unfold phase1_surface_admitted_observation.
  apply (phase1_surface_observation_admitted_replay_value
    (phase1_admitted_observation_key entry)
    (phase1_admitted_observation_refined entry)).
  exact (phase1_admitted_observation_certificate entry).
Qed.

Theorem phase1_surface_observation_admitted_replay_related :
  forall (entry : Phase1SurfaceAdmittedObservationKey) other,
    (phase1_surface_recursive_grouping_observation_related
       (phase1_surface_recursive_grouping_implementation_declaration_spine
         (phase1_admitted_observation_refined entry)) other <->
     phase1_surface_recursive_grouping_observation_related
       (phase1_admitted_observation_key entry) other).
Proof.
  intros entry other.
  rewrite (phase1_surface_observation_admitted_replay_exact_key
    (phase1_admitted_observation_key entry)
    (phase1_admitted_observation_refined entry)
    (phase1_admitted_observation_certificate entry)).
  tauto.
Qed.

Theorem phase1_surface_derived_record_observation_replay :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "record_decl")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := tree |} = Some refined /\
      phase1_surface_normalized_observation
        (phase1_surface_recursive_grouping_implementation_declaration_spine
          refined) =
      phase1_surface_normalized_observation
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := tree |}.
Proof.
  intros path input rest tree Hderive.
  destruct (phase1_surface_derived_record_has_admitted_equivalence_representative
    path input rest tree Hderive) as [entry [Hkey _]].
  assert (Hnormal :
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
         phase1_declaration_spine_selected_tree := tree |} =
    Some (phase1_admitted_observation_refined entry)).
  { rewrite <- Hkey.
    exact (phase1_admitted_observation_certificate entry). }
  exists (phase1_admitted_observation_refined entry).
  split; [exact Hnormal |].
  exact (phase1_surface_observation_admitted_replay_stable _ _ Hnormal).
Qed.

Theorem phase1_surface_derived_data_observation_replay :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "data_decl")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
        {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := tree |} = Some refined /\
      phase1_surface_normalized_observation
        (phase1_surface_recursive_grouping_implementation_declaration_spine
          refined) =
      phase1_surface_normalized_observation
        {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := tree |}.
Proof.
  intros path input rest tree Hderive.
  destruct (phase1_surface_derived_data_has_admitted_equivalence_representative
    path input rest tree Hderive) as [entry [Hkey _]].
  assert (Hnormal :
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      {| phase1_declaration_spine_tag := Phase1DataDeclaration;
         phase1_declaration_spine_selected_tree := tree |} =
    Some (phase1_admitted_observation_refined entry)).
  { rewrite <- Hkey.
    exact (phase1_admitted_observation_certificate entry). }
  exists (phase1_admitted_observation_refined entry).
  split; [exact Hnormal |].
  exact (phase1_surface_observation_admitted_replay_stable _ _ Hnormal).
Qed.

Example phase1_surface_rejected_record_key_has_no_replay :
  ~ exists refined,
      phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := PTLiteral "Nat" |} =
      Some refined.
Proof.
  intros [refined Hnormal].
  rewrite phase1_surface_impl_literal_under_record_tag_rejected in Hnormal.
  discriminate Hnormal.
Qed.
