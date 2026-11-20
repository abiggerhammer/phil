From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingImplementationRepresentation
  GrammarAstRecordDataRecursiveGroupingProductionObservables
  GrammarAstRecordDataRecursiveGroupingObservationPER
  GrammarAstRecordDataRecursiveGroupingObservationPERDomain
  GrammarAstRecordDataRecursiveGroupingObservationClassSaturation.

Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: expose an option-valued
  observational classifier for public Record/Data declaration keys.
  None is rejection; equality of successful classifications
  characterizes public observational relatedness, without confusing
  lossy observation with exact-key equality. Failed admission is not
  promoted to a class; Record and Data remain separated.
  Proof-side only: no new admission, Grammar-v1 or TCB changes,
  production Haskell AST binding, G2/G4, or Phase 1 closure.
*)

Definition phase1_surface_normalized_observation
  (key : Phase1SurfaceDeclarationSpine)
  : option Phase1SurfaceRecursiveGroupingObservedRecordData :=
  match phase1_surface_normalize_recursive_grouping_record_data_declaration_spine key with
  | Some refined => Some (phase1_surface_observe_recursive_grouping_record_data refined)
  | None => None
  end.

Theorem phase1_surface_normalized_observation_none_iff_rejection :
  forall key,
    phase1_surface_normalized_observation key = None <->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine key = None.
Proof.
  intro key.
  unfold phase1_surface_normalized_observation.
  destruct (phase1_surface_normalize_recursive_grouping_record_data_declaration_spine key)
    as [refined |] eqn:Hnormal; simpl.
  - split; intro H; discriminate.
  - split; intro H; reflexivity.
Qed.

Theorem phase1_surface_normalized_observation_some_iff_admission :
  forall key,
    (exists observed, phase1_surface_normalized_observation key = Some observed) <->
    (exists refined,
      phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
        key = Some refined).
Proof.
  intro key.
  split.
  - intros [observed Hsome].
    unfold phase1_surface_normalized_observation in Hsome.
    destruct (phase1_surface_normalize_recursive_grouping_record_data_declaration_spine key)
      as [refined |] eqn:Hnormal.
    + exists refined. reflexivity.
    + discriminate Hsome.
  - intros [refined Hnormal].
    exists (phase1_surface_observe_recursive_grouping_record_data refined).
    unfold phase1_surface_normalized_observation.
    now rewrite Hnormal.
Qed.

Theorem phase1_surface_normalized_observation_related_iff_same_success :
  forall left right,
    phase1_surface_recursive_grouping_observation_related left right <->
    exists observed,
      phase1_surface_normalized_observation left = Some observed /\
      phase1_surface_normalized_observation right = Some observed.
Proof.
  intros left right.
  split.
  - intros [left_refined [right_refined [Hleft [Hright Hobs]]]].
    exists (phase1_surface_observe_recursive_grouping_record_data left_refined).
    unfold phase1_surface_normalized_observation.
    split.
    + now rewrite Hleft.
    + now rewrite Hright, Hobs.
  - intros [observed [Hleft Hright]].
    unfold phase1_surface_normalized_observation in Hleft, Hright.
    destruct (phase1_surface_normalize_recursive_grouping_record_data_declaration_spine left)
      as [left_refined |] eqn:Hleft_norm; try discriminate.
    destruct (phase1_surface_normalize_recursive_grouping_record_data_declaration_spine right)
      as [right_refined |] eqn:Hright_norm; try discriminate.
    injection Hleft as Hleft_obs.
    injection Hright as Hright_obs.
    exists left_refined, right_refined.
    split; [exact Hleft_norm |].
    split; [exact Hright_norm |].
    now rewrite Hleft_obs, Hright_obs.
Qed.

Theorem phase1_surface_normalized_observation_same_success_preserves_tag :
  forall left right observed,
    phase1_surface_normalized_observation left = Some observed ->
    phase1_surface_normalized_observation right = Some observed ->
    phase1_declaration_spine_tag left = phase1_declaration_spine_tag right.
Proof.
  intros left right observed Hleft Hright.
  apply phase1_surface_recursive_grouping_observation_related_preserves_tag.
  apply (proj2
    (phase1_surface_normalized_observation_related_iff_same_success left right)).
  exists observed.
  split; assumption.
Qed.

Theorem phase1_surface_normalized_observation_is_lossy :
  exists left right observed,
    left <> right /\
    phase1_surface_normalized_observation left = Some observed /\
    phase1_surface_normalized_observation right = Some observed.
Proof.
  destruct phase1_surface_recursive_grouping_observation_related_not_exact_key_equality
    as [left [right [Hrelated Hdistinct]]].
  apply (proj1
    (phase1_surface_normalized_observation_related_iff_same_success left right))
    in Hrelated.
  destruct Hrelated as [observed [Hleft Hright]].
  exists left, right, observed.
  repeat split; assumption.
Qed.

Theorem phase1_surface_record_data_normalized_observation_separated :
  forall record_tree data_tree,
    ~ (exists observed,
        phase1_surface_normalized_observation
          {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
             phase1_declaration_spine_selected_tree := record_tree |} = Some observed /\
        phase1_surface_normalized_observation
          {| phase1_declaration_spine_tag := Phase1DataDeclaration;
             phase1_declaration_spine_selected_tree := data_tree |} = Some observed).
Proof.
  intros record_tree data_tree [observed [Hrecord Hdata]].
  apply (phase1_surface_recursive_grouping_record_data_observation_classes_disjoint
    record_tree data_tree).
  apply (proj2
    (phase1_surface_normalized_observation_related_iff_same_success
      {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
         phase1_declaration_spine_selected_tree := record_tree |}
      {| phase1_declaration_spine_tag := Phase1DataDeclaration;
         phase1_declaration_spine_selected_tree := data_tree |})).
  exists observed.
  split; assumption.
Qed.
