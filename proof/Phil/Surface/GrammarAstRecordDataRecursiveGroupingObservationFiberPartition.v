From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingObservationPER
  GrammarAstRecordDataRecursiveGroupingObservationClassifier
  GrammarAstRecordDataRecursiveGroupingObservationDerivedPairFibers.

Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: successful option-valued
  Record/Data observation fibers form nonempty, disjoint-or-equal
  relatedness classes. A shared member forces equal observations and
  related centers; distinct observations cannot share a member; the
  relatedness class is determined extensionally by its members.
  Rejected public intermediate carriers belong to no successful fiber.

  Proof-side only: no production AST binding, exact-key injectivity,
  Grammar-v1 or TCB change, G2/G4 result, or Phase 1 closure.
*)

Theorem phase1_surface_successful_observation_fiber_overlap_forces_class :
  forall left right common left_observed right_observed,
    phase1_surface_normalized_observation left = Some left_observed ->
    phase1_surface_normalized_observation right = Some right_observed ->
    phase1_surface_recursive_grouping_observation_related left common ->
    phase1_surface_recursive_grouping_observation_related right common ->
    left_observed = right_observed /\
    phase1_surface_recursive_grouping_observation_related left right.
Proof.
  intros left right common left_observed right_observed
    Hleft Hright Hleft_common Hright_common.
  pose proof (proj2 (phase1_surface_observation_fiber_iff_related
    left common left_observed Hleft) Hleft_common) as Hcommon_left.
  pose proof (proj2 (phase1_surface_observation_fiber_iff_related
    right common right_observed Hright) Hright_common) as Hcommon_right.
  rewrite Hcommon_left in Hcommon_right.
  injection Hcommon_right as Heq.
  subst right_observed.
  split; [reflexivity |].
  apply (proj1 (phase1_surface_observation_fiber_iff_related
    left right left_observed Hleft)).
  exact Hright.
Qed.

Theorem phase1_surface_successful_observation_fibers_disjoint_if_values_differ :
  forall left right common left_observed right_observed,
    phase1_surface_normalized_observation left = Some left_observed ->
    phase1_surface_normalized_observation right = Some right_observed ->
    left_observed <> right_observed ->
    ~ (phase1_surface_recursive_grouping_observation_related left common /\
       phase1_surface_recursive_grouping_observation_related right common).
Proof.
  intros left right common left_observed right_observed
    Hleft Hright Hdistinct [Hleft_common Hright_common].
  destruct (phase1_surface_successful_observation_fiber_overlap_forces_class
    left right common left_observed right_observed
    Hleft Hright Hleft_common Hright_common) as [Heq _].
  exact (Hdistinct Heq).
Qed.

Theorem phase1_surface_successful_observation_fibers_same_members_iff_related :
  forall left right left_observed right_observed,
    phase1_surface_normalized_observation left = Some left_observed ->
    phase1_surface_normalized_observation right = Some right_observed ->
    ((forall member,
       phase1_surface_recursive_grouping_observation_related left member <->
       phase1_surface_recursive_grouping_observation_related right member) <->
     phase1_surface_recursive_grouping_observation_related left right).
Proof.
  intros left right left_observed right_observed Hleft Hright.
  split.
  - intro Hmembers.
    apply phase1_surface_recursive_grouping_observation_related_symmetric.
    apply (proj1 (Hmembers left)).
    apply (proj1 (phase1_surface_observation_fiber_iff_related
      left left left_observed Hleft)).
    exact Hleft.
  - intros Hrelated member.
    split; intro Hmember.
    + eapply phase1_surface_recursive_grouping_observation_related_transitive.
      * apply phase1_surface_recursive_grouping_observation_related_symmetric.
        exact Hrelated.
      * exact Hmember.
    + eapply phase1_surface_recursive_grouping_observation_related_transitive.
      * exact Hrelated.
      * exact Hmember.
Qed.

Theorem phase1_surface_rejected_observation_key_not_in_successful_fiber :
  forall center member observed,
    phase1_surface_normalized_observation center = Some observed ->
    phase1_surface_normalized_observation member = None ->
    ~ phase1_surface_recursive_grouping_observation_related center member.
Proof.
  intros center member observed Hcenter Hreject Hrelated.
  pose proof (proj2 (phase1_surface_observation_fiber_iff_related
    center member observed Hcenter) Hrelated) as Hmember.
  rewrite Hreject in Hmember.
  discriminate Hmember.
Qed.
