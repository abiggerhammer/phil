From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List.
From Phil.Surface Require Import BranchEvidenceSupport.
From Phil.Assurance Require Import
  EvidenceConsumerSubjectTransport
  EvidenceConsumerEndpointCoverage
  EvidenceConsumerSelectionCoverage
  EvidenceConsumerUseClassification
  EvidenceConsumerFinalUseCorrespondence.
Import ListNotations.

(*
  Defensive proof-correspondence continuation of D-RES-SUPPORT-01 /
  D-RES-TREE-01 after same-event final-use correspondence.

  EvidenceConsumerFinalUseCorrespondence.v is total over the represented
  actual evidence-use domain, but the subject-bearing transport model still
  stores only one source/target SubjectId pair per consumer.  A fact can refer
  to more than one logical subject.  Proving transport for one represented
  subject therefore does not establish that every relevant subject occurrence
  of the same evidence use was represented.

  This module adds an occurrence-level inventory boundary.  Every relevant
  subject occurrence of an actual evidence use must be represented, every
  represented occurrence must have source and target endpoints, and those
  endpoints must satisfy ExportSubject using the same survivor/rebase state as
  the existing consumer-level transport model.

  The concrete Haskell adapter remains responsible for faithfully enumerating
  the actual subject-occurrence domain and reflecting each occurrence into the
  right stable SubjectId values.  This proof does not manufacture that native
  inventory, restore consumed ownership, or change any Phase 1 trusted-
  computing-base boundary.
*)

Definition EvidenceSubjectOccurrenceId := nat.

Record EvidenceConsumerSubjectOccurrenceCoverageModel : Type :=
  mkEvidenceConsumerSubjectOccurrenceCoverageModel {
    modelOccurrenceFinalUse : EvidenceConsumerFinalUseModel;
    modelActualSubjectOccurrence :
      EvidenceConsumerId -> EvidenceSubjectOccurrenceId -> bool;
    modelRepresentedSubjectOccurrence :
      EvidenceConsumerId -> EvidenceSubjectOccurrenceId -> bool;
    modelOccurrenceSourceSubject :
      EvidenceConsumerId -> EvidenceSubjectOccurrenceId -> option SubjectId;
    modelOccurrenceTargetSubject :
      EvidenceConsumerId -> EvidenceSubjectOccurrenceId -> option SubjectId
  }.

Definition occurrenceTransportModel
  (model : EvidenceConsumerSubjectOccurrenceCoverageModel)
  : EvidenceConsumerSubjectTransportModel :=
  modelSelectionTransport
    (modelUseSelection
      (modelFinalUseClassification (modelOccurrenceFinalUse model))).

Definition EvidenceConsumerSubjectOccurrenceInventoryCoverage
  (model : EvidenceConsumerSubjectOccurrenceCoverageModel) : Prop :=
  forall consumer occurrence,
    modelActualEvidenceUse
      (modelFinalUseClassification (modelOccurrenceFinalUse model)) consumer =
      true ->
    modelActualSubjectOccurrence model consumer occurrence = true ->
    modelRepresentedSubjectOccurrence model consumer occurrence = true.

Definition EvidenceConsumerSubjectOccurrenceEndpointCoverage
  (model : EvidenceConsumerSubjectOccurrenceCoverageModel) : Prop :=
  forall consumer occurrence,
    modelRepresentedSubjectOccurrence model consumer occurrence = true ->
    exists source target,
      modelOccurrenceSourceSubject model consumer occurrence = Some source /\
      modelOccurrenceTargetSubject model consumer occurrence = Some target.

Definition EvidenceConsumerSubjectOccurrenceTransportPreserved
  (model : EvidenceConsumerSubjectOccurrenceCoverageModel) : Prop :=
  forall consumer occurrence source target,
    modelRepresentedSubjectOccurrence model consumer occurrence = true ->
    modelOccurrenceSourceSubject model consumer occurrence = Some source ->
    modelOccurrenceTargetSubject model consumer occurrence = Some target ->
    ExportSubject
      (modelTransportSurvivors (occurrenceTransportModel model))
      (modelTransportRebases (occurrenceTransportModel model))
      source
      target.

Definition CompleteEvidenceConsumerSubjectOccurrenceCorrespondence
  (model : EvidenceConsumerSubjectOccurrenceCoverageModel) : Prop :=
  CompleteEvidenceConsumerFinalUseCorrespondence
    (modelOccurrenceFinalUse model) /\
  forall consumer occurrence,
    modelActualEvidenceUse
      (modelFinalUseClassification (modelOccurrenceFinalUse model)) consumer =
      true ->
    modelActualSubjectOccurrence model consumer occurrence = true ->
    exists source target,
      modelRepresentedSubjectOccurrence model consumer occurrence = true /\
      modelOccurrenceSourceSubject model consumer occurrence = Some source /\
      modelOccurrenceTargetSubject model consumer occurrence = Some target /\
      ExportSubject
        (modelTransportSurvivors (occurrenceTransportModel model))
        (modelTransportRebases (occurrenceTransportModel model))
        source
        target.

Theorem final_use_and_subject_occurrence_coverage_compose :
  forall model,
    CompleteEvidenceConsumerFinalUseCorrespondence
      (modelOccurrenceFinalUse model) ->
    EvidenceConsumerSubjectOccurrenceInventoryCoverage model ->
    EvidenceConsumerSubjectOccurrenceEndpointCoverage model ->
    EvidenceConsumerSubjectOccurrenceTransportPreserved model ->
    CompleteEvidenceConsumerSubjectOccurrenceCorrespondence model.
Proof.
  intros model Hfinal Hinventory Hendpoints Htransport.
  split.
  - exact Hfinal.
  - intros consumer occurrence Hactual Hoccurrence.
    pose proof
      (Hinventory consumer occurrence Hactual Hoccurrence)
      as Hrepresented.
    destruct (Hendpoints consumer occurrence Hrepresented)
      as [source [target [Hsource Htarget]]].
    exists source, target.
    split.
    + exact Hrepresented.
    + split.
      * exact Hsource.
      * split.
        -- exact Htarget.
        -- eapply Htransport; eauto.
Qed.

(*
  A consumer-level model with two live subjects.  Its existing one-pair
  correspondence follows subject 1; subject 2 is deliberately left to the
  occurrence-level inventory below.  This is the shape that demonstrates why
  final-use correspondence alone cannot establish multi-subject completeness.
*)
Definition multiSubjectConsumerTransportWitness
  : EvidenceConsumerSubjectTransportModel :=
  mkEvidenceConsumerSubjectTransportModel
    [1; 2]
    []
    (fun consumer => Nat.eqb consumer 7)
    (fun consumer => if Nat.eqb consumer 7 then Some 1 else None)
    (fun consumer => if Nat.eqb consumer 7 then Some 1 else None).

Theorem multi_subject_consumer_has_complete_transport :
  CompleteEvidenceConsumerSubjectTransport
    multiSubjectConsumerTransportWitness.
Proof.
  intros consumer Hselected.
  cbn in Hselected.
  apply Nat.eqb_eq in Hselected.
  subst consumer.
  exists 1, 1.
  split; [reflexivity |].
  split; [reflexivity |].
  apply ExportSubject_survives.
  simpl. left. reflexivity.
Qed.

Definition multiSubjectSelectionWitness
  : EvidenceConsumerSelectionCoverageModel :=
  mkEvidenceConsumerSelectionCoverageModel
    multiSubjectConsumerTransportWitness
    (fun consumer => Nat.eqb consumer 7).

Theorem multi_subject_selection_is_covered :
  EvidenceConsumerSelectionCoverage multiSubjectSelectionWitness.
Proof.
  intros consumer Hactual.
  exact Hactual.
Qed.

Theorem multi_subject_actual_use_has_complete_transport :
  ActualUseCompleteEvidenceConsumerSubjectTransport
    multiSubjectSelectionWitness.
Proof.
  eapply selection_coverage_lifts_complete_transport_to_actual_uses.
  - exact multi_subject_selection_is_covered.
  - exact multi_subject_consumer_has_complete_transport.
Qed.

Definition multiSubjectUseClassificationWitness
  : EvidenceConsumerUseClassificationModel :=
  mkEvidenceConsumerUseClassificationModel
    multiSubjectSelectionWitness
    (fun consumer => Nat.eqb consumer 7)
    (fun _ => false).

Theorem multi_subject_use_has_classification_coverage :
  EvidenceConsumerUseClassificationCoverage
    multiSubjectUseClassificationWitness.
Proof.
  intros consumer Hactual.
  left. exact Hactual.
Qed.

Theorem multi_subject_closed_classification_is_disjoint :
  CheckedClosedEvidenceUseDisjointFromSubjectBearing
    multiSubjectUseClassificationWitness.
Proof.
  intros consumer Hclosed.
  cbn in Hclosed. discriminate Hclosed.
Qed.

Theorem multi_subject_use_has_complete_correspondence :
  CompleteEvidenceConsumerUseCorrespondence
    multiSubjectUseClassificationWitness.
Proof.
  eapply classified_actual_uses_receive_transport_or_checked_closed_credit.
  - exact multi_subject_use_has_classification_coverage.
  - exact multi_subject_closed_classification_is_disjoint.
  - exact multi_subject_actual_use_has_complete_transport.
Qed.

Definition multiSubjectFinalUseWitness : EvidenceConsumerFinalUseModel :=
  mkEvidenceConsumerFinalUseModel
    multiSubjectUseClassificationWitness
    (fun consumer => if Nat.eqb consumer 7 then Some 7 else None)
    (fun consumer => if Nat.eqb consumer 7 then Some 7 else None)
    (fun consumer => Nat.eqb consumer 7).

Theorem multi_subject_same_event_final_use_is_preserved :
  SameEventFinalEvidenceUsePreserved multiSubjectFinalUseWitness.
Proof.
  intros consumer Hactual.
  cbn in Hactual.
  apply Nat.eqb_eq in Hactual.
  subst consumer.
  exists 7.
  repeat split; reflexivity.
Qed.

Theorem multi_subject_final_use_has_complete_correspondence :
  CompleteEvidenceConsumerFinalUseCorrespondence
    multiSubjectFinalUseWitness.
Proof.
  eapply complete_use_correspondence_and_same_event_final_use_compose.
  - exact multi_subject_use_has_complete_correspondence.
  - exact multi_subject_same_event_final_use_is_preserved.
Qed.

Definition twoSubjectOccurrenceSelected
  (consumer : EvidenceConsumerId)
  (occurrence : EvidenceSubjectOccurrenceId) : bool :=
  if Nat.eqb consumer 7 then
    if Nat.eqb occurrence 1 then true else Nat.eqb occurrence 2
  else false.

Definition firstSubjectOccurrenceOnly
  (consumer : EvidenceConsumerId)
  (occurrence : EvidenceSubjectOccurrenceId) : bool :=
  if Nat.eqb consumer 7 then Nat.eqb occurrence 1 else false.

Definition twoSubjectOccurrenceEndpoint
  (consumer : EvidenceConsumerId)
  (occurrence : EvidenceSubjectOccurrenceId) : option SubjectId :=
  if Nat.eqb consumer 7 then
    if Nat.eqb occurrence 1 then Some 1
    else if Nat.eqb occurrence 2 then Some 2 else None
  else None.

(*
  Negative witness: the actual use reaches the right final consumer under the
  right event and its represented consumer-level subject transports legally,
  but the adapter represents only the first of two actual subject occurrences.
*)
Definition omittedSecondSubjectOccurrenceWitness
  : EvidenceConsumerSubjectOccurrenceCoverageModel :=
  mkEvidenceConsumerSubjectOccurrenceCoverageModel
    multiSubjectFinalUseWitness
    twoSubjectOccurrenceSelected
    firstSubjectOccurrenceOnly
    (fun consumer occurrence =>
      if firstSubjectOccurrenceOnly consumer occurrence then Some 1 else None)
    (fun consumer occurrence =>
      if firstSubjectOccurrenceOnly consumer occurrence then Some 1 else None).

Theorem omitted_second_subject_still_has_complete_final_use_correspondence :
  CompleteEvidenceConsumerFinalUseCorrespondence
    (modelOccurrenceFinalUse omittedSecondSubjectOccurrenceWitness).
Proof.
  exact multi_subject_final_use_has_complete_correspondence.
Qed.

Theorem omitted_second_subject_lacks_occurrence_inventory_coverage :
  ~ EvidenceConsumerSubjectOccurrenceInventoryCoverage
      omittedSecondSubjectOccurrenceWitness.
Proof.
  intro Hcoverage.
  pose proof (Hcoverage 7 2 eq_refl eq_refl) as Hrepresented.
  cbn in Hrepresented.
  discriminate Hrepresented.
Qed.

Theorem complete_final_use_does_not_establish_multi_subject_coverage :
  CompleteEvidenceConsumerFinalUseCorrespondence
    (modelOccurrenceFinalUse omittedSecondSubjectOccurrenceWitness) /\
  ~ CompleteEvidenceConsumerSubjectOccurrenceCorrespondence
      omittedSecondSubjectOccurrenceWitness.
Proof.
  split.
  - exact omitted_second_subject_still_has_complete_final_use_correspondence.
  - intros [_ Hoccurrences].
    destruct (Hoccurrences 7 2 eq_refl eq_refl)
      as [source [target [Hrepresented Hrest]]].
    cbn in Hrepresented.
    discriminate Hrepresented.
Qed.

(* Positive witness: both actual subject occurrences are represented and each
   occurrence receives a complete endpoint pair and legal stable transport. *)
Definition completeTwoSubjectOccurrenceWitness
  : EvidenceConsumerSubjectOccurrenceCoverageModel :=
  mkEvidenceConsumerSubjectOccurrenceCoverageModel
    multiSubjectFinalUseWitness
    twoSubjectOccurrenceSelected
    twoSubjectOccurrenceSelected
    twoSubjectOccurrenceEndpoint
    twoSubjectOccurrenceEndpoint.

Theorem complete_two_subject_inventory_is_covered :
  EvidenceConsumerSubjectOccurrenceInventoryCoverage
    completeTwoSubjectOccurrenceWitness.
Proof.
  intros consumer occurrence Hactual Hoccurrence.
  exact Hoccurrence.
Qed.

Theorem complete_two_subject_endpoints_are_covered :
  EvidenceConsumerSubjectOccurrenceEndpointCoverage
    completeTwoSubjectOccurrenceWitness.
Proof.
  intros consumer occurrence Hrepresented.
  cbn in Hrepresented.
  unfold twoSubjectOccurrenceSelected in Hrepresented.
  destruct (Nat.eqb consumer 7) eqn:Hconsumer.
  - destruct (Nat.eqb occurrence 1) eqn:Hfirst.
    + apply Nat.eqb_eq in Hconsumer.
      apply Nat.eqb_eq in Hfirst.
      subst consumer. subst occurrence.
      exists 1, 1. split; reflexivity.
    + destruct (Nat.eqb occurrence 2) eqn:Hsecond.
      * apply Nat.eqb_eq in Hconsumer.
        apply Nat.eqb_eq in Hsecond.
        subst consumer. subst occurrence.
        exists 2, 2. split; reflexivity.
      * discriminate Hrepresented.
  - discriminate Hrepresented.
Qed.

Theorem complete_two_subject_transport_is_preserved :
  EvidenceConsumerSubjectOccurrenceTransportPreserved
    completeTwoSubjectOccurrenceWitness.
Proof.
  intros consumer occurrence source target Hrepresented Hsource Htarget.
  cbn in Hsource, Htarget.
  unfold twoSubjectOccurrenceEndpoint in Hsource, Htarget.
  destruct (Nat.eqb consumer 7) eqn:Hconsumer.
  - destruct (Nat.eqb occurrence 1) eqn:Hfirst.
    + inversion Hsource; subst source.
      inversion Htarget; subst target.
      apply ExportSubject_survives.
      simpl. left. reflexivity.
    + destruct (Nat.eqb occurrence 2) eqn:Hsecond.
      * inversion Hsource; subst source.
        inversion Htarget; subst target.
        apply ExportSubject_survives.
        simpl. right. left. reflexivity.
      * discriminate Hsource.
  - discriminate Hsource.
Qed.

Theorem complete_two_subject_use_has_occurrence_correspondence :
  CompleteEvidenceConsumerSubjectOccurrenceCorrespondence
    completeTwoSubjectOccurrenceWitness.
Proof.
  eapply final_use_and_subject_occurrence_coverage_compose.
  - exact multi_subject_final_use_has_complete_correspondence.
  - exact complete_two_subject_inventory_is_covered.
  - exact complete_two_subject_endpoints_are_covered.
  - exact complete_two_subject_transport_is_preserved.
Qed.

(* A checked closed use still requires no invented subject occurrence. *)
Definition checkedClosedNoSubjectOccurrenceWitness
  : EvidenceConsumerSubjectOccurrenceCoverageModel :=
  mkEvidenceConsumerSubjectOccurrenceCoverageModel
    checkedClosedSameEventFinalUseWitness
    (fun _ _ => false)
    (fun _ _ => false)
    (fun _ _ => None)
    (fun _ _ => None).

Theorem checked_closed_use_needs_no_subject_occurrence :
  CompleteEvidenceConsumerSubjectOccurrenceCorrespondence
    checkedClosedNoSubjectOccurrenceWitness.
Proof.
  eapply final_use_and_subject_occurrence_coverage_compose.
  - exact checked_closed_same_event_has_complete_final_correspondence.
  - intros consumer occurrence Hactual Hoccurrence.
    cbn in Hoccurrence. discriminate Hoccurrence.
  - intros consumer occurrence Hrepresented.
    cbn in Hrepresented. discriminate Hrepresented.
  - intros consumer occurrence source target Hrepresented Hsource Htarget.
    cbn in Hrepresented. discriminate Hrepresented.
Qed.

Theorem subject_occurrence_coverage_distinguishes_omission_and_closed_use :
  ~ EvidenceConsumerSubjectOccurrenceInventoryCoverage
      omittedSecondSubjectOccurrenceWitness /\
  CompleteEvidenceConsumerSubjectOccurrenceCorrespondence
    completeTwoSubjectOccurrenceWitness /\
  CompleteEvidenceConsumerSubjectOccurrenceCorrespondence
    checkedClosedNoSubjectOccurrenceWitness.
Proof.
  split.
  - exact omitted_second_subject_lacks_occurrence_inventory_coverage.
  - split.
    + exact complete_two_subject_use_has_occurrence_correspondence.
    + exact checked_closed_use_needs_no_subject_occurrence.
Qed.
