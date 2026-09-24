From Stdlib Require Import Bool.Bool Arith.PeanoNat.
From Phil.Assurance Require Import
  EvidenceConsumerUseClassification
  EvidenceConsumerFinalUseCorrespondence
  EvidenceConsumerSubjectOccurrenceCoverage.

(*
  Defensive proof-correspondence continuation of D-RES-SUPPORT-01 /
  D-RES-TREE-01 after complete subject-occurrence coverage.

  EvidenceConsumerFinalUseCorrespondence.v requires the same event identifier
  at the original and final evidence-use endpoints.  A caller can still supply
  matching event metadata without establishing that the event identifier came
  from an approved original checking event.  In particular, the mere presence
  of a ResidualSpec parameter is not producer evidence for a residual-free
  result.

  This module adds that producer-origin boundary without changing the existing
  event, use, subject-occurrence, or transport models.  Every actual evidence
  use must retain its already-required event identity and that exact event must
  be marked as originating from an approved producer.  An unrelated approved
  event is insufficient.

  The concrete Haskell implementation remains responsible for reflecting the
  real producer relationship into this predicate.  This proof does not create
  stored events, infer origin from ResidualSpec, alter source admission,
  restore resource ownership, change native lowering, or move LLVM outside the
  Phase 1 trusted-computing-base boundary.
*)

Record EvidenceConsumerEventOriginModel : Type :=
  mkEvidenceConsumerEventOriginModel {
    modelOriginSubjectOccurrences :
      EvidenceConsumerSubjectOccurrenceCoverageModel;
    modelApprovedProducerEvent : EvidenceUseEventId -> bool
  }.

Definition ApprovedActualUseEventOriginPreserved
  (model : EvidenceConsumerEventOriginModel) : Prop :=
  forall consumer,
    modelActualEvidenceUse
      (modelFinalUseClassification
        (modelOccurrenceFinalUse
          (modelOriginSubjectOccurrences model))) consumer = true ->
    exists event,
      modelActualUseEvent
        (modelOccurrenceFinalUse
          (modelOriginSubjectOccurrences model)) consumer = Some event /\
      modelApprovedProducerEvent model event = true.

Definition CompleteEvidenceConsumerEventOriginCorrespondence
  (model : EvidenceConsumerEventOriginModel) : Prop :=
  CompleteEvidenceConsumerSubjectOccurrenceCorrespondence
    (modelOriginSubjectOccurrences model) /\
  ApprovedActualUseEventOriginPreserved model.

Theorem subject_occurrence_and_approved_event_origin_compose :
  forall model,
    CompleteEvidenceConsumerSubjectOccurrenceCorrespondence
      (modelOriginSubjectOccurrences model) ->
    ApprovedActualUseEventOriginPreserved model ->
    CompleteEvidenceConsumerEventOriginCorrespondence model.
Proof.
  intros model Hoccurrences Horigin.
  split; assumption.
Qed.

(*
  Negative witness: consumer 7 has complete closed-use, same-event final-use,
  and subject-occurrence correspondence, but its matching event metadata has
  no approved producer origin.  This models the forbidden inference from
  caller-supplied event/residual metadata to an independently produced event.
*)
Definition metadataOnlyEventOriginWitness : EvidenceConsumerEventOriginModel :=
  mkEvidenceConsumerEventOriginModel
    checkedClosedNoSubjectOccurrenceWitness
    (fun _ => false).

Theorem metadata_only_event_still_has_complete_subject_occurrence_correspondence :
  CompleteEvidenceConsumerSubjectOccurrenceCorrespondence
    (modelOriginSubjectOccurrences metadataOnlyEventOriginWitness).
Proof.
  exact checked_closed_use_needs_no_subject_occurrence.
Qed.

Theorem metadata_only_event_lacks_approved_origin :
  ~ ApprovedActualUseEventOriginPreserved metadataOnlyEventOriginWitness.
Proof.
  intro Horigin.
  destruct (Horigin 7 eq_refl) as [event [Hactual Hproducer]].
  cbn in Hactual.
  inversion Hactual; subst event.
  cbn in Hproducer.
  discriminate Hproducer.
Qed.

Theorem complete_subject_occurrence_correspondence_does_not_establish_origin :
  CompleteEvidenceConsumerSubjectOccurrenceCorrespondence
    (modelOriginSubjectOccurrences metadataOnlyEventOriginWitness) /\
  ~ CompleteEvidenceConsumerEventOriginCorrespondence
      metadataOnlyEventOriginWitness.
Proof.
  split.
  - exact metadata_only_event_still_has_complete_subject_occurrence_correspondence.
  - intros [_ Horigin].
    exact (metadata_only_event_lacks_approved_origin Horigin).
Qed.

(*
  A different approved producer also cannot authorize consumer 7's event 7.
  The producer relation must apply to the exact event already used by the
  same-event final-use correspondence.
*)
Definition unrelatedApprovedEventOriginWitness
  : EvidenceConsumerEventOriginModel :=
  mkEvidenceConsumerEventOriginModel
    checkedClosedNoSubjectOccurrenceWitness
    (fun event => Nat.eqb event 8).

Theorem unrelated_approved_event_does_not_establish_origin :
  ~ ApprovedActualUseEventOriginPreserved unrelatedApprovedEventOriginWitness.
Proof.
  intro Horigin.
  destruct (Horigin 7 eq_refl) as [event [Hactual Hproducer]].
  cbn in Hactual.
  inversion Hactual; subst event.
  cbn in Hproducer.
  discriminate Hproducer.
Qed.

(* Positive closed-use witness: event 7 is the exact approved producer event. *)
Definition checkedClosedApprovedEventOriginWitness
  : EvidenceConsumerEventOriginModel :=
  mkEvidenceConsumerEventOriginModel
    checkedClosedNoSubjectOccurrenceWitness
    (fun event => Nat.eqb event 7).

Theorem checked_closed_actual_use_has_approved_event_origin :
  ApprovedActualUseEventOriginPreserved
    checkedClosedApprovedEventOriginWitness.
Proof.
  intros consumer Hactual.
  cbn in Hactual.
  apply Nat.eqb_eq in Hactual.
  subst consumer.
  exists 7.
  split; reflexivity.
Qed.

Theorem checked_closed_use_has_complete_event_origin_correspondence :
  CompleteEvidenceConsumerEventOriginCorrespondence
    checkedClosedApprovedEventOriginWitness.
Proof.
  eapply subject_occurrence_and_approved_event_origin_compose.
  - exact checked_closed_use_needs_no_subject_occurrence.
  - exact checked_closed_actual_use_has_approved_event_origin.
Qed.

(*
  Positive multi-subject witness: all subject occurrences remain represented,
  and the same exact event 7 also has approved producer origin.
*)
Definition multiSubjectApprovedEventOriginWitness
  : EvidenceConsumerEventOriginModel :=
  mkEvidenceConsumerEventOriginModel
    completeTwoSubjectOccurrenceWitness
    (fun event => Nat.eqb event 7).

Theorem multi_subject_actual_use_has_approved_event_origin :
  ApprovedActualUseEventOriginPreserved
    multiSubjectApprovedEventOriginWitness.
Proof.
  intros consumer Hactual.
  cbn in Hactual.
  apply Nat.eqb_eq in Hactual.
  subst consumer.
  exists 7.
  split; reflexivity.
Qed.

Theorem multi_subject_use_has_complete_event_origin_correspondence :
  CompleteEvidenceConsumerEventOriginCorrespondence
    multiSubjectApprovedEventOriginWitness.
Proof.
  eapply subject_occurrence_and_approved_event_origin_compose.
  - exact complete_two_subject_use_has_occurrence_correspondence.
  - exact multi_subject_actual_use_has_approved_event_origin.
Qed.

Theorem event_origin_correspondence_distinguishes_metadata_and_producer_origin :
  ~ ApprovedActualUseEventOriginPreserved metadataOnlyEventOriginWitness /\
  ~ ApprovedActualUseEventOriginPreserved unrelatedApprovedEventOriginWitness /\
  CompleteEvidenceConsumerEventOriginCorrespondence
    checkedClosedApprovedEventOriginWitness /\
  CompleteEvidenceConsumerEventOriginCorrespondence
    multiSubjectApprovedEventOriginWitness.
Proof.
  split.
  - exact metadata_only_event_lacks_approved_origin.
  - split.
    + exact unrelated_approved_event_does_not_establish_origin.
    + split.
      * exact checked_closed_use_has_complete_event_origin_correspondence.
      * exact multi_subject_use_has_complete_event_origin_correspondence.
Qed.
