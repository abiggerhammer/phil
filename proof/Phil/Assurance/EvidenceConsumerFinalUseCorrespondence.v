From Stdlib Require Import Bool.Bool Arith.PeanoNat.
From Phil.Assurance Require Import
  EvidenceConsumerSubjectTransport
  EvidenceConsumerUseClassification.

(*
  Defensive proof-correspondence continuation of D-RES-SUPPORT-01 /
  D-RES-TREE-01 after complete actual-use classification.

  EvidenceConsumerUseClassification.v establishes that every actual evidence
  use is accounted for either by complete subject transport or by an explicit
  checked closed-use classification.  That does not yet establish that the
  evidence support credited to the use reaches the final consuming operation
  under the same original checking event.

  This module keeps that final-use identity boundary explicit.  Every actual
  evidence use must name its original event, the final consuming use must name
  the same event, and the final consumer must actually use that evidence use.
  A use may already satisfy complete subject/closed correspondence and still
  fail this same-event final-use boundary.

  The concrete Haskell implementation remains responsible for reflecting the
  real check-event identity and the real final consuming operation into this
  model.  This proof does not modify source admission, ownership, native
  lowering, LLVM, packaging, or any Phase 1 trusted-computing-base boundary.
*)

Definition EvidenceUseEventId := nat.

Record EvidenceConsumerFinalUseModel : Type :=
  mkEvidenceConsumerFinalUseModel {
    modelFinalUseClassification : EvidenceConsumerUseClassificationModel;
    modelActualUseEvent : EvidenceConsumerId -> option EvidenceUseEventId;
    modelFinalUseEvent : EvidenceConsumerId -> option EvidenceUseEventId;
    modelFinalConsumerUsesEvidence : EvidenceConsumerId -> bool
  }.

Definition SameEventFinalEvidenceUsePreserved
  (model : EvidenceConsumerFinalUseModel) : Prop :=
  forall consumer,
    modelActualEvidenceUse
      (modelFinalUseClassification model) consumer = true ->
    exists event,
      modelActualUseEvent model consumer = Some event /\
      modelFinalUseEvent model consumer = Some event /\
      modelFinalConsumerUsesEvidence model consumer = true.

Definition CompleteEvidenceConsumerFinalUseCorrespondence
  (model : EvidenceConsumerFinalUseModel) : Prop :=
  CompleteEvidenceConsumerUseCorrespondence
    (modelFinalUseClassification model) /\
  SameEventFinalEvidenceUsePreserved model.

Theorem complete_use_correspondence_and_same_event_final_use_compose :
  forall model,
    CompleteEvidenceConsumerUseCorrespondence
      (modelFinalUseClassification model) ->
    SameEventFinalEvidenceUsePreserved model ->
    CompleteEvidenceConsumerFinalUseCorrespondence model.
Proof.
  intros model Huse Hfinal.
  split; assumption.
Qed.

(*
  Negative witness: consumer 7 is a genuine checked closed use with complete
  use correspondence, and the final consumer does use it, but the use is
  credited to event 8 instead of the original event 7.
*)
Definition wrongEventFinalUseWitness : EvidenceConsumerFinalUseModel :=
  mkEvidenceConsumerFinalUseModel
    checkedClosedActualEvidenceUseWitness
    (fun consumer => if Nat.eqb consumer 7 then Some 7 else None)
    (fun consumer => if Nat.eqb consumer 7 then Some 8 else None)
    (fun consumer => Nat.eqb consumer 7).

Theorem wrong_event_final_use_still_has_complete_use_correspondence :
  CompleteEvidenceConsumerUseCorrespondence
    (modelFinalUseClassification wrongEventFinalUseWitness).
Proof.
  exact checked_closed_actual_use_has_complete_correspondence.
Qed.

Theorem wrong_event_final_use_lacks_same_event_preservation :
  ~ SameEventFinalEvidenceUsePreserved wrongEventFinalUseWitness.
Proof.
  intro Hpreserved.
  destruct (Hpreserved 7 eq_refl) as [event [Hactual [Hfinal Hused]]].
  cbn in Hactual, Hfinal.
  inversion Hactual; subst event.
  discriminate Hfinal.
Qed.

Theorem complete_use_correspondence_alone_does_not_establish_final_use :
  CompleteEvidenceConsumerUseCorrespondence
    (modelFinalUseClassification wrongEventFinalUseWitness) /\
  ~ CompleteEvidenceConsumerFinalUseCorrespondence wrongEventFinalUseWitness.
Proof.
  split.
  - exact wrong_event_final_use_still_has_complete_use_correspondence.
  - intros [_ Hfinal].
    exact (wrong_event_final_use_lacks_same_event_preservation Hfinal).
Qed.

(*
  A second negative witness keeps the event identity correct but never records
  an actual final use.  Merely carrying matching event metadata is therefore
  insufficient.
*)
Definition omittedFinalUseWitness : EvidenceConsumerFinalUseModel :=
  mkEvidenceConsumerFinalUseModel
    checkedClosedActualEvidenceUseWitness
    (fun consumer => if Nat.eqb consumer 7 then Some 7 else None)
    (fun consumer => if Nat.eqb consumer 7 then Some 7 else None)
    (fun _ => false).

Theorem omitted_final_use_lacks_same_event_preservation :
  ~ SameEventFinalEvidenceUsePreserved omittedFinalUseWitness.
Proof.
  intro Hpreserved.
  destruct (Hpreserved 7 eq_refl) as [event [Hactual [Hfinal Hused]]].
  cbn in Hused.
  discriminate Hused.
Qed.

(* Positive checked-closed witness: the real use remains associated with event
   7 through the final consumer without inventing subject endpoints. *)
Definition checkedClosedSameEventFinalUseWitness
  : EvidenceConsumerFinalUseModel :=
  mkEvidenceConsumerFinalUseModel
    checkedClosedActualEvidenceUseWitness
    (fun consumer => if Nat.eqb consumer 7 then Some 7 else None)
    (fun consumer => if Nat.eqb consumer 7 then Some 7 else None)
    (fun consumer => Nat.eqb consumer 7).

Theorem checked_closed_same_event_final_use_is_preserved :
  SameEventFinalEvidenceUsePreserved checkedClosedSameEventFinalUseWitness.
Proof.
  intros consumer Hactual.
  cbn in Hactual.
  apply Nat.eqb_eq in Hactual.
  subst consumer.
  exists 7.
  repeat split; reflexivity.
Qed.

Theorem checked_closed_same_event_has_complete_final_correspondence :
  CompleteEvidenceConsumerFinalUseCorrespondence
    checkedClosedSameEventFinalUseWitness.
Proof.
  eapply complete_use_correspondence_and_same_event_final_use_compose.
  - exact checked_closed_actual_use_has_complete_correspondence.
  - exact checked_closed_same_event_final_use_is_preserved.
Qed.

(* Positive subject-bearing witness: the already-proved stable subject
   transport remains valid and the final use belongs to the same event. *)
Definition stableSameEventFinalUseWitness : EvidenceConsumerFinalUseModel :=
  mkEvidenceConsumerFinalUseModel
    stableClassifiedActualEvidenceUseWitness
    (fun consumer => if Nat.eqb consumer 7 then Some 7 else None)
    (fun consumer => if Nat.eqb consumer 7 then Some 7 else None)
    (fun consumer => Nat.eqb consumer 7).

Theorem stable_same_event_final_use_is_preserved :
  SameEventFinalEvidenceUsePreserved stableSameEventFinalUseWitness.
Proof.
  intros consumer Hactual.
  cbn in Hactual.
  apply Nat.eqb_eq in Hactual.
  subst consumer.
  exists 7.
  repeat split; reflexivity.
Qed.

Theorem stable_same_event_has_complete_final_correspondence :
  CompleteEvidenceConsumerFinalUseCorrespondence
    stableSameEventFinalUseWitness.
Proof.
  eapply complete_use_correspondence_and_same_event_final_use_compose.
  - exact stable_classified_actual_use_has_complete_correspondence.
  - exact stable_same_event_final_use_is_preserved.
Qed.

Theorem final_use_correspondence_distinguishes_event_reuse_and_omission :
  ~ CompleteEvidenceConsumerFinalUseCorrespondence wrongEventFinalUseWitness /\
  ~ SameEventFinalEvidenceUsePreserved omittedFinalUseWitness /\
  CompleteEvidenceConsumerFinalUseCorrespondence
    checkedClosedSameEventFinalUseWitness /\
  CompleteEvidenceConsumerFinalUseCorrespondence
    stableSameEventFinalUseWitness.
Proof.
  split.
  - intros [_ Hfinal].
    exact (wrong_event_final_use_lacks_same_event_preservation Hfinal).
  - split.
    + exact omitted_final_use_lacks_same_event_preservation.
    + split.
      * exact checked_closed_same_event_has_complete_final_correspondence.
      * exact stable_same_event_has_complete_final_correspondence.
Qed.