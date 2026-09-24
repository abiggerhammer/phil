From Stdlib Require Import Bool.Bool Arith.PeanoNat.
From Phil.Surface Require Import BranchEvidenceSupport.
From Phil.Assurance Require Import
  EvidenceConsumerSubjectTransport
  EvidenceConsumerEndpointCoverage
  EvidenceConsumerSelectionCoverage.

(*
  Defensive proof-correspondence continuation of D-RES-SUPPORT-01 /
  D-RES-TREE-01 after actual subject-bearing use selection coverage.

  EvidenceConsumerSelectionCoverage.v deliberately ranges only over actual
  subject-bearing evidence uses.  A genuinely closed evidence use need not
  acquire fabricated SubjectId endpoints, but absence from the subject-bearing
  domain cannot itself be treated as proof that the use is closed.

  This module makes the remaining classification boundary explicit.  Every
  actual evidence use must be classified either as subject-bearing or by a
  competent checked closed-use predicate.  Checked closed uses must be
  disjoint from subject-bearing uses.  Subject-bearing uses continue through
  the already-landed selection/endpoint/transport chain.

  The concrete Haskell adapter remains responsible for enumerating the actual
  evidence-use domain and implementing the checked closed-use classifier.
  This proof changes no resource-ownership rule and no Phase 1 TCB boundary.
*)

Record EvidenceConsumerUseClassificationModel : Type :=
  mkEvidenceConsumerUseClassificationModel {
    modelUseSelection : EvidenceConsumerSelectionCoverageModel;
    modelActualEvidenceUse : EvidenceConsumerId -> bool;
    modelCheckedClosedEvidenceUse : EvidenceConsumerId -> bool
  }.

Definition EvidenceConsumerUseClassificationCoverage
  (model : EvidenceConsumerUseClassificationModel) : Prop :=
  forall consumer,
    modelActualEvidenceUse model consumer = true ->
    modelActualSubjectBearingUse
      (modelUseSelection model) consumer = true \/
    modelCheckedClosedEvidenceUse model consumer = true.

Definition CheckedClosedEvidenceUseDisjointFromSubjectBearing
  (model : EvidenceConsumerUseClassificationModel) : Prop :=
  forall consumer,
    modelCheckedClosedEvidenceUse model consumer = true ->
    modelActualSubjectBearingUse
      (modelUseSelection model) consumer = false.

Definition CompleteEvidenceConsumerUseCorrespondence
  (model : EvidenceConsumerUseClassificationModel) : Prop :=
  forall consumer,
    modelActualEvidenceUse model consumer = true ->
    (exists source target,
      modelEvidenceConsumerSourceSubject
        (modelSelectionTransport (modelUseSelection model)) consumer =
        Some source /\
      modelEvidenceConsumerTargetSubject
        (modelSelectionTransport (modelUseSelection model)) consumer =
        Some target /\
      ExportSubject
        (modelTransportSurvivors
          (modelSelectionTransport (modelUseSelection model)))
        (modelTransportRebases
          (modelSelectionTransport (modelUseSelection model)))
        source
        target) \/
    (modelCheckedClosedEvidenceUse model consumer = true /\
     modelActualSubjectBearingUse
       (modelUseSelection model) consumer = false).

Theorem classified_actual_uses_receive_transport_or_checked_closed_credit :
  forall model,
    EvidenceConsumerUseClassificationCoverage model ->
    CheckedClosedEvidenceUseDisjointFromSubjectBearing model ->
    ActualUseCompleteEvidenceConsumerSubjectTransport
      (modelUseSelection model) ->
    CompleteEvidenceConsumerUseCorrespondence model.
Proof.
  intros model Hclassification HclosedDisjoint Htransport consumer Hactual.
  destruct (Hclassification consumer Hactual) as [Hsubject | Hclosed].
  - left. exact (Htransport consumer Hsubject).
  - right. split.
    + exact Hclosed.
    + exact (HclosedDisjoint consumer Hclosed).
Qed.

Definition emptySubjectBearingActualUseSelection
  : EvidenceConsumerSelectionCoverageModel :=
  mkEvidenceConsumerSelectionCoverageModel
    noSelectedSubjectBearingConsumerWitness
    (fun _ => false).

Theorem empty_subject_bearing_actual_use_domain_has_vacuous_transport :
  ActualUseCompleteEvidenceConsumerSubjectTransport
    emptySubjectBearingActualUseSelection.
Proof.
  intros consumer Hsubject.
  cbn in Hsubject. discriminate Hsubject.
Qed.

(*
  Negative witness: consumer 7 is a real evidence use but is neither present in
  the subject-bearing domain nor admitted by a checked closed-use classifier.
  Missing subject endpoints therefore do not become accidental closedness.
*)
Definition unclassifiedActualEvidenceUseWitness
  : EvidenceConsumerUseClassificationModel :=
  mkEvidenceConsumerUseClassificationModel
    emptySubjectBearingActualUseSelection
    (fun consumer => Nat.eqb consumer 7)
    (fun _ => false).

Theorem unclassified_actual_use_lacks_classification_coverage :
  ~ EvidenceConsumerUseClassificationCoverage
      unclassifiedActualEvidenceUseWitness.
Proof.
  intro Hcoverage.
  destruct (Hcoverage 7 eq_refl) as [Hsubject | Hclosed].
  - cbn in Hsubject. discriminate Hsubject.
  - cbn in Hclosed. discriminate Hclosed.
Qed.

(*
  Positive closed-use witness: consumer 7 is actual and explicitly checked
  closed.  It receives no fabricated subject endpoints and is not silently
  dropped from the actual-use inventory.
*)
Definition checkedClosedActualEvidenceUseWitness
  : EvidenceConsumerUseClassificationModel :=
  mkEvidenceConsumerUseClassificationModel
    emptySubjectBearingActualUseSelection
    (fun consumer => Nat.eqb consumer 7)
    (fun consumer => Nat.eqb consumer 7).

Theorem checked_closed_actual_use_has_classification_coverage :
  EvidenceConsumerUseClassificationCoverage
    checkedClosedActualEvidenceUseWitness.
Proof.
  intros consumer Hactual.
  right. exact Hactual.
Qed.

Theorem checked_closed_actual_use_is_disjoint_from_subject_bearing :
  CheckedClosedEvidenceUseDisjointFromSubjectBearing
    checkedClosedActualEvidenceUseWitness.
Proof.
  intros consumer Hclosed.
  reflexivity.
Qed.

Theorem checked_closed_actual_use_has_complete_correspondence :
  CompleteEvidenceConsumerUseCorrespondence
    checkedClosedActualEvidenceUseWitness.
Proof.
  eapply classified_actual_uses_receive_transport_or_checked_closed_credit.
  - exact checked_closed_actual_use_has_classification_coverage.
  - exact checked_closed_actual_use_is_disjoint_from_subject_bearing.
  - exact empty_subject_bearing_actual_use_domain_has_vacuous_transport.
Qed.

Definition stableClassifiedActualEvidenceUseWitness
  : EvidenceConsumerUseClassificationModel :=
  mkEvidenceConsumerUseClassificationModel
    stableActualUseWitness
    (fun consumer => Nat.eqb consumer 7)
    (fun _ => false).

Theorem stable_actual_use_has_classification_coverage :
  EvidenceConsumerUseClassificationCoverage
    stableClassifiedActualEvidenceUseWitness.
Proof.
  intros consumer Hactual.
  left. exact Hactual.
Qed.

Theorem stable_actual_use_closed_classification_is_disjoint :
  CheckedClosedEvidenceUseDisjointFromSubjectBearing
    stableClassifiedActualEvidenceUseWitness.
Proof.
  intros consumer Hclosed.
  cbn in Hclosed. discriminate Hclosed.
Qed.

Theorem stable_classified_actual_use_has_complete_correspondence :
  CompleteEvidenceConsumerUseCorrespondence
    stableClassifiedActualEvidenceUseWitness.
Proof.
  eapply classified_actual_uses_receive_transport_or_checked_closed_credit.
  - exact stable_actual_use_has_classification_coverage.
  - exact stable_actual_use_closed_classification_is_disjoint.
  - exact stable_actual_use_has_complete_transport.
Qed.

Definition checkedRebaseClassifiedActualEvidenceUseWitness
  : EvidenceConsumerUseClassificationModel :=
  mkEvidenceConsumerUseClassificationModel
    checkedRebaseActualUseWitness
    (fun consumer => Nat.eqb consumer 7)
    (fun _ => false).

Theorem checked_rebase_actual_use_has_classification_coverage :
  EvidenceConsumerUseClassificationCoverage
    checkedRebaseClassifiedActualEvidenceUseWitness.
Proof.
  intros consumer Hactual.
  left. exact Hactual.
Qed.

Theorem checked_rebase_actual_use_closed_classification_is_disjoint :
  CheckedClosedEvidenceUseDisjointFromSubjectBearing
    checkedRebaseClassifiedActualEvidenceUseWitness.
Proof.
  intros consumer Hclosed.
  cbn in Hclosed. discriminate Hclosed.
Qed.

Theorem checked_rebase_classified_actual_use_has_complete_correspondence :
  CompleteEvidenceConsumerUseCorrespondence
    checkedRebaseClassifiedActualEvidenceUseWitness.
Proof.
  eapply classified_actual_uses_receive_transport_or_checked_closed_credit.
  - exact checked_rebase_actual_use_has_classification_coverage.
  - exact checked_rebase_actual_use_closed_classification_is_disjoint.
  - exact checked_rebase_actual_use_has_complete_transport.
Qed.

Definition overlappingClosedAndSubjectBearingWitness
  : EvidenceConsumerUseClassificationModel :=
  mkEvidenceConsumerUseClassificationModel
    stableActualUseWitness
    (fun consumer => Nat.eqb consumer 7)
    (fun consumer => Nat.eqb consumer 7).

Theorem overlapping_closed_and_subject_bearing_classification_is_rejected :
  ~ CheckedClosedEvidenceUseDisjointFromSubjectBearing
      overlappingClosedAndSubjectBearingWitness.
Proof.
  intro Hdisjoint.
  pose proof (Hdisjoint 7 eq_refl) as HsubjectFalse.
  cbn in HsubjectFalse. discriminate HsubjectFalse.
Qed.

Theorem use_classification_distinguishes_unclassified_closed_and_subject_uses :
  ~ EvidenceConsumerUseClassificationCoverage
      unclassifiedActualEvidenceUseWitness /\
  CompleteEvidenceConsumerUseCorrespondence
    checkedClosedActualEvidenceUseWitness /\
  CompleteEvidenceConsumerUseCorrespondence
    stableClassifiedActualEvidenceUseWitness /\
  CompleteEvidenceConsumerUseCorrespondence
    checkedRebaseClassifiedActualEvidenceUseWitness /\
  ~ CheckedClosedEvidenceUseDisjointFromSubjectBearing
      overlappingClosedAndSubjectBearingWitness.
Proof.
  repeat split.
  - exact unclassified_actual_use_lacks_classification_coverage.
  - exact checked_closed_actual_use_has_complete_correspondence.
  - exact stable_classified_actual_use_has_complete_correspondence.
  - exact checked_rebase_classified_actual_use_has_complete_correspondence.
  - exact overlapping_closed_and_subject_bearing_classification_is_rejected.
Qed.
