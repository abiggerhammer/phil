From Stdlib Require Import Lists.List Arith.PeanoNat.
From Phil.Surface Require Import BranchEvidenceSupport.
From Phil.Assurance Require Import EvidenceConsumerSubjectTransport.
Import ListNotations.

(*
  Defensive proof-correspondence continuation of D-RES-SUPPORT-01 /
  D-RES-TREE-01 after the evidence-consumer subject-transport boundary.

  EvidenceConsumerSubjectTransportPreserved is intentionally a pair theorem:
  once both source and target logical SubjectId values are present for a
  selected consumer, they must be related by ExportSubject.  It does not by
  itself require those lookups to succeed.  This module supplies the missing
  domain/endpoint-totality factor without changing the existing theorem.

  The selected domain here is the subject-bearing evidence-consumer domain.
  A genuinely closed fact can remain outside that domain only through a
  competent checked classification in the concrete adapter; an unmapped
  subject-bearing use must not be represented merely by absent endpoints.

  Concrete Haskell enumeration of all relevant consumer/subject occurrences,
  closed-fact classification, and reflection into stable SubjectId values
  remain implementation-correspondence premises.  Logical subject survival is
  not resource ownership and this proof changes no Phase 1 TCB boundary.
*)

Definition EvidenceConsumerEndpointCoverage
  (model : EvidenceConsumerSubjectTransportModel) : Prop :=
  forall consumer,
    modelEvidenceConsumerSelected model consumer = true ->
    exists source target,
      modelEvidenceConsumerSourceSubject model consumer = Some source /\
      modelEvidenceConsumerTargetSubject model consumer = Some target.

Definition CompleteEvidenceConsumerSubjectTransport
  (model : EvidenceConsumerSubjectTransportModel) : Prop :=
  forall consumer,
    modelEvidenceConsumerSelected model consumer = true ->
    exists source target,
      modelEvidenceConsumerSourceSubject model consumer = Some source /\
      modelEvidenceConsumerTargetSubject model consumer = Some target /\
      ExportSubject
        (modelTransportSurvivors model)
        (modelTransportRebases model)
        source
        target.

Theorem complete_transport_iff_endpoint_coverage_and_pair_preservation :
  forall model,
    CompleteEvidenceConsumerSubjectTransport model <->
    EvidenceConsumerEndpointCoverage model /\
    EvidenceConsumerSubjectTransportPreserved model.
Proof.
  intros model. split.
  - intros Hcomplete. split.
    + intros consumer Hselected.
      destruct (Hcomplete consumer Hselected)
        as [source [target [Hsource [Htarget Htransport]]]].
      exists source, target. split; assumption.
    + intros consumer source target Hselected Hsource Htarget.
      destruct (Hcomplete consumer Hselected)
        as [actualSource [actualTarget [HactualSource [HactualTarget Htransport]]]].
      rewrite Hsource in HactualSource.
      inversion HactualSource; subst actualSource.
      rewrite Htarget in HactualTarget.
      inversion HactualTarget; subst actualTarget.
      exact Htransport.
  - intros [Hcoverage Hpair] consumer Hselected.
    destruct (Hcoverage consumer Hselected)
      as [source [target [Hsource Htarget]]].
    exists source, target. split.
    + exact Hsource.
    + split.
      * exact Htarget.
      * eapply Hpair; eauto.
Qed.

Definition missingSourceEndpointWitness :
  EvidenceConsumerSubjectTransportModel :=
  mkEvidenceConsumerSubjectTransportModel
    [1]
    []
    (fun consumer => Nat.eqb consumer 7)
    (fun _ => None)
    (fun consumer => if Nat.eqb consumer 7 then Some 1 else None).

Definition missingTargetEndpointWitness :
  EvidenceConsumerSubjectTransportModel :=
  mkEvidenceConsumerSubjectTransportModel
    [1]
    []
    (fun consumer => Nat.eqb consumer 7)
    (fun consumer => if Nat.eqb consumer 7 then Some 1 else None)
    (fun _ => None).

Definition missingBothEndpointsWitness :
  EvidenceConsumerSubjectTransportModel :=
  mkEvidenceConsumerSubjectTransportModel
    []
    []
    (fun consumer => Nat.eqb consumer 7)
    (fun _ => None)
    (fun _ => None).

Theorem missing_source_can_satisfy_pair_preservation_vacuously :
  EvidenceConsumerSubjectTransportPreserved missingSourceEndpointWitness.
Proof.
  intros consumer source target Hselected Hsource Htarget.
  cbn in Hsource. discriminate Hsource.
Qed.

Theorem missing_target_can_satisfy_pair_preservation_vacuously :
  EvidenceConsumerSubjectTransportPreserved missingTargetEndpointWitness.
Proof.
  intros consumer source target Hselected Hsource Htarget.
  cbn in Htarget. discriminate Htarget.
Qed.

Theorem missing_both_can_satisfy_pair_preservation_vacuously :
  EvidenceConsumerSubjectTransportPreserved missingBothEndpointsWitness.
Proof.
  intros consumer source target Hselected Hsource Htarget.
  cbn in Hsource. discriminate Hsource.
Qed.

Theorem selected_missing_source_lacks_complete_transport :
  modelEvidenceConsumerSelected missingSourceEndpointWitness 7 = true /\
  ~ CompleteEvidenceConsumerSubjectTransport missingSourceEndpointWitness.
Proof.
  split; [reflexivity |].
  intro Hcomplete.
  destruct (Hcomplete 7 eq_refl)
    as [source [target [Hsource Hrest]]].
  cbn in Hsource. discriminate Hsource.
Qed.

Theorem selected_missing_target_lacks_complete_transport :
  modelEvidenceConsumerSelected missingTargetEndpointWitness 7 = true /\
  ~ CompleteEvidenceConsumerSubjectTransport missingTargetEndpointWitness.
Proof.
  split; [reflexivity |].
  intro Hcomplete.
  destruct (Hcomplete 7 eq_refl)
    as [source [target [Hsource [Htarget Htransport]]]].
  cbn in Htarget. discriminate Htarget.
Qed.

Theorem selected_missing_both_lacks_complete_transport :
  modelEvidenceConsumerSelected missingBothEndpointsWitness 7 = true /\
  ~ CompleteEvidenceConsumerSubjectTransport missingBothEndpointsWitness.
Proof.
  split; [reflexivity |].
  intro Hcomplete.
  destruct (Hcomplete 7 eq_refl)
    as [source [target [Hsource Hrest]]].
  cbn in Hsource. discriminate Hsource.
Qed.

Theorem stable_subject_has_complete_transport :
  CompleteEvidenceConsumerSubjectTransport stableSubjectWitness.
Proof.
  apply
    (proj2
      (complete_transport_iff_endpoint_coverage_and_pair_preservation
        stableSubjectWitness)).
  split.
  - intros consumer Hselected.
    cbn in Hselected.
    apply Nat.eqb_eq in Hselected.
    subst consumer.
    exists 1, 1. split; reflexivity.
  - exact stable_subject_preserves_evidence_consumer_authority.
Qed.

Theorem checked_rebase_has_complete_transport :
  CompleteEvidenceConsumerSubjectTransport checkedRebaseWitness.
Proof.
  apply
    (proj2
      (complete_transport_iff_endpoint_coverage_and_pair_preservation
        checkedRebaseWitness)).
  split.
  - intros consumer Hselected.
    cbn in Hselected.
    apply Nat.eqb_eq in Hselected.
    subst consumer.
    exists 1, 2. split; reflexivity.
  - exact checked_rebase_preserves_evidence_consumer_authority.
Qed.

Theorem unrelated_replacement_still_lacks_complete_transport :
  ~ CompleteEvidenceConsumerSubjectTransport sameSpellingReplacementWitness.
Proof.
  intro Hcomplete.
  apply same_spelling_replacement_lacks_subject_transport.
  exact
    (proj2
      (proj1
        (complete_transport_iff_endpoint_coverage_and_pair_preservation
          sameSpellingReplacementWitness)
        Hcomplete)).
Qed.

Definition noSelectedSubjectBearingConsumerWitness :
  EvidenceConsumerSubjectTransportModel :=
  mkEvidenceConsumerSubjectTransportModel
    []
    []
    (fun _ => false)
    (fun _ => None)
    (fun _ => None).

Theorem empty_subject_bearing_selection_needs_no_invented_subject :
  CompleteEvidenceConsumerSubjectTransport
    noSelectedSubjectBearingConsumerWitness.
Proof.
  intros consumer Hselected.
  cbn in Hselected. discriminate Hselected.
Qed.
