From Stdlib Require Import Bool.Bool Arith.PeanoNat.
From Phil.Surface Require Import BranchEvidenceSupport.
From Phil.Assurance Require Import
  EvidenceConsumerSubjectTransport EvidenceConsumerEndpointCoverage.

(*
  Defensive proof-correspondence continuation of D-RES-SUPPORT-01 /
  D-RES-TREE-01 after endpoint-total subject transport.

  EvidenceConsumerEndpointCoverage.v proves complete subject transport for the
  consumers that the adapter marks selected.  That is not sufficient if an
  actual subject-bearing evidence use can be omitted from the selected domain.
  This module makes the remaining domain-faithfulness premise explicit.

  The concrete adapter remains responsible for enumerating every actual
  subject-bearing check/evidence use, including every relevant subject
  occurrence of a multi-subject fact.  Closed facts may be excluded only by a
  competent checked classification; absence from this domain is not itself
  evidence that a use is closed.  This proof changes no resource-ownership
  rule and no Phase 1 trusted-computing-base boundary.
*)

Record EvidenceConsumerSelectionCoverageModel : Type :=
  mkEvidenceConsumerSelectionCoverageModel {
    modelSelectionTransport : EvidenceConsumerSubjectTransportModel;
    modelActualSubjectBearingUse : EvidenceConsumerId -> bool
  }.

Definition EvidenceConsumerSelectionCoverage
  (model : EvidenceConsumerSelectionCoverageModel) : Prop :=
  forall consumer,
    modelActualSubjectBearingUse model consumer = true ->
    modelEvidenceConsumerSelected
      (modelSelectionTransport model)
      consumer = true.

Definition ActualUseCompleteEvidenceConsumerSubjectTransport
  (model : EvidenceConsumerSelectionCoverageModel) : Prop :=
  forall consumer,
    modelActualSubjectBearingUse model consumer = true ->
    exists source target,
      modelEvidenceConsumerSourceSubject
        (modelSelectionTransport model) consumer = Some source /\
      modelEvidenceConsumerTargetSubject
        (modelSelectionTransport model) consumer = Some target /\
      ExportSubject
        (modelTransportSurvivors (modelSelectionTransport model))
        (modelTransportRebases (modelSelectionTransport model))
        source
        target.

Theorem selection_coverage_lifts_complete_transport_to_actual_uses :
  forall model,
    EvidenceConsumerSelectionCoverage model ->
    CompleteEvidenceConsumerSubjectTransport
      (modelSelectionTransport model) ->
    ActualUseCompleteEvidenceConsumerSubjectTransport model.
Proof.
  intros model Hcoverage Hcomplete consumer Hactual.
  pose proof (Hcoverage consumer Hactual) as Hselected.
  exact (Hcomplete consumer Hselected).
Qed.

(*
  Negative witness: consumer 7 is an actual subject-bearing use, but the
  selected-domain adapter omits every consumer.  Complete transport over the
  selected set therefore holds vacuously while the actual use has no subject
  endpoints and cannot receive transport credit.
*)
Definition omittedActualUseWitness : EvidenceConsumerSelectionCoverageModel :=
  mkEvidenceConsumerSelectionCoverageModel
    noSelectedSubjectBearingConsumerWitness
    (fun consumer => Nat.eqb consumer 7).

Theorem omitted_actual_use_still_has_vacuous_selected_complete_transport :
  CompleteEvidenceConsumerSubjectTransport
    (modelSelectionTransport omittedActualUseWitness).
Proof.
  exact empty_subject_bearing_selection_needs_no_invented_subject.
Qed.

Theorem omitted_actual_use_lacks_selection_coverage :
  ~ EvidenceConsumerSelectionCoverage omittedActualUseWitness.
Proof.
  intro Hcoverage.
  pose proof (Hcoverage 7 eq_refl) as Hselected.
  cbn in Hselected.
  discriminate.
Qed.

Theorem omitted_actual_use_lacks_actual_use_complete_transport :
  ~ ActualUseCompleteEvidenceConsumerSubjectTransport omittedActualUseWitness.
Proof.
  intro Hcomplete.
  destruct (Hcomplete 7 eq_refl)
    as [source [target [Hsource [Htarget Htransport]]]].
  cbn in Hsource.
  discriminate.
Qed.

Definition stableActualUseWitness : EvidenceConsumerSelectionCoverageModel :=
  mkEvidenceConsumerSelectionCoverageModel
    stableSubjectWitness
    (fun consumer => Nat.eqb consumer 7).

Theorem stable_actual_use_selection_is_covered :
  EvidenceConsumerSelectionCoverage stableActualUseWitness.
Proof.
  intros consumer Hactual.
  exact Hactual.
Qed.

Theorem stable_actual_use_has_complete_transport :
  ActualUseCompleteEvidenceConsumerSubjectTransport stableActualUseWitness.
Proof.
  eapply selection_coverage_lifts_complete_transport_to_actual_uses.
  - exact stable_actual_use_selection_is_covered.
  - exact stable_subject_has_complete_transport.
Qed.

Definition checkedRebaseActualUseWitness
  : EvidenceConsumerSelectionCoverageModel :=
  mkEvidenceConsumerSelectionCoverageModel
    checkedRebaseWitness
    (fun consumer => Nat.eqb consumer 7).

Theorem checked_rebase_actual_use_selection_is_covered :
  EvidenceConsumerSelectionCoverage checkedRebaseActualUseWitness.
Proof.
  intros consumer Hactual.
  exact Hactual.
Qed.

Theorem checked_rebase_actual_use_has_complete_transport :
  ActualUseCompleteEvidenceConsumerSubjectTransport
    checkedRebaseActualUseWitness.
Proof.
  eapply selection_coverage_lifts_complete_transport_to_actual_uses.
  - exact checked_rebase_actual_use_selection_is_covered.
  - exact checked_rebase_has_complete_transport.
Qed.

Theorem selected_domain_completeness_distinguishes_omission_from_covered_uses :
  CompleteEvidenceConsumerSubjectTransport
    (modelSelectionTransport omittedActualUseWitness) /\
  ~ EvidenceConsumerSelectionCoverage omittedActualUseWitness /\
  ~ ActualUseCompleteEvidenceConsumerSubjectTransport omittedActualUseWitness /\
  ActualUseCompleteEvidenceConsumerSubjectTransport stableActualUseWitness /\
  ActualUseCompleteEvidenceConsumerSubjectTransport
    checkedRebaseActualUseWitness.
Proof.
  repeat split.
  - exact omitted_actual_use_still_has_vacuous_selected_complete_transport.
  - exact omitted_actual_use_lacks_selection_coverage.
  - exact omitted_actual_use_lacks_actual_use_complete_transport.
  - exact stable_actual_use_has_complete_transport.
  - exact checked_rebase_actual_use_has_complete_transport.
Qed.
