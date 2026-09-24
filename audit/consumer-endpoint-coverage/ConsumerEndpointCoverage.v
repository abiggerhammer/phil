From Stdlib Require Import Lists.List Arith.PeanoNat.
From Phil.Surface Require Import BranchEvidenceSupport.
From Phil.Assurance Require Import EvidenceConsumerSubjectTransport.
Import ListNotations.

(* Independent audit supplement: no production definition is changed.
   A pair-preservation relation and total selection coverage are different.
   These are model witnesses, not a native acceptance demonstration. *)

Definition AuditEndpointCoverage
  (model : EvidenceConsumerSubjectTransportModel) : Prop :=
  forall consumer,
    modelEvidenceConsumerSelected model consumer = true ->
    exists source target,
      modelEvidenceConsumerSourceSubject model consumer = Some source /\
      modelEvidenceConsumerTargetSubject model consumer = Some target.

Definition AuditTotalTransport
  (model : EvidenceConsumerSubjectTransportModel) : Prop :=
  forall consumer,
    modelEvidenceConsumerSelected model consumer = true ->
    exists source target,
      modelEvidenceConsumerSourceSubject model consumer = Some source /\
      modelEvidenceConsumerTargetSubject model consumer = Some target /\
      ExportSubject (modelTransportSurvivors model)
        (modelTransportRebases model) source target.

Theorem audit_total_transport_iff_coverage_and_pair_preservation :
  forall model,
    AuditTotalTransport model <->
    AuditEndpointCoverage model /\
    EvidenceConsumerSubjectTransportPreserved model.
Proof.
  intros model. split.
  - intros Htotal. split.
    + intros consumer Hselected.
      destruct (Htotal consumer Hselected) as [source [target [Hs [Ht He]]]].
      exists source, target. split; assumption.
    + intros consumer source target Hselected Hsource Htarget.
      destruct (Htotal consumer Hselected) as [s [t [Hs [Ht He]]]].
      rewrite Hsource in Hs. inversion Hs; subst s.
      rewrite Htarget in Ht. inversion Ht; subst t.
      exact He.
  - intros [Hcoverage Hpair] consumer Hselected.
    destruct (Hcoverage consumer Hselected) as [source [target [Hs Ht]]].
    exists source, target. split.
    + exact Hs.
    + split.
      * exact Ht.
      * eapply Hpair; eauto.
Qed.

Definition auditMissingSource : EvidenceConsumerSubjectTransportModel :=
  mkEvidenceConsumerSubjectTransportModel [1] []
    (fun consumer => Nat.eqb consumer 7)
    (fun _ => None)
    (fun consumer => if Nat.eqb consumer 7 then Some 1 else None).

Definition auditMissingTarget : EvidenceConsumerSubjectTransportModel :=
  mkEvidenceConsumerSubjectTransportModel [1] []
    (fun consumer => Nat.eqb consumer 7)
    (fun consumer => if Nat.eqb consumer 7 then Some 1 else None)
    (fun _ => None).

Definition auditMissingBoth : EvidenceConsumerSubjectTransportModel :=
  mkEvidenceConsumerSubjectTransportModel [] []
    (fun consumer => Nat.eqb consumer 7)
    (fun _ => None) (fun _ => None).

Theorem audit_missing_source_still_satisfies_pair_preservation :
  EvidenceConsumerSubjectTransportPreserved auditMissingSource.
Proof.
  intros consumer source target Hselected Hsource Htarget.
  cbn in Hsource. discriminate Hsource.
Qed.

Theorem audit_missing_target_still_satisfies_pair_preservation :
  EvidenceConsumerSubjectTransportPreserved auditMissingTarget.
Proof.
  intros consumer source target Hselected Hsource Htarget.
  cbn in Htarget. discriminate Htarget.
Qed.

Theorem audit_missing_both_still_satisfies_pair_preservation :
  EvidenceConsumerSubjectTransportPreserved auditMissingBoth.
Proof.
  intros consumer source target Hselected Hsource Htarget.
  cbn in Hsource. discriminate Hsource.
Qed.

Theorem audit_selected_missing_source_lacks_total_transport :
  modelEvidenceConsumerSelected auditMissingSource 7 = true /\
  ~ AuditTotalTransport auditMissingSource.
Proof.
  split; [reflexivity |]. intro Htotal.
  destruct (Htotal 7 eq_refl) as [source [target [Hs Hrest]]].
  cbn in Hs. discriminate Hs.
Qed.

Theorem audit_selected_missing_target_lacks_total_transport :
  modelEvidenceConsumerSelected auditMissingTarget 7 = true /\
  ~ AuditTotalTransport auditMissingTarget.
Proof.
  split; [reflexivity |]. intro Htotal.
  destruct (Htotal 7 eq_refl) as [source [target [Hs [Ht He]]]].
  cbn in Ht. discriminate Ht.
Qed.

Theorem audit_selected_missing_both_lacks_total_transport :
  modelEvidenceConsumerSelected auditMissingBoth 7 = true /\
  ~ AuditTotalTransport auditMissingBoth.
Proof.
  split; [reflexivity |]. intro Htotal.
  destruct (Htotal 7 eq_refl) as [source [target [Hs Hrest]]].
  cbn in Hs. discriminate Hs.
Qed.

Theorem audit_stable_original_retains_total_transport :
  AuditTotalTransport stableSubjectWitness.
Proof.
  apply (proj2 (audit_total_transport_iff_coverage_and_pair_preservation _)).
  split.
  - intros consumer Hselected.
    cbn in Hselected. apply Nat.eqb_eq in Hselected. subst consumer.
    exists 1, 1. split; reflexivity.
  - exact stable_subject_preserves_evidence_consumer_authority.
Qed.

Theorem audit_checked_rebase_retains_total_transport :
  AuditTotalTransport checkedRebaseWitness.
Proof.
  apply (proj2 (audit_total_transport_iff_coverage_and_pair_preservation _)).
  split.
  - intros consumer Hselected.
    cbn in Hselected. apply Nat.eqb_eq in Hselected. subst consumer.
    exists 1, 2. split; reflexivity.
  - exact checked_rebase_preserves_evidence_consumer_authority.
Qed.

Theorem audit_replacement_still_lacks_total_transport :
  ~ AuditTotalTransport sameSpellingReplacementWitness.
Proof.
  intro Htotal. apply same_spelling_replacement_lacks_subject_transport.
  exact (proj2 (proj1
    (audit_total_transport_iff_coverage_and_pair_preservation _) Htotal)).
Qed.

Definition auditNoSelectedConsumer : EvidenceConsumerSubjectTransportModel :=
  mkEvidenceConsumerSubjectTransportModel [] []
    (fun _ => false) (fun _ => None) (fun _ => None).

Theorem audit_empty_selection_needs_no_invented_subject :
  AuditTotalTransport auditNoSelectedConsumer.
Proof.
  intros consumer Hselected. cbn in Hselected. discriminate Hselected.
Qed.

(* Inspect axioms for each result. No Admitted or additional axiom is used. *)
Print Assumptions audit_total_transport_iff_coverage_and_pair_preservation.
Print Assumptions audit_missing_source_still_satisfies_pair_preservation.
Print Assumptions audit_missing_target_still_satisfies_pair_preservation.
Print Assumptions audit_missing_both_still_satisfies_pair_preservation.
Print Assumptions audit_selected_missing_source_lacks_total_transport.
Print Assumptions audit_selected_missing_target_lacks_total_transport.
Print Assumptions audit_selected_missing_both_lacks_total_transport.
Print Assumptions audit_stable_original_retains_total_transport.
Print Assumptions audit_checked_rebase_retains_total_transport.
Print Assumptions audit_replacement_still_lacks_total_transport.
Print Assumptions audit_empty_selection_needs_no_invented_subject.
