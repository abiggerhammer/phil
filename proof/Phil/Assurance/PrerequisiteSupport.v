From Stdlib Require Import Bool.Bool Arith.PeanoNat.

(*
  PHIL-AUD-PREREQUISITE-SUPPORT-001 — certificate prerequisite support
  must remain distinct from revision-generation provenance.

  Native correspondence:

  - Phil.Core.Discharge introduces child obligations for focused prerequisites
    and makes locally established children available to the parent decision
    procedure as PrerequisiteFact child-id assumptions.
  - StaticByCertificate retains the DecisionCertificate used for the parent.
  - Phil.Assurance.Handoff records each child revision as generated_from the
    parent revision.
  - VerificationObligationGraph defines an edge (A,B) to mean A depends on B.
  - buildVerificationRevisionGraph currently projects revisionGeneratedFrom
    directly in the stored child -> parent direction.

  This model fixes the semantic direction needed by certificate support:
  when a parent certificate uses a child prerequisite, the parent's evidence
  must depend on that child obligation.  Historical generated_from lineage is
  independent provenance and cannot substitute for that support edge.

  Concrete ObligationId/RevisionId translation, DecisionCertificate traversal,
  Haskell Map/Set construction, and EvidenceEntry serialization remain explicit
  implementation-correspondence boundaries.
*)

Definition SupportRevisionId := nat.
Definition SupportEvidenceId := nat.

Record PrerequisiteSupportModel : Type := mkPrerequisiteSupportModel {
  modelResolvedPrerequisite :
    SupportRevisionId -> SupportRevisionId -> bool;
  modelGeneratedFrom :
    SupportRevisionId -> SupportRevisionId -> bool;
  modelEvidenceRevision :
    SupportEvidenceId -> SupportRevisionId;
  modelCertificatePrerequisite :
    SupportEvidenceId -> SupportRevisionId -> bool;
  modelEvidenceDependsOn :
    SupportEvidenceId -> SupportRevisionId -> bool
}.

Definition CertificateSupportPreserved
  (model : PrerequisiteSupportModel) : Prop :=
  forall evidence prerequisite,
    modelCertificatePrerequisite model evidence prerequisite = true ->
    modelEvidenceDependsOn model evidence prerequisite = true.

Definition EvidenceTargetsParent
  (model : PrerequisiteSupportModel)
  (evidence : SupportEvidenceId)
  (parent : SupportRevisionId) : Prop :=
  modelEvidenceRevision model evidence = parent.

Theorem certificate_prerequisite_requires_explicit_support :
  forall model evidence prerequisite,
    CertificateSupportPreserved model ->
    modelCertificatePrerequisite model evidence prerequisite = true ->
    modelEvidenceDependsOn model evidence prerequisite = true.
Proof.
  intros model evidence prerequisite Hpreserved Hused.
  eapply Hpreserved.
  exact Hused.
Qed.

Theorem resolved_parent_prerequisite_direction_is_parent_to_child :
  forall model parent child,
    modelResolvedPrerequisite model parent child = true ->
    modelResolvedPrerequisite model parent child = true.
Proof.
  intros model parent child Hprerequisite.
  exact Hprerequisite.
Qed.

(*
  Concrete two-revision witness.

    parent revision      = 1
    child prerequisite   = 0
    parent evidence      = 10

  The resolved semantic relation is parent -> child.
  The handoff provenance relation is child generated_from parent.
  Projecting generated_from as though it were semantic dependency therefore
  provides child -> parent, not the support edge required by the certificate.
*)
Definition ReversedLineageWitness : PrerequisiteSupportModel :=
  mkPrerequisiteSupportModel
    (fun parent child =>
      andb (Nat.eqb parent 1) (Nat.eqb child 0))
    (fun child parent =>
      andb (Nat.eqb child 0) (Nat.eqb parent 1))
    (fun evidence =>
      if Nat.eqb evidence 10 then 1 else 0)
    (fun evidence prerequisite =>
      andb (Nat.eqb evidence 10) (Nat.eqb prerequisite 0))
    (fun _ _ => false).

Theorem witness_parent_has_child_prerequisite :
  modelResolvedPrerequisite ReversedLineageWitness 1 0 = true.
Proof.
  reflexivity.
Qed.

Theorem witness_child_records_parent_provenance :
  modelGeneratedFrom ReversedLineageWitness 0 1 = true.
Proof.
  reflexivity.
Qed.

Theorem witness_parent_does_not_record_child_as_generated_from :
  modelGeneratedFrom ReversedLineageWitness 1 0 = false.
Proof.
  reflexivity.
Qed.

Theorem witness_certificate_targets_parent :
  EvidenceTargetsParent ReversedLineageWitness 10 1.
Proof.
  reflexivity.
Qed.

Theorem witness_certificate_uses_child_prerequisite :
  modelCertificatePrerequisite ReversedLineageWitness 10 0 = true.
Proof.
  reflexivity.
Qed.

Theorem generated_from_projection_cannot_supply_parent_support :
  modelGeneratedFrom ReversedLineageWitness 0 1 = true /\
  modelGeneratedFrom ReversedLineageWitness 1 0 = false /\
  modelCertificatePrerequisite ReversedLineageWitness 10 0 = true /\
  modelEvidenceDependsOn ReversedLineageWitness 10 0 = false.
Proof.
  repeat split; reflexivity.
Qed.

Theorem lineage_only_witness_fails_certificate_support_preservation :
  ~ CertificateSupportPreserved ReversedLineageWitness.
Proof.
  intro Hpreserved.
  pose proof
    (certificate_prerequisite_requires_explicit_support
      ReversedLineageWitness 10 0
      Hpreserved
      witness_certificate_uses_child_prerequisite)
    as Hsupport.
  simpl in Hsupport.
  discriminate.
Qed.

Definition ExplicitSupportWitness : PrerequisiteSupportModel :=
  mkPrerequisiteSupportModel
    (fun parent child =>
      andb (Nat.eqb parent 1) (Nat.eqb child 0))
    (fun child parent =>
      andb (Nat.eqb child 0) (Nat.eqb parent 1))
    (fun evidence =>
      if Nat.eqb evidence 10 then 1 else 0)
    (fun evidence prerequisite =>
      andb (Nat.eqb evidence 10) (Nat.eqb prerequisite 0))
    (fun evidence prerequisite =>
      andb (Nat.eqb evidence 10) (Nat.eqb prerequisite 0)).

Theorem explicit_support_witness_preserves_certificate_support :
  CertificateSupportPreserved ExplicitSupportWitness.
Proof.
  intros evidence prerequisite Hused.
  exact Hused.
Qed.

Theorem explicit_support_does_not_erase_generation_provenance :
  modelGeneratedFrom ExplicitSupportWitness 0 1 = true /\
  modelEvidenceDependsOn ExplicitSupportWitness 10 0 = true.
Proof.
  split; reflexivity.
Qed.
