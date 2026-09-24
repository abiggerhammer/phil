From Stdlib Require Import Lists.List Arith.PeanoNat.
From Phil.Surface Require Import BranchEvidenceSupport.
Import ListNotations.

(*
  Defensive proof-correspondence continuation of D-RES-SUPPORT-01 and
  D-RES-TREE-01.

  The durable residual-subject repair keeps enough logical typing information
  to interpret an obligation after its affine/linear owner has been consumed.
  That typing support is not itself evidence identity.  A later binding with
  the same source spelling must not become proof authority for the old logical
  subject merely because it can sort the proposition.

  BranchEvidenceSupport already models persistent logical SubjectId values and
  explicit checked rebases.  This slice applies that boundary to evidence
  consumers: every selected consumer must carry the original logical subject
  to the subject actually used by the consumer through ExportSubject.  The
  source subject may survive unchanged, or it may move only through an
  explicit checked rebase whose target survives.  Same spelling is deliberately
  absent from the model.

  Concrete Haskell reflection from binding occurrences, residual obligations,
  direct StaticByEvidence uses, certificate EvidenceFact assumptions, and
  checked rebase records into these SubjectId values remains an implementation
  correspondence premise.  This proof does not restore consumed ownership,
  grant truth to captured types, or change any Phase 1 trusted-computing-base
  boundary.
*)

Definition EvidenceConsumerId := nat.

Record EvidenceConsumerSubjectTransportModel : Type :=
  mkEvidenceConsumerSubjectTransportModel {
    modelTransportSurvivors : list SubjectId;
    modelTransportRebases : list SubjectRebase;
    modelEvidenceConsumerSelected : EvidenceConsumerId -> bool;
    modelEvidenceConsumerSourceSubject :
      EvidenceConsumerId -> option SubjectId;
    modelEvidenceConsumerTargetSubject :
      EvidenceConsumerId -> option SubjectId
  }.

Definition EvidenceConsumerSubjectTransportPreserved
  (model : EvidenceConsumerSubjectTransportModel) : Prop :=
  forall consumer source target,
    modelEvidenceConsumerSelected model consumer = true ->
    modelEvidenceConsumerSourceSubject model consumer = Some source ->
    modelEvidenceConsumerTargetSubject model consumer = Some target ->
    ExportSubject
      (modelTransportSurvivors model)
      (modelTransportRebases model)
      source
      target.

Theorem selected_evidence_consumer_requires_legal_subject_transport :
  forall model consumer source target,
    EvidenceConsumerSubjectTransportPreserved model ->
    modelEvidenceConsumerSelected model consumer = true ->
    modelEvidenceConsumerSourceSubject model consumer = Some source ->
    modelEvidenceConsumerTargetSubject model consumer = Some target ->
    ExportSubject
      (modelTransportSurvivors model)
      (modelTransportRebases model)
      source
      target.
Proof.
  intros model consumer source target Hpreserved Hselected Hsource Htarget.
  eapply Hpreserved; eauto.
Qed.

Definition sameSpellingReplacementWitness :
  EvidenceConsumerSubjectTransportModel :=
  mkEvidenceConsumerSubjectTransportModel
    [2]
    []
    (fun consumer => Nat.eqb consumer 7)
    (fun consumer => if Nat.eqb consumer 7 then Some 1 else None)
    (fun consumer => if Nat.eqb consumer 7 then Some 2 else None).

Theorem same_spelling_replacement_is_selected :
  modelEvidenceConsumerSelected sameSpellingReplacementWitness 7 = true /\
  modelEvidenceConsumerSourceSubject sameSpellingReplacementWitness 7 = Some 1 /\
  modelEvidenceConsumerTargetSubject sameSpellingReplacementWitness 7 = Some 2.
Proof.
  repeat split; reflexivity.
Qed.

Theorem same_spelling_replacement_lacks_subject_transport :
  ~ EvidenceConsumerSubjectTransportPreserved sameSpellingReplacementWitness.
Proof.
  intro Hpreserved.
  assert
    (Hselected :
      modelEvidenceConsumerSelected sameSpellingReplacementWitness 7 = true).
  { reflexivity. }
  assert
    (Hsource :
      modelEvidenceConsumerSourceSubject sameSpellingReplacementWitness 7 =
      Some 1).
  { reflexivity. }
  assert
    (Htarget :
      modelEvidenceConsumerTargetSubject sameSpellingReplacementWitness 7 =
      Some 2).
  { reflexivity. }
  pose proof
    (Hpreserved 7 1 2 Hselected Hsource Htarget)
    as Hexport.
  assert (HnotLive : ~ In 1 [2]).
  {
    simpl.
    intros [Hequal | Hfalse].
    - discriminate Hequal.
    - contradiction.
  }
  apply
    (unsupported_subject_cannot_export
      [2]
      []
      1
      2
      HnotLive
      (empty_rebase_has_no_source 1)).
  exact Hexport.
Qed.

Definition stableSubjectWitness : EvidenceConsumerSubjectTransportModel :=
  mkEvidenceConsumerSubjectTransportModel
    [1]
    []
    (fun consumer => Nat.eqb consumer 7)
    (fun consumer => if Nat.eqb consumer 7 then Some 1 else None)
    (fun consumer => if Nat.eqb consumer 7 then Some 1 else None).

Theorem stable_subject_preserves_evidence_consumer_authority :
  EvidenceConsumerSubjectTransportPreserved stableSubjectWitness.
Proof.
  intros consumer source target Hselected Hsource Htarget.
  cbn in Hselected.
  apply Nat.eqb_eq in Hselected.
  subst consumer.
  cbn in Hsource, Htarget.
  inversion Hsource; subst source.
  inversion Htarget; subst target.
  apply ExportSubject_survives.
  simpl. left. reflexivity.
Qed.

Definition checkedRebaseWitness : EvidenceConsumerSubjectTransportModel :=
  mkEvidenceConsumerSubjectTransportModel
    [2]
    [(1, 2)]
    (fun consumer => Nat.eqb consumer 7)
    (fun consumer => if Nat.eqb consumer 7 then Some 1 else None)
    (fun consumer => if Nat.eqb consumer 7 then Some 2 else None).

Theorem checked_rebase_preserves_evidence_consumer_authority :
  EvidenceConsumerSubjectTransportPreserved checkedRebaseWitness.
Proof.
  intros consumer source target Hselected Hsource Htarget.
  cbn in Hselected.
  apply Nat.eqb_eq in Hselected.
  subst consumer.
  cbn in Hsource, Htarget.
  inversion Hsource; subst source.
  inversion Htarget; subst target.
  eapply ExportSubject_rebased.
  - simpl.
    intros [Hequal | Hfalse].
    + discriminate Hequal.
    + contradiction.
  - simpl. left. reflexivity.
  - simpl. left. reflexivity.
Qed.

Theorem subject_transport_distinguishes_replacement_from_checked_rebase :
  ~ EvidenceConsumerSubjectTransportPreserved sameSpellingReplacementWitness /\
  EvidenceConsumerSubjectTransportPreserved stableSubjectWitness /\
  EvidenceConsumerSubjectTransportPreserved checkedRebaseWitness.
Proof.
  repeat split.
  - exact same_spelling_replacement_lacks_subject_transport.
  - exact stable_subject_preserves_evidence_consumer_authority.
  - exact checked_rebase_preserves_evidence_consumer_authority.
Qed.
