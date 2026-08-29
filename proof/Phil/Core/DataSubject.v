From Stdlib Require Import Bool.Bool Arith.PeanoNat.

(*
  PHIL-DATA-SUBJECT-001 — stable semantic subject identity through
  consume-and-reconstruct updates.

  Concrete RefTerm/Proposition representation, substitution/normalization,
  lifecycle implementation correspondence, and truth of accepted succession
  relations remain explicit boundaries.  This file certifies the semantic
  dependency structure of DATA-012.
*)

Definition PropositionInstance : Type := (nat * nat)%type.

Definition instantiateProposition
  (template subjectIdentity : nat) : PropositionInstance :=
  (template, subjectIdentity).

Record DataSubject : Type := mkDataSubject {
  dataSubjectStable : bool;
  dataSubjectKind : nat;
  dataSubjectIdentity : nat;
  dataSubjectRepresentationToken : nat
}.

Record SubjectBoundEvidence : Type := mkSubjectBoundEvidence {
  subjectEvidenceReference : nat;
  subjectEvidenceTemplate : nat;
  subjectEvidenceTemplateMentionsSubject : bool;
  subjectEvidenceSubject : DataSubject
}.

Record DataSubjectUpdate : Type := mkDataSubjectUpdate {
  dataSubjectUpdatePrior : DataSubject;
  dataSubjectUpdateReplacement : DataSubject;
  dataSubjectUpdatePriorConsumed : bool;
  dataSubjectUpdateReplacementConstructed : bool
}.

Inductive DataSubjectTransportKind : Type :=
| SubjectCopyTransport
| SubjectSuccessionTransport.

Record DataSubjectTransport : Type := mkDataSubjectTransport {
  dataSubjectTransportKind : DataSubjectTransportKind;
  dataSubjectTransportRelationRevision : nat;
  dataSubjectTransportEvidenceReference : nat;
  dataSubjectTransportPriorIdentity : nat;
  dataSubjectTransportReplacementIdentity : nat;
  dataSubjectTransportSourceProposition : PropositionInstance;
  dataSubjectTransportTargetProposition : PropositionInstance;
  dataSubjectTransportAccepted : bool
}.

Definition retargetEvidence
  (evidence : SubjectBoundEvidence)
  (replacement : DataSubject) : SubjectBoundEvidence :=
  mkSubjectBoundEvidence
    (subjectEvidenceReference evidence)
    (subjectEvidenceTemplate evidence)
    (subjectEvidenceTemplateMentionsSubject evidence)
    replacement.

Definition sourceProposition
  (update : DataSubjectUpdate)
  (evidence : SubjectBoundEvidence) : PropositionInstance :=
  instantiateProposition
    (subjectEvidenceTemplate evidence)
    (dataSubjectIdentity (dataSubjectUpdatePrior update)).

Definition targetProposition
  (update : DataSubjectUpdate)
  (evidence : SubjectBoundEvidence) : PropositionInstance :=
  instantiateProposition
    (subjectEvidenceTemplate evidence)
    (dataSubjectIdentity (dataSubjectUpdateReplacement update)).

Definition TransportValid
  (update : DataSubjectUpdate)
  (evidence : SubjectBoundEvidence)
  (transport : DataSubjectTransport) : Prop :=
  dataSubjectTransportAccepted transport = true /\
  dataSubjectTransportRelationRevision transport <> 0 /\
  dataSubjectTransportEvidenceReference transport =
    subjectEvidenceReference evidence /\
  dataSubjectTransportPriorIdentity transport =
    dataSubjectIdentity (dataSubjectUpdatePrior update) /\
  dataSubjectTransportReplacementIdentity transport =
    dataSubjectIdentity (dataSubjectUpdateReplacement update) /\
  dataSubjectTransportSourceProposition transport =
    sourceProposition update evidence /\
  dataSubjectTransportTargetProposition transport =
    targetProposition update evidence.

Inductive CheckedDataSubjectUpdate
  : DataSubjectUpdate -> SubjectBoundEvidence ->
    option DataSubjectTransport -> SubjectBoundEvidence -> Prop :=
| CheckedSameSubject :
    forall update evidence,
      dataSubjectUpdatePriorConsumed update = true ->
      dataSubjectUpdateReplacementConstructed update = true ->
      dataSubjectStable (dataSubjectUpdatePrior update) = true ->
      dataSubjectStable (dataSubjectUpdateReplacement update) = true ->
      dataSubjectKind (dataSubjectUpdatePrior update) =
        dataSubjectKind (dataSubjectUpdateReplacement update) ->
      subjectEvidenceTemplateMentionsSubject evidence = true ->
      dataSubjectStable (subjectEvidenceSubject evidence) = true ->
      dataSubjectKind (subjectEvidenceSubject evidence) =
        dataSubjectKind (dataSubjectUpdatePrior update) ->
      dataSubjectIdentity (subjectEvidenceSubject evidence) =
        dataSubjectIdentity (dataSubjectUpdatePrior update) ->
      dataSubjectIdentity (dataSubjectUpdatePrior update) =
        dataSubjectIdentity (dataSubjectUpdateReplacement update) ->
      CheckedDataSubjectUpdate
        update evidence None
        (retargetEvidence evidence (dataSubjectUpdateReplacement update))
| CheckedChangedSubject :
    forall update evidence transport,
      dataSubjectUpdatePriorConsumed update = true ->
      dataSubjectUpdateReplacementConstructed update = true ->
      dataSubjectStable (dataSubjectUpdatePrior update) = true ->
      dataSubjectStable (dataSubjectUpdateReplacement update) = true ->
      dataSubjectKind (dataSubjectUpdatePrior update) =
        dataSubjectKind (dataSubjectUpdateReplacement update) ->
      subjectEvidenceTemplateMentionsSubject evidence = true ->
      dataSubjectStable (subjectEvidenceSubject evidence) = true ->
      dataSubjectKind (subjectEvidenceSubject evidence) =
        dataSubjectKind (dataSubjectUpdatePrior update) ->
      dataSubjectIdentity (subjectEvidenceSubject evidence) =
        dataSubjectIdentity (dataSubjectUpdatePrior update) ->
      dataSubjectIdentity (dataSubjectUpdatePrior update) <>
        dataSubjectIdentity (dataSubjectUpdateReplacement update) ->
      TransportValid update evidence transport ->
      CheckedDataSubjectUpdate
        update evidence (Some transport)
        (retargetEvidence evidence (dataSubjectUpdateReplacement update)).

Theorem checked_update_requires_lifecycle_accounting :
  forall update evidence transport resultEvidence,
    CheckedDataSubjectUpdate update evidence transport resultEvidence ->
    dataSubjectUpdatePriorConsumed update = true /\
    dataSubjectUpdateReplacementConstructed update = true.
Proof.
  intros update evidence transport resultEvidence Hchecked.
  inversion Hchecked; subst; split; assumption.
Qed.

Theorem checked_update_requires_stable_compatible_subjects :
  forall update evidence transport resultEvidence,
    CheckedDataSubjectUpdate update evidence transport resultEvidence ->
    dataSubjectStable (dataSubjectUpdatePrior update) = true /\
    dataSubjectStable (dataSubjectUpdateReplacement update) = true /\
    dataSubjectKind (dataSubjectUpdatePrior update) =
      dataSubjectKind (dataSubjectUpdateReplacement update).
Proof.
  intros update evidence transport resultEvidence Hchecked.
  inversion Hchecked; subst; repeat split; assumption.
Qed.

Theorem checked_update_requires_subject_bound_evidence :
  forall update evidence transport resultEvidence,
    CheckedDataSubjectUpdate update evidence transport resultEvidence ->
    subjectEvidenceTemplateMentionsSubject evidence = true /\
    dataSubjectIdentity (subjectEvidenceSubject evidence) =
      dataSubjectIdentity (dataSubjectUpdatePrior update).
Proof.
  intros update evidence transport resultEvidence Hchecked.
  inversion Hchecked; subst; split; assumption.
Qed.

Theorem checked_result_targets_exact_replacement :
  forall update evidence transport resultEvidence,
    CheckedDataSubjectUpdate update evidence transport resultEvidence ->
    subjectEvidenceReference resultEvidence = subjectEvidenceReference evidence /\
    subjectEvidenceTemplate resultEvidence = subjectEvidenceTemplate evidence /\
    subjectEvidenceSubject resultEvidence = dataSubjectUpdateReplacement update.
Proof.
  intros update evidence transport resultEvidence Hchecked.
  inversion Hchecked; subst; simpl; repeat split; reflexivity.
Qed.

Theorem distinct_subject_without_transport_rejects :
  forall update evidence resultEvidence,
    dataSubjectIdentity (dataSubjectUpdatePrior update) <>
      dataSubjectIdentity (dataSubjectUpdateReplacement update) ->
    ~ CheckedDataSubjectUpdate update evidence None resultEvidence.
Proof.
  intros update evidence resultEvidence Hdistinct Hchecked.
  inversion Hchecked; subst.
  contradiction.
Qed.

Corollary same_kind_does_not_authorize_subject_retarget :
  forall update evidence resultEvidence,
    dataSubjectKind (dataSubjectUpdatePrior update) =
      dataSubjectKind (dataSubjectUpdateReplacement update) ->
    dataSubjectIdentity (dataSubjectUpdatePrior update) <>
      dataSubjectIdentity (dataSubjectUpdateReplacement update) ->
    ~ CheckedDataSubjectUpdate update evidence None resultEvidence.
Proof.
  intros update evidence resultEvidence Hkind Hdistinct.
  apply distinct_subject_without_transport_rejects.
  exact Hdistinct.
Qed.

Corollary matching_representation_token_does_not_authorize_subject_retarget :
  forall update evidence resultEvidence,
    dataSubjectRepresentationToken (dataSubjectUpdatePrior update) =
      dataSubjectRepresentationToken (dataSubjectUpdateReplacement update) ->
    dataSubjectIdentity (dataSubjectUpdatePrior update) <>
      dataSubjectIdentity (dataSubjectUpdateReplacement update) ->
    ~ CheckedDataSubjectUpdate update evidence None resultEvidence.
Proof.
  intros update evidence resultEvidence Hrepresentation Hdistinct.
  apply distinct_subject_without_transport_rejects.
  exact Hdistinct.
Qed.

Theorem unchanged_subject_rejects_spurious_transport :
  forall update evidence transport resultEvidence,
    dataSubjectIdentity (dataSubjectUpdatePrior update) =
      dataSubjectIdentity (dataSubjectUpdateReplacement update) ->
    ~ CheckedDataSubjectUpdate update evidence (Some transport) resultEvidence.
Proof.
  intros update evidence transport resultEvidence Hequal Hchecked.
  inversion Hchecked; subst.
  contradiction.
Qed.

Theorem changed_subject_requires_exact_transport :
  forall update evidence maybeTransport resultEvidence,
    CheckedDataSubjectUpdate update evidence maybeTransport resultEvidence ->
    dataSubjectIdentity (dataSubjectUpdatePrior update) <>
      dataSubjectIdentity (dataSubjectUpdateReplacement update) ->
    exists transport,
      maybeTransport = Some transport /\
      dataSubjectTransportAccepted transport = true /\
      dataSubjectTransportRelationRevision transport <> 0 /\
      dataSubjectTransportEvidenceReference transport =
        subjectEvidenceReference evidence /\
      dataSubjectTransportPriorIdentity transport =
        dataSubjectIdentity (dataSubjectUpdatePrior update) /\
      dataSubjectTransportReplacementIdentity transport =
        dataSubjectIdentity (dataSubjectUpdateReplacement update) /\
      dataSubjectTransportSourceProposition transport =
        sourceProposition update evidence /\
      dataSubjectTransportTargetProposition transport =
        targetProposition update evidence.
Proof.
  intros update evidence maybeTransport resultEvidence Hchecked Hdistinct.
  inversion Hchecked; subst.
  - contradiction.
  - exists transport0.
    split.
    + reflexivity.
    + unfold TransportValid in H10.
      exact H10.
Qed.

Theorem same_subject_representation_change_is_nonsemantic :
  forall update evidence,
    dataSubjectUpdatePriorConsumed update = true ->
    dataSubjectUpdateReplacementConstructed update = true ->
    dataSubjectStable (dataSubjectUpdatePrior update) = true ->
    dataSubjectStable (dataSubjectUpdateReplacement update) = true ->
    dataSubjectKind (dataSubjectUpdatePrior update) =
      dataSubjectKind (dataSubjectUpdateReplacement update) ->
    subjectEvidenceTemplateMentionsSubject evidence = true ->
    dataSubjectStable (subjectEvidenceSubject evidence) = true ->
    dataSubjectKind (subjectEvidenceSubject evidence) =
      dataSubjectKind (dataSubjectUpdatePrior update) ->
    dataSubjectIdentity (subjectEvidenceSubject evidence) =
      dataSubjectIdentity (dataSubjectUpdatePrior update) ->
    dataSubjectIdentity (dataSubjectUpdatePrior update) =
      dataSubjectIdentity (dataSubjectUpdateReplacement update) ->
    CheckedDataSubjectUpdate
      update evidence None
      (retargetEvidence evidence (dataSubjectUpdateReplacement update)).
Proof.
  intros update evidence Hconsumed Hconstructed HpriorStable HreplacementStable
    Hkind Hmentions HevidenceStable HevidenceKind HevidenceIdentity Hsame.
  constructor; assumption.
Qed.
