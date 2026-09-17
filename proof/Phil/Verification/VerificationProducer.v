From Stdlib Require Import Lists.List.

Import ListNotations.

From Phil.Verification Require Import VerificationWorkflow.

(*
  PHIL-VERIFY-PRODUCER-001 — replaceable proof production, competent evidence
  checking, unresolved failure semantics, and evidence-lineage separation.

  This proof imports the already-Certified PHIL-VERIFY-WORKFLOW-001 target
  boundary.  The obligation graph/revision to be discharged is therefore fixed
  before any replaceable producer runs.

  The producer may propose an artifact, time out, return unknown, fail, or
  refuse.  None of those producer outcomes is itself proof authority.  Accepted
  evidence exists only after the proposal is bound to the exact target,
  supported format, exact semantic subjects/contexts and proposition, and the
  competent checker accepts the exact certificate.  Producer/checker/artifact
  lineage remains separate from semantic discharge-target identity.

  Concrete Text/Digest/RevisionId identity, proposition rendering,
  DecisionCertificate checking, CheckState/SolverAssumption semantics, and
  Haskell list normalization remain explicit predecessor/representation
  boundaries.
*)

Definition GraphRevision := nat.
Definition ObligationRevision := nat.
Definition ProducerIdentity := nat.
Definition CheckerIdentity := nat.
Definition EvidenceFormat := nat.
Definition SemanticIdentity := nat.
Definition PropositionIdentity := nat.
Definition CertificateIdentity := nat.

Record ProofDischargeTarget : Type := mkProofDischargeTarget {
  proofTargetGraphRevision : GraphRevision;
  proofTargetObligationRevision : ObligationRevision
}.

Record ProofProposal : Type := mkProofProposal {
  proofProposalTarget : ProofDischargeTarget;
  proofProposalProducer : ProducerIdentity;
  proofProposalFormat : EvidenceFormat;
  proofProposalSubjects : list SemanticIdentity;
  proofProposalContexts : list SemanticIdentity;
  proofProposalProposition : PropositionIdentity;
  proofProposalCertificate : CertificateIdentity
}.

Record ProofCompetenceExpectation : Type := mkProofCompetenceExpectation {
  proofExpectedTarget : ProofDischargeTarget;
  proofExpectedFormat : EvidenceFormat;
  proofExpectedSubjects : list SemanticIdentity;
  proofExpectedContexts : list SemanticIdentity;
  proofExpectedProposition : PropositionIdentity
}.

Definition ProposalCompetent
  (expected : ProofCompetenceExpectation)
  (proposal : ProofProposal) : Prop :=
  proofProposalTarget proposal = proofExpectedTarget expected /\
  proofProposalFormat proposal = proofExpectedFormat expected /\
  SameMembers (proofProposalSubjects proposal) (proofExpectedSubjects expected) /\
  SameMembers (proofProposalContexts proposal) (proofExpectedContexts expected) /\
  proofProposalProposition proposal = proofExpectedProposition expected.

Record CheckedProofEvidence : Type := mkCheckedProofEvidence {
  checkedProofTarget : ProofDischargeTarget;
  checkedProofProducer : ProducerIdentity;
  checkedProofChecker : CheckerIdentity;
  checkedProofFormat : EvidenceFormat;
  checkedProofSubjects : list SemanticIdentity;
  checkedProofContexts : list SemanticIdentity;
  checkedProofProposition : PropositionIdentity;
  checkedProofCertificate : CertificateIdentity
}.

Definition CheckedEvidenceValid
  (checkerAccepts : PropositionIdentity -> CertificateIdentity -> Prop)
  (expected : ProofCompetenceExpectation)
  (checker : CheckerIdentity)
  (proposal : ProofProposal)
  (evidence : CheckedProofEvidence) : Prop :=
  ProposalCompetent expected proposal /\
  checkerAccepts
    (proofProposalProposition proposal)
    (proofProposalCertificate proposal) /\
  checkedProofTarget evidence = proofProposalTarget proposal /\
  checkedProofProducer evidence = proofProposalProducer proposal /\
  checkedProofChecker evidence = checker /\
  checkedProofFormat evidence = proofProposalFormat proposal /\
  SameMembers (checkedProofSubjects evidence) (proofProposalSubjects proposal) /\
  SameMembers (checkedProofContexts evidence) (proofProposalContexts proposal) /\
  checkedProofProposition evidence = proofProposalProposition proposal /\
  checkedProofCertificate evidence = proofProposalCertificate proposal.

Theorem checked_evidence_requires_exact_discharge_target :
  forall checkerAccepts expected checker proposal evidence,
    CheckedEvidenceValid checkerAccepts expected checker proposal evidence ->
    checkedProofTarget evidence = proofExpectedTarget expected.
Proof.
  intros checkerAccepts expected checker proposal evidence Hvalid.
  destruct Hvalid as
    [Hcompetent [_ [Htarget _]]].
  destruct Hcompetent as [Hexpected _].
  rewrite Htarget.
  exact Hexpected.
Qed.

Theorem checked_evidence_requires_competent_checker_acceptance :
  forall checkerAccepts expected checker proposal evidence,
    CheckedEvidenceValid checkerAccepts expected checker proposal evidence ->
    checkerAccepts
      (proofProposalProposition proposal)
      (proofProposalCertificate proposal).
Proof.
  intros checkerAccepts expected checker proposal evidence Hvalid.
  destruct Hvalid as [_ [Hchecker _]].
  exact Hchecker.
Qed.

Theorem producer_success_alone_is_not_evidence_authority :
  forall checkerAccepts expected checker proposal evidence,
    ~ checkerAccepts
        (proofProposalProposition proposal)
        (proofProposalCertificate proposal) ->
    ~ CheckedEvidenceValid checkerAccepts expected checker proposal evidence.
Proof.
  intros checkerAccepts expected checker proposal evidence Hrejected Hvalid.
  apply Hrejected.
  eapply checked_evidence_requires_competent_checker_acceptance.
  exact Hvalid.
Qed.

Theorem incompetent_proposal_cannot_create_checked_evidence :
  forall checkerAccepts expected checker proposal evidence,
    ~ ProposalCompetent expected proposal ->
    ~ CheckedEvidenceValid checkerAccepts expected checker proposal evidence.
Proof.
  intros checkerAccepts expected checker proposal evidence Hincompetent Hvalid.
  apply Hincompetent.
  exact (proj1 Hvalid).
Qed.

Theorem checked_evidence_preserves_exact_format :
  forall checkerAccepts expected checker proposal evidence,
    CheckedEvidenceValid checkerAccepts expected checker proposal evidence ->
    checkedProofFormat evidence = proofExpectedFormat expected.
Proof.
  intros checkerAccepts expected checker proposal evidence Hvalid.
  destruct Hvalid as
    [Hcompetent [_ [_ [_ [_ [Hformat _]]]]]].
  destruct Hcompetent as [_ [HexpectedFormat _]].
  rewrite Hformat.
  exact HexpectedFormat.
Qed.

Theorem checked_evidence_preserves_exact_subject_domain :
  forall checkerAccepts expected checker proposal evidence,
    CheckedEvidenceValid checkerAccepts expected checker proposal evidence ->
    SameMembers (checkedProofSubjects evidence) (proofExpectedSubjects expected).
Proof.
  intros checkerAccepts expected checker proposal evidence Hvalid.
  destruct Hvalid as
    [Hcompetent [_ [_ [_ [_ [_ [Hsubjects _]]]]]]].
  destruct Hcompetent as [_ [_ [HexpectedSubjects _]]].
  eapply same_members_transitive; eauto.
Qed.

Theorem checked_evidence_preserves_exact_context_domain :
  forall checkerAccepts expected checker proposal evidence,
    CheckedEvidenceValid checkerAccepts expected checker proposal evidence ->
    SameMembers (checkedProofContexts evidence) (proofExpectedContexts expected).
Proof.
  intros checkerAccepts expected checker proposal evidence Hvalid.
  destruct Hvalid as
    [Hcompetent [_ [_ [_ [_ [_ [_ [Hcontexts _]]]]]]]].
  destruct Hcompetent as [_ [_ [_ [HexpectedContexts _]]]].
  eapply same_members_transitive; eauto.
Qed.

Inductive ProofProducerFailure : Type :=
| ProducerTimedOut
| ProducerReturnedUnknown
| ProducerFailed
| ProducerRefused
| ProducerArtifactRejected.

Record UnresolvedProofAttempt : Type := mkUnresolvedProofAttempt {
  unresolvedProofTarget : ProofDischargeTarget;
  unresolvedProofProducer : ProducerIdentity;
  unresolvedProofFailure : ProofProducerFailure
}.

Inductive ProofAttemptSemanticResult : Type :=
| ProofAttemptAccepted (evidence : CheckedProofEvidence)
| ProofAttemptUnresolved (attempt : UnresolvedProofAttempt).

Definition unresolvedProducerResult
  (target : ProofDischargeTarget)
  (producer : ProducerIdentity)
  (failure : ProofProducerFailure) : ProofAttemptSemanticResult :=
  ProofAttemptUnresolved
    (mkUnresolvedProofAttempt target producer failure).

Theorem producer_failure_remains_unresolved :
  forall target producer failure,
    exists attempt,
      unresolvedProducerResult target producer failure =
        ProofAttemptUnresolved attempt /\
      unresolvedProofTarget attempt = target /\
      unresolvedProofProducer attempt = producer /\
      unresolvedProofFailure attempt = failure.
Proof.
  intros target producer failure.
  exists (mkUnresolvedProofAttempt target producer failure).
  repeat split; reflexivity.
Qed.

Theorem producer_failure_never_manufactures_checked_evidence :
  forall target producer failure evidence,
    unresolvedProducerResult target producer failure <>
      ProofAttemptAccepted evidence.
Proof.
  intros target producer failure evidence Hcontra.
  discriminate Hcontra.
Qed.

Theorem checker_rejection_is_unresolved_not_refutation :
  forall target producer,
    unresolvedProducerResult target producer ProducerArtifactRejected =
      ProofAttemptUnresolved
        (mkUnresolvedProofAttempt target producer ProducerArtifactRejected).
Proof.
  reflexivity.
Qed.

Record ProofEvidenceLineage : Type := mkProofEvidenceLineage {
  proofEvidenceLineageTarget : ProofDischargeTarget;
  proofEvidenceLineageProducer : ProducerIdentity;
  proofEvidenceLineageChecker : CheckerIdentity;
  proofEvidenceLineageFormat : EvidenceFormat;
  proofEvidenceLineageSubjects : list SemanticIdentity;
  proofEvidenceLineageContexts : list SemanticIdentity;
  proofEvidenceLineageCertificate : CertificateIdentity
}.

Definition evidenceLineageOf
  (evidence : CheckedProofEvidence) : ProofEvidenceLineage :=
  mkProofEvidenceLineage
    (checkedProofTarget evidence)
    (checkedProofProducer evidence)
    (checkedProofChecker evidence)
    (checkedProofFormat evidence)
    (checkedProofSubjects evidence)
    (checkedProofContexts evidence)
    (checkedProofCertificate evidence).

Definition replaceLineageProducer
  (lineage : ProofEvidenceLineage)
  (producer : ProducerIdentity) : ProofEvidenceLineage :=
  mkProofEvidenceLineage
    (proofEvidenceLineageTarget lineage)
    producer
    (proofEvidenceLineageChecker lineage)
    (proofEvidenceLineageFormat lineage)
    (proofEvidenceLineageSubjects lineage)
    (proofEvidenceLineageContexts lineage)
    (proofEvidenceLineageCertificate lineage).

Definition replaceLineageCertificate
  (lineage : ProofEvidenceLineage)
  (certificate : CertificateIdentity) : ProofEvidenceLineage :=
  mkProofEvidenceLineage
    (proofEvidenceLineageTarget lineage)
    (proofEvidenceLineageProducer lineage)
    (proofEvidenceLineageChecker lineage)
    (proofEvidenceLineageFormat lineage)
    (proofEvidenceLineageSubjects lineage)
    (proofEvidenceLineageContexts lineage)
    certificate.

Theorem producer_replacement_does_not_rekey_discharge_target :
  forall lineage producer,
    proofEvidenceLineageTarget (replaceLineageProducer lineage producer) =
      proofEvidenceLineageTarget lineage.
Proof.
  reflexivity.
Qed.

Theorem certificate_replacement_does_not_rekey_discharge_target :
  forall lineage certificate,
    proofEvidenceLineageTarget (replaceLineageCertificate lineage certificate) =
      proofEvidenceLineageTarget lineage.
Proof.
  reflexivity.
Qed.

Theorem distinct_producers_have_distinct_evidence_lineage :
  forall lineage firstProducer secondProducer,
    firstProducer <> secondProducer ->
    replaceLineageProducer lineage firstProducer <>
      replaceLineageProducer lineage secondProducer.
Proof.
  intros lineage firstProducer secondProducer Hdifferent Hequal.
  apply Hdifferent.
  pose proof (f_equal proofEvidenceLineageProducer Hequal) as Hproducer.
  exact Hproducer.
Qed.

Theorem distinct_certificates_have_distinct_evidence_lineage :
  forall lineage firstCertificate secondCertificate,
    firstCertificate <> secondCertificate ->
    replaceLineageCertificate lineage firstCertificate <>
      replaceLineageCertificate lineage secondCertificate.
Proof.
  intros lineage firstCertificate secondCertificate Hdifferent Hequal.
  apply Hdifferent.
  pose proof (f_equal proofEvidenceLineageCertificate Hequal) as Hcertificate.
  exact Hcertificate.
Qed.
