From Stdlib Require Import Bool.Bool.

From Phil.Verification Require Import VerificationProducer.

(*
  PHIL-VERIFY-PRODUCER-001 — executable producer/checker correspondence.

  Production performs the concrete Text/list/revision/proposition checks and
  invokes the competent certificate checker.  This normalized layer owns the
  finite conjunction of those already-reflected facts.  Producer identity is
  deliberately absent from the authority conjunction: a producer may supply a
  proposal, but only exact competence plus competent-checker acceptance admits
  checked evidence.
*)

Definition producerAdmissionFactsb
  (targetMatches formatMatches subjectsMatch contextsMatch propositionMatches
    checkerAccepted : bool) : bool :=
  andb targetMatches
    (andb formatMatches
      (andb subjectsMatch
        (andb contextsMatch
          (andb propositionMatches checkerAccepted)))).

Inductive ProducerEvidenceDecision : Type :=
| ProducerEvidenceAccepted
| ProducerEvidenceRejected.

Definition decideProducerEvidence
  (targetMatches formatMatches subjectsMatch contextsMatch propositionMatches
    checkerAccepted : bool) : ProducerEvidenceDecision :=
  if producerAdmissionFactsb
      targetMatches formatMatches subjectsMatch contextsMatch propositionMatches
      checkerAccepted
  then ProducerEvidenceAccepted
  else ProducerEvidenceRejected.

Record ProducerAdmissionFactReflection
  (checkerAccepts : PropositionIdentity -> CertificateIdentity -> Prop)
  (expected : ProofCompetenceExpectation)
  (proposal : ProofProposal)
  (targetMatches formatMatches subjectsMatch contextsMatch propositionMatches
    checkerAccepted : bool) : Prop := mkProducerAdmissionFactReflection {
  targetMatchesReflects :
    targetMatches = true <->
      proofProposalTarget proposal = proofExpectedTarget expected;
  formatMatchesReflects :
    formatMatches = true <->
      proofProposalFormat proposal = proofExpectedFormat expected;
  subjectsMatchReflects :
    subjectsMatch = true <->
      SameMembers (proofProposalSubjects proposal) (proofExpectedSubjects expected);
  contextsMatchReflects :
    contextsMatch = true <->
      SameMembers (proofProposalContexts proposal) (proofExpectedContexts expected);
  propositionMatchesReflects :
    propositionMatches = true <->
      proofProposalProposition proposal = proofExpectedProposition expected;
  checkerAcceptedReflects :
    checkerAccepted = true <->
      checkerAccepts
        (proofProposalProposition proposal)
        (proofProposalCertificate proposal)
}.

Definition SemanticProducerAdmission
  (checkerAccepts : PropositionIdentity -> CertificateIdentity -> Prop)
  (expected : ProofCompetenceExpectation)
  (proposal : ProofProposal) : Prop :=
  ProposalCompetent expected proposal /\
  checkerAccepts
    (proofProposalProposition proposal)
    (proofProposalCertificate proposal).

Theorem producer_admission_facts_true_iff_semantic_admission :
  forall checkerAccepts expected proposal
    targetMatches formatMatches subjectsMatch contextsMatch propositionMatches
    checkerAccepted,
    ProducerAdmissionFactReflection
      checkerAccepts expected proposal
      targetMatches formatMatches subjectsMatch contextsMatch propositionMatches
      checkerAccepted ->
    (producerAdmissionFactsb
      targetMatches formatMatches subjectsMatch contextsMatch propositionMatches
      checkerAccepted = true <->
      SemanticProducerAdmission checkerAccepts expected proposal).
Proof.
  intros checkerAccepts expected proposal
    targetMatches formatMatches subjectsMatch contextsMatch propositionMatches
    checkerAccepted Hreflection.
  destruct Hreflection as
    [Htarget Hformat Hsubjects Hcontexts Hproposition Hchecker].
  unfold producerAdmissionFactsb, SemanticProducerAdmission, ProposalCompetent.
  repeat rewrite andb_true_iff.
  rewrite Htarget, Hformat, Hsubjects, Hcontexts, Hproposition, Hchecker.
  tauto.
Qed.

Theorem producer_evidence_decision_accept_iff_facts_true :
  forall targetMatches formatMatches subjectsMatch contextsMatch propositionMatches
    checkerAccepted,
    decideProducerEvidence
      targetMatches formatMatches subjectsMatch contextsMatch propositionMatches
      checkerAccepted = ProducerEvidenceAccepted <->
    producerAdmissionFactsb
      targetMatches formatMatches subjectsMatch contextsMatch propositionMatches
      checkerAccepted = true.
Proof.
  intros targetMatches formatMatches subjectsMatch contextsMatch propositionMatches
    checkerAccepted.
  unfold decideProducerEvidence.
  destruct (producerAdmissionFactsb
    targetMatches formatMatches subjectsMatch contextsMatch propositionMatches
    checkerAccepted) eqn:Hfacts;
    split; intro H; try reflexivity; try discriminate.
Qed.

Theorem producer_evidence_decision_accept_iff_certified_semantics :
  forall checkerAccepts expected proposal
    targetMatches formatMatches subjectsMatch contextsMatch propositionMatches
    checkerAccepted,
    ProducerAdmissionFactReflection
      checkerAccepts expected proposal
      targetMatches formatMatches subjectsMatch contextsMatch propositionMatches
      checkerAccepted ->
    (decideProducerEvidence
      targetMatches formatMatches subjectsMatch contextsMatch propositionMatches
      checkerAccepted = ProducerEvidenceAccepted <->
      SemanticProducerAdmission checkerAccepts expected proposal).
Proof.
  intros checkerAccepts expected proposal
    targetMatches formatMatches subjectsMatch contextsMatch propositionMatches
    checkerAccepted Hreflection.
  split.
  - intros Hdecision.
    apply (proj1
      (producer_admission_facts_true_iff_semantic_admission
        checkerAccepts expected proposal
        targetMatches formatMatches subjectsMatch contextsMatch propositionMatches
        checkerAccepted Hreflection)).
    apply (proj1
      (producer_evidence_decision_accept_iff_facts_true
        targetMatches formatMatches subjectsMatch contextsMatch propositionMatches
        checkerAccepted)).
    exact Hdecision.
  - intros Hsemantic.
    apply (proj2
      (producer_evidence_decision_accept_iff_facts_true
        targetMatches formatMatches subjectsMatch contextsMatch propositionMatches
        checkerAccepted)).
    apply (proj2
      (producer_admission_facts_true_iff_semantic_admission
        checkerAccepts expected proposal
        targetMatches formatMatches subjectsMatch contextsMatch propositionMatches
        checkerAccepted Hreflection)).
    exact Hsemantic.
Qed.

Theorem producer_identity_is_not_an_authority_fact :
  forall targetMatches formatMatches subjectsMatch contextsMatch propositionMatches
    checkerAccepted,
    decideProducerEvidence
      targetMatches formatMatches subjectsMatch contextsMatch propositionMatches
      checkerAccepted =
    decideProducerEvidence
      targetMatches formatMatches subjectsMatch contextsMatch propositionMatches
      checkerAccepted.
Proof.
  reflexivity.
Qed.

Theorem checker_rejection_rejects_evidence :
  forall targetMatches formatMatches subjectsMatch contextsMatch propositionMatches,
    decideProducerEvidence
      targetMatches formatMatches subjectsMatch contextsMatch propositionMatches false =
      ProducerEvidenceRejected.
Proof.
  intros.
  unfold decideProducerEvidence, producerAdmissionFactsb.
  repeat rewrite andb_false_r.
  reflexivity.
Qed.

Theorem target_mismatch_rejects_evidence :
  forall formatMatches subjectsMatch contextsMatch propositionMatches checkerAccepted,
    decideProducerEvidence
      false formatMatches subjectsMatch contextsMatch propositionMatches checkerAccepted =
      ProducerEvidenceRejected.
Proof.
  reflexivity.
Qed.

Inductive ProducerAttemptDecision : Type :=
| ProducerAttemptEvidenceAccepted
| ProducerAttemptStillUnresolved.

Definition decideProducerAttempt
  (producerSuppliedArtifact checkerAccepted : bool) : ProducerAttemptDecision :=
  if andb producerSuppliedArtifact checkerAccepted
  then ProducerAttemptEvidenceAccepted
  else ProducerAttemptStillUnresolved.

Theorem no_artifact_remains_unresolved :
  forall checkerAccepted,
    decideProducerAttempt false checkerAccepted = ProducerAttemptStillUnresolved.
Proof.
  reflexivity.
Qed.

Theorem checker_rejected_artifact_remains_unresolved :
  forall producerSuppliedArtifact,
    decideProducerAttempt producerSuppliedArtifact false = ProducerAttemptStillUnresolved.
Proof.
  intros producerSuppliedArtifact.
  destruct producerSuppliedArtifact; reflexivity.
Qed.

Theorem only_supplied_checker_accepted_artifact_closes_attempt :
  forall producerSuppliedArtifact checkerAccepted,
    decideProducerAttempt producerSuppliedArtifact checkerAccepted =
      ProducerAttemptEvidenceAccepted <->
    producerSuppliedArtifact = true /\ checkerAccepted = true.
Proof.
  intros producerSuppliedArtifact checkerAccepted.
  destruct producerSuppliedArtifact, checkerAccepted; cbn;
    split; intro H; try reflexivity; try discriminate; try tauto.
Qed.
