From Stdlib Require Import Lists.List.

Import ListNotations.

From Phil.Verification Require Import VerificationWorkflow VerificationProducer.

(*
  PHIL-VERIFY-POLICY-001 — policy-controlled runtime, assumption, and export
  disposition.

  This proof composes the already-Certified verification workflow and producer
  boundaries.  Intrinsic rejection remains terminal.  A residual obligation
  may become RuntimeBound, AssumptionDependent, or Exported only through an
  explicit, exact closure path whose semantic/boundary competence facts and
  selected assurance policy all independently admit that disposition.

  In particular, missing proof evidence and replaceable producer failure never
  silently synthesize an assumption or export.  Runtime closure retains
  explicit failure/resource residue and cost references, and policy identity is
  separate from source/obligation semantic identity.

  Concrete Text/Digest/RevisionId values, ADR-010 Assumption/ExportEntry
  digests and validity maps, RuntimeMechanism representation, the extracted
  runtime-authority kernel, and Haskell Map/Set normalization remain explicit
  representation or predecessor boundaries.
*)

Definition PolicyChoiceRevision := nat.
Definition EvidenceRoleIdentity := nat.
Definition RuntimeMechanismIdentity := nat.
Definition ResidueIdentity := nat.
Definition CostReferenceIdentity := nat.
Definition BoundaryIdentity := nat.
Definition AssumptionIdentity := nat.
Definition ExportIdentity := nat.

Inductive PolicyDisposition : Type :=
| DispositionStaticallyDischarged
| DispositionRuntimeBound
| DispositionAssumptionDependent
| DispositionExported
| DispositionUnresolved.

Record AssurancePolicy : Type := mkAssurancePolicy {
  assurancePolicyRevision : PolicyChoiceRevision;
  assurancePolicyPermits : PolicyDisposition -> Prop
}.

Record RuntimeClosureProposal : Type := mkRuntimeClosureProposal {
  runtimeProposalTarget : RevisionIdentity;
  runtimeProposalRole : EvidenceRoleIdentity;
  runtimeProposalMechanism : RuntimeMechanismIdentity;
  runtimeProposalResidue : list ResidueIdentity;
  runtimeProposalCostReferences : list CostReferenceIdentity
}.

Record RuntimeClosureFacts : Type := mkRuntimeClosureFacts {
  runtimeTargetInCertificationScope : Prop;
  runtimeAcceptanceRuleAllowsRole : Prop;
  runtimeMechanismComplete : Prop;
  runtimeResidueExplicit : Prop;
  runtimeCostReferencesPresent : Prop;
  runtimeCostReferencesKnown : Prop;
  runtimeAuthorityAccepts : Prop
}.

Definition RuntimeClosureAdmissible
  (policy : AssurancePolicy)
  (expectedTarget : RevisionIdentity)
  (proposal : RuntimeClosureProposal)
  (facts : RuntimeClosureFacts) : Prop :=
  runtimeProposalTarget proposal = expectedTarget /\
  runtimeTargetInCertificationScope facts /\
  runtimeAcceptanceRuleAllowsRole facts /\
  runtimeMechanismComplete facts /\
  runtimeResidueExplicit facts /\
  runtimeCostReferencesPresent facts /\
  runtimeCostReferencesKnown facts /\
  runtimeAuthorityAccepts facts /\
  assurancePolicyPermits policy DispositionRuntimeBound.

Record RuntimeClosureRecord : Type := mkRuntimeClosureRecord {
  runtimeClosureTarget : RevisionIdentity;
  runtimeClosurePolicyRevision : PolicyChoiceRevision;
  runtimeClosureRole : EvidenceRoleIdentity;
  runtimeClosureMechanism : RuntimeMechanismIdentity;
  runtimeClosureResidue : list ResidueIdentity;
  runtimeClosureCostReferences : list CostReferenceIdentity
}.

Definition makeRuntimeClosureRecord
  (policy : AssurancePolicy)
  (proposal : RuntimeClosureProposal) : RuntimeClosureRecord :=
  mkRuntimeClosureRecord
    (runtimeProposalTarget proposal)
    (assurancePolicyRevision policy)
    (runtimeProposalRole proposal)
    (runtimeProposalMechanism proposal)
    (runtimeProposalResidue proposal)
    (runtimeProposalCostReferences proposal).

Theorem runtime_closure_requires_exact_target :
  forall policy expectedTarget proposal facts,
    RuntimeClosureAdmissible policy expectedTarget proposal facts ->
    runtimeProposalTarget proposal = expectedTarget.
Proof.
  intros policy expectedTarget proposal facts Hadmitted.
  destruct Hadmitted as [Htarget _].
  exact Htarget.
Qed.

Theorem runtime_closure_requires_acceptance_rule :
  forall policy expectedTarget proposal facts,
    RuntimeClosureAdmissible policy expectedTarget proposal facts ->
    runtimeAcceptanceRuleAllowsRole facts.
Proof.
  intros policy expectedTarget proposal facts Hadmitted.
  destruct Hadmitted as [_ [_ [Hacceptance _]]].
  exact Hacceptance.
Qed.

Theorem runtime_closure_requires_explicit_residue :
  forall policy expectedTarget proposal facts,
    RuntimeClosureAdmissible policy expectedTarget proposal facts ->
    runtimeResidueExplicit facts.
Proof.
  intros policy expectedTarget proposal facts Hadmitted.
  destruct Hadmitted as [_ [_ [_ [_ [Hresidue _]]]]].
  exact Hresidue.
Qed.

Theorem runtime_closure_requires_known_cost_references :
  forall policy expectedTarget proposal facts,
    RuntimeClosureAdmissible policy expectedTarget proposal facts ->
    runtimeCostReferencesPresent facts /\ runtimeCostReferencesKnown facts.
Proof.
  intros policy expectedTarget proposal facts Hadmitted.
  destruct Hadmitted as [_ [_ [_ [_ [_ [Hpresent [Hknown _]]]]]]].
  split; assumption.
Qed.

Theorem runtime_closure_requires_competent_authority :
  forall policy expectedTarget proposal facts,
    RuntimeClosureAdmissible policy expectedTarget proposal facts ->
    runtimeAuthorityAccepts facts.
Proof.
  intros policy expectedTarget proposal facts Hadmitted.
  destruct Hadmitted as [_ [_ [_ [_ [_ [_ [_ [Hauthority _]]]]]]]].
  exact Hauthority.
Qed.

Theorem runtime_closure_requires_policy_permission :
  forall policy expectedTarget proposal facts,
    RuntimeClosureAdmissible policy expectedTarget proposal facts ->
    assurancePolicyPermits policy DispositionRuntimeBound.
Proof.
  intros policy expectedTarget proposal facts Hadmitted.
  destruct Hadmitted as [_ [_ [_ [_ [_ [_ [_ [_ Hpolicy]]]]]]]].
  exact Hpolicy.
Qed.

Theorem runtime_policy_rejection_prevents_closure :
  forall policy expectedTarget proposal facts,
    ~ assurancePolicyPermits policy DispositionRuntimeBound ->
    ~ RuntimeClosureAdmissible policy expectedTarget proposal facts.
Proof.
  intros policy expectedTarget proposal facts Hpolicy Hadmitted.
  apply Hpolicy.
  eapply runtime_closure_requires_policy_permission.
  exact Hadmitted.
Qed.

Theorem changing_only_runtime_policy_does_not_rekey_target :
  forall firstPolicy secondPolicy proposal,
    runtimeClosureTarget (makeRuntimeClosureRecord firstPolicy proposal) =
    runtimeClosureTarget (makeRuntimeClosureRecord secondPolicy proposal).
Proof.
  reflexivity.
Qed.

Theorem runtime_closure_cannot_repair_intrinsic_rejection :
  forall workflowPolicy,
    decideIntrinsicWorkflow false workflowPolicy = WorkflowRejected.
Proof.
  apply intrinsic_rejection_is_terminal.
Qed.

Record AssumptionBoundaryProposal : Type := mkAssumptionBoundaryProposal {
  assumptionProposalTarget : RevisionIdentity;
  assumptionProposalRole : EvidenceRoleIdentity;
  assumptionProposalIdentity : AssumptionIdentity;
  assumptionProposalOwnerBoundary : BoundaryIdentity
}.

Record AssumptionClosureFacts : Type := mkAssumptionClosureFacts {
  assumptionTargetInCertificationScope : Prop;
  assumptionRoleExact : Prop;
  assumptionAcceptanceRuleAllows : Prop;
  assumptionContentBound : Prop;
  assumptionExplicitlyPermitted : Prop;
  assumptionValidityMatches : Prop
}.

Definition AssumptionClosureAdmissible
  (policy : AssurancePolicy)
  (expectedTarget : RevisionIdentity)
  (proposal : AssumptionBoundaryProposal)
  (facts : AssumptionClosureFacts) : Prop :=
  assumptionProposalTarget proposal = expectedTarget /\
  assumptionTargetInCertificationScope facts /\
  assumptionRoleExact facts /\
  assumptionAcceptanceRuleAllows facts /\
  assumptionContentBound facts /\
  assumptionExplicitlyPermitted facts /\
  assumptionValidityMatches facts /\
  assurancePolicyPermits policy DispositionAssumptionDependent.

Theorem assumption_closure_requires_explicit_permission :
  forall policy expectedTarget proposal facts,
    AssumptionClosureAdmissible policy expectedTarget proposal facts ->
    assumptionExplicitlyPermitted facts.
Proof.
  intros policy expectedTarget proposal facts Hadmitted.
  destruct Hadmitted as [_ [_ [_ [_ [_ [Hpermitted _]]]]]].
  exact Hpermitted.
Qed.

Theorem assumption_closure_requires_policy_permission :
  forall policy expectedTarget proposal facts,
    AssumptionClosureAdmissible policy expectedTarget proposal facts ->
    assurancePolicyPermits policy DispositionAssumptionDependent.
Proof.
  intros policy expectedTarget proposal facts Hadmitted.
  destruct Hadmitted as [_ [_ [_ [_ [_ [_ [_ Hpolicy]]]]]]].
  exact Hpolicy.
Qed.

Record ExportBoundaryProposal : Type := mkExportBoundaryProposal {
  exportProposalTarget : RevisionIdentity;
  exportProposalIdentity : ExportIdentity;
  exportProposalDestinationBoundary : BoundaryIdentity
}.

Record ExportClosureFacts : Type := mkExportClosureFacts {
  exportTargetOutsideCertificationScope : Prop;
  exportContentBound : Prop;
  exportDestinationPresent : Prop;
  exportDestinationExplicitlyPermitted : Prop;
  exportValidityMatches : Prop
}.

Definition ExportClosureAdmissible
  (policy : AssurancePolicy)
  (expectedTarget : RevisionIdentity)
  (proposal : ExportBoundaryProposal)
  (facts : ExportClosureFacts) : Prop :=
  exportProposalTarget proposal = expectedTarget /\
  exportTargetOutsideCertificationScope facts /\
  exportContentBound facts /\
  exportDestinationPresent facts /\
  exportDestinationExplicitlyPermitted facts /\
  exportValidityMatches facts /\
  assurancePolicyPermits policy DispositionExported.

Theorem export_closure_requires_out_of_scope_target :
  forall policy expectedTarget proposal facts,
    ExportClosureAdmissible policy expectedTarget proposal facts ->
    exportTargetOutsideCertificationScope facts.
Proof.
  intros policy expectedTarget proposal facts Hadmitted.
  destruct Hadmitted as [_ [Houtside _]].
  exact Houtside.
Qed.

Theorem export_closure_requires_explicit_destination_permission :
  forall policy expectedTarget proposal facts,
    ExportClosureAdmissible policy expectedTarget proposal facts ->
    exportDestinationExplicitlyPermitted facts.
Proof.
  intros policy expectedTarget proposal facts Hadmitted.
  destruct Hadmitted as [_ [_ [_ [_ [Hpermitted _]]]]].
  exact Hpermitted.
Qed.

Theorem export_closure_requires_policy_permission :
  forall policy expectedTarget proposal facts,
    ExportClosureAdmissible policy expectedTarget proposal facts ->
    assurancePolicyPermits policy DispositionExported.
Proof.
  intros policy expectedTarget proposal facts Hadmitted.
  destruct Hadmitted as [_ [_ [_ [_ [_ [_ Hpolicy]]]]]].
  exact Hpolicy.
Qed.

Inductive MissingProofBoundaryProposal : Type :=
| NoBoundaryProposal
| ExplicitAssumptionProposal (proposal : AssumptionBoundaryProposal)
| ExplicitExportProposal (proposal : ExportBoundaryProposal).

Inductive MissingProofBoundaryDecision : Type :=
| PolicyMissingProofRemainsUnresolved (target : RevisionIdentity)
| PolicyAssumptionProposalRequiresValidation
    (target : RevisionIdentity)
    (proposal : AssumptionBoundaryProposal)
| PolicyExportProposalRequiresValidation
    (target : RevisionIdentity)
    (proposal : ExportBoundaryProposal).

Definition decideMissingProofBoundary
  (policy : AssurancePolicy)
  (target : RevisionIdentity)
  (proposal : MissingProofBoundaryProposal) : MissingProofBoundaryDecision :=
  match proposal with
  | NoBoundaryProposal => PolicyMissingProofRemainsUnresolved target
  | ExplicitAssumptionProposal assumption =>
      PolicyAssumptionProposalRequiresValidation target assumption
  | ExplicitExportProposal exportEntry =>
      PolicyExportProposalRequiresValidation target exportEntry
  end.

Theorem proof_absence_without_explicit_boundary_remains_unresolved :
  forall policy target,
    decideMissingProofBoundary policy target NoBoundaryProposal =
      PolicyMissingProofRemainsUnresolved target.
Proof.
  reflexivity.
Qed.

Theorem missing_proof_default_is_policy_independent :
  forall firstPolicy secondPolicy target,
    decideMissingProofBoundary firstPolicy target NoBoundaryProposal =
    decideMissingProofBoundary secondPolicy target NoBoundaryProposal.
Proof.
  reflexivity.
Qed.

Theorem producer_failure_without_boundary_proposal_remains_unresolved :
  forall target producer failure policy,
    exists attempt,
      unresolvedProducerResult target producer failure =
        ProofAttemptUnresolved attempt /\
      decideMissingProofBoundary
        policy
        (proofTargetObligationRevision target)
        NoBoundaryProposal =
        PolicyMissingProofRemainsUnresolved
          (proofTargetObligationRevision target).
Proof.
  intros target producer failure policy.
  destruct (producer_failure_remains_unresolved target producer failure) as
    [attempt [Hresult Hfacts]].
  exists attempt.
  split.
  - exact Hresult.
  - reflexivity.
Qed.
