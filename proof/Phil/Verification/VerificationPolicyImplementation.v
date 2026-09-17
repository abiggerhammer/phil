From Stdlib Require Import Bool.Bool.

From Phil.Verification Require Import VerificationWorkflow VerificationPolicy.

(*
  PHIL-VERIFY-POLICY-001 — executable correspondence for VER-007 / VER-008.

  The Haskell implementation evaluates finite boolean/equality gates before it
  admits RuntimeBound, AssumptionDependent, or Exported.  This file reflects
  those finite gate surfaces into the semantic predicates in VerificationPolicy.
  The no-proposal case is separate and policy-independent: no explicit boundary
  proposal remains unresolved.
*)

Definition runtimeAdmissionFactsb
  (targetMatches targetInScope acceptanceAllows mechanismComplete residuePresent
    costRefsPresent costRefsKnown authorityAccepted policyPermits : bool) : bool :=
  andb targetMatches
    (andb targetInScope
      (andb acceptanceAllows
        (andb mechanismComplete
          (andb residuePresent
            (andb costRefsPresent
              (andb costRefsKnown
                (andb authorityAccepted policyPermits))))))).

Record RuntimeAdmissionFactReflection
  (policy : AssurancePolicy)
  (expectedTarget : RevisionIdentity)
  (proposal : RuntimeClosureProposal)
  (facts : RuntimeClosureFacts)
  (targetMatches targetInScope acceptanceAllows mechanismComplete residuePresent
    costRefsPresent costRefsKnown authorityAccepted policyPermits : bool) : Prop :=
  mkRuntimeAdmissionFactReflection {
    runtimeTargetMatchesReflects :
      targetMatches = true <-> runtimeProposalTarget proposal = expectedTarget;
    runtimeTargetScopeReflects :
      targetInScope = true <-> runtimeTargetInCertificationScope facts;
    runtimeAcceptanceReflects :
      acceptanceAllows = true <-> runtimeAcceptanceRuleAllowsRole facts;
    runtimeMechanismReflects :
      mechanismComplete = true <-> runtimeMechanismComplete facts;
    runtimeResidueReflects :
      residuePresent = true <-> runtimeResidueExplicit facts;
    runtimeCostPresenceReflects :
      costRefsPresent = true <-> runtimeCostReferencesPresent facts;
    runtimeCostKnownReflects :
      costRefsKnown = true <-> runtimeCostReferencesKnown facts;
    runtimeAuthorityReflects :
      authorityAccepted = true <-> runtimeAuthorityAccepts facts;
    runtimePolicyReflects :
      policyPermits = true <->
        assurancePolicyPermits policy DispositionRuntimeBound
  }.

Theorem runtime_admission_facts_true_iff_semantic_admission :
  forall policy expectedTarget proposal facts
    targetMatches targetInScope acceptanceAllows mechanismComplete residuePresent
    costRefsPresent costRefsKnown authorityAccepted policyPermits,
    RuntimeAdmissionFactReflection
      policy expectedTarget proposal facts
      targetMatches targetInScope acceptanceAllows mechanismComplete residuePresent
      costRefsPresent costRefsKnown authorityAccepted policyPermits ->
    (runtimeAdmissionFactsb
      targetMatches targetInScope acceptanceAllows mechanismComplete residuePresent
      costRefsPresent costRefsKnown authorityAccepted policyPermits = true <->
      RuntimeClosureAdmissible policy expectedTarget proposal facts).
Proof.
  intros policy expectedTarget proposal facts
    targetMatches targetInScope acceptanceAllows mechanismComplete residuePresent
    costRefsPresent costRefsKnown authorityAccepted policyPermits Hreflection.
  destruct Hreflection as
    [Htarget Hscope Hacceptance Hmechanism Hresidue HcostPresent HcostKnown
      Hauthority Hpolicy].
  unfold runtimeAdmissionFactsb, RuntimeClosureAdmissible.
  repeat rewrite andb_true_iff.
  rewrite Htarget, Hscope, Hacceptance, Hmechanism, Hresidue, HcostPresent,
    HcostKnown, Hauthority, Hpolicy.
  tauto.
Qed.

Inductive RuntimeAdmissionDecision : Type :=
| RuntimeAdmissionAccepted
| RuntimeAdmissionRejected.

Definition decideRuntimeAdmission
  (targetMatches targetInScope acceptanceAllows mechanismComplete residuePresent
    costRefsPresent costRefsKnown authorityAccepted policyPermits : bool)
  : RuntimeAdmissionDecision :=
  if runtimeAdmissionFactsb
      targetMatches targetInScope acceptanceAllows mechanismComplete residuePresent
      costRefsPresent costRefsKnown authorityAccepted policyPermits
  then RuntimeAdmissionAccepted
  else RuntimeAdmissionRejected.

Theorem runtime_admission_decision_accept_iff_facts_true :
  forall targetMatches targetInScope acceptanceAllows mechanismComplete residuePresent
    costRefsPresent costRefsKnown authorityAccepted policyPermits,
    decideRuntimeAdmission
      targetMatches targetInScope acceptanceAllows mechanismComplete residuePresent
      costRefsPresent costRefsKnown authorityAccepted policyPermits =
        RuntimeAdmissionAccepted <->
    runtimeAdmissionFactsb
      targetMatches targetInScope acceptanceAllows mechanismComplete residuePresent
      costRefsPresent costRefsKnown authorityAccepted policyPermits = true.
Proof.
  intros targetMatches targetInScope acceptanceAllows mechanismComplete residuePresent
    costRefsPresent costRefsKnown authorityAccepted policyPermits.
  unfold decideRuntimeAdmission.
  destruct (runtimeAdmissionFactsb
    targetMatches targetInScope acceptanceAllows mechanismComplete residuePresent
    costRefsPresent costRefsKnown authorityAccepted policyPermits) eqn:Hfacts;
    split; intro H; try reflexivity; try discriminate.
Qed.

Theorem runtime_policy_denial_rejects :
  forall targetMatches targetInScope acceptanceAllows mechanismComplete residuePresent
    costRefsPresent costRefsKnown authorityAccepted,
    decideRuntimeAdmission
      targetMatches targetInScope acceptanceAllows mechanismComplete residuePresent
      costRefsPresent costRefsKnown authorityAccepted false =
      RuntimeAdmissionRejected.
Proof.
  intros.
  unfold decideRuntimeAdmission, runtimeAdmissionFactsb.
  repeat rewrite andb_false_r.
  reflexivity.
Qed.

Theorem runtime_acceptance_rule_denial_rejects :
  forall targetMatches targetInScope mechanismComplete residuePresent costRefsPresent
    costRefsKnown authorityAccepted policyPermits,
    decideRuntimeAdmission
      targetMatches targetInScope false mechanismComplete residuePresent
      costRefsPresent costRefsKnown authorityAccepted policyPermits =
      RuntimeAdmissionRejected.
Proof.
  intros.
  unfold decideRuntimeAdmission, runtimeAdmissionFactsb.
  rewrite andb_false_l.
  repeat rewrite andb_false_r.
  reflexivity.
Qed.

Definition assumptionAdmissionFactsb
  (targetMatches targetInScope roleExact acceptanceAllows contentBound
    explicitlyPermitted validityMatches policyPermits : bool) : bool :=
  andb targetMatches
    (andb targetInScope
      (andb roleExact
        (andb acceptanceAllows
          (andb contentBound
            (andb explicitlyPermitted
              (andb validityMatches policyPermits)))))).

Record AssumptionAdmissionFactReflection
  (policy : AssurancePolicy)
  (expectedTarget : RevisionIdentity)
  (proposal : AssumptionBoundaryProposal)
  (facts : AssumptionClosureFacts)
  (targetMatches targetInScope roleExact acceptanceAllows contentBound
    explicitlyPermitted validityMatches policyPermits : bool) : Prop :=
  mkAssumptionAdmissionFactReflection {
    assumptionTargetMatchesReflects :
      targetMatches = true <-> assumptionProposalTarget proposal = expectedTarget;
    assumptionTargetScopeReflects :
      targetInScope = true <-> assumptionTargetInCertificationScope facts;
    assumptionRoleReflects :
      roleExact = true <-> assumptionRoleExact facts;
    assumptionAcceptanceReflects :
      acceptanceAllows = true <-> assumptionAcceptanceRuleAllows facts;
    assumptionContentReflects :
      contentBound = true <-> assumptionContentBound facts;
    assumptionPermissionReflects :
      explicitlyPermitted = true <-> assumptionExplicitlyPermitted facts;
    assumptionValidityReflects :
      validityMatches = true <-> assumptionValidityMatches facts;
    assumptionPolicyReflects :
      policyPermits = true <->
        assurancePolicyPermits policy DispositionAssumptionDependent
  }.

Theorem assumption_admission_facts_true_iff_semantic_admission :
  forall policy expectedTarget proposal facts
    targetMatches targetInScope roleExact acceptanceAllows contentBound
    explicitlyPermitted validityMatches policyPermits,
    AssumptionAdmissionFactReflection
      policy expectedTarget proposal facts
      targetMatches targetInScope roleExact acceptanceAllows contentBound
      explicitlyPermitted validityMatches policyPermits ->
    (assumptionAdmissionFactsb
      targetMatches targetInScope roleExact acceptanceAllows contentBound
      explicitlyPermitted validityMatches policyPermits = true <->
      AssumptionClosureAdmissible policy expectedTarget proposal facts).
Proof.
  intros policy expectedTarget proposal facts
    targetMatches targetInScope roleExact acceptanceAllows contentBound
    explicitlyPermitted validityMatches policyPermits Hreflection.
  destruct Hreflection as
    [Htarget Hscope Hrole Hacceptance Hcontent Hpermission Hvalidity Hpolicy].
  unfold assumptionAdmissionFactsb, AssumptionClosureAdmissible.
  repeat rewrite andb_true_iff.
  rewrite Htarget, Hscope, Hrole, Hacceptance, Hcontent, Hpermission, Hvalidity,
    Hpolicy.
  tauto.
Qed.

Definition exportAdmissionFactsb
  (targetMatches targetOutsideScope contentBound destinationPresent
    destinationPermitted validityMatches policyPermits : bool) : bool :=
  andb targetMatches
    (andb targetOutsideScope
      (andb contentBound
        (andb destinationPresent
          (andb destinationPermitted
            (andb validityMatches policyPermits))))).

Record ExportAdmissionFactReflection
  (policy : AssurancePolicy)
  (expectedTarget : RevisionIdentity)
  (proposal : ExportBoundaryProposal)
  (facts : ExportClosureFacts)
  (targetMatches targetOutsideScope contentBound destinationPresent
    destinationPermitted validityMatches policyPermits : bool) : Prop :=
  mkExportAdmissionFactReflection {
    exportTargetMatchesReflects :
      targetMatches = true <-> exportProposalTarget proposal = expectedTarget;
    exportScopeReflects :
      targetOutsideScope = true <-> exportTargetOutsideCertificationScope facts;
    exportContentReflects :
      contentBound = true <-> exportContentBound facts;
    exportDestinationPresentReflects :
      destinationPresent = true <-> exportDestinationPresent facts;
    exportDestinationPermissionReflects :
      destinationPermitted = true <-> exportDestinationExplicitlyPermitted facts;
    exportValidityReflects :
      validityMatches = true <-> exportValidityMatches facts;
    exportPolicyReflects :
      policyPermits = true <-> assurancePolicyPermits policy DispositionExported
  }.

Theorem export_admission_facts_true_iff_semantic_admission :
  forall policy expectedTarget proposal facts
    targetMatches targetOutsideScope contentBound destinationPresent
    destinationPermitted validityMatches policyPermits,
    ExportAdmissionFactReflection
      policy expectedTarget proposal facts
      targetMatches targetOutsideScope contentBound destinationPresent
      destinationPermitted validityMatches policyPermits ->
    (exportAdmissionFactsb
      targetMatches targetOutsideScope contentBound destinationPresent
      destinationPermitted validityMatches policyPermits = true <->
      ExportClosureAdmissible policy expectedTarget proposal facts).
Proof.
  intros policy expectedTarget proposal facts
    targetMatches targetOutsideScope contentBound destinationPresent
    destinationPermitted validityMatches policyPermits Hreflection.
  destruct Hreflection as
    [Htarget Hscope Hcontent Hpresent Hpermission Hvalidity Hpolicy].
  unfold exportAdmissionFactsb, ExportClosureAdmissible.
  repeat rewrite andb_true_iff.
  rewrite Htarget, Hscope, Hcontent, Hpresent, Hpermission, Hvalidity, Hpolicy.
  tauto.
Qed.

Inductive MissingProofProposalTag : Type :=
| NoExplicitBoundaryProposal
| ExplicitAssumptionBoundaryProposal
| ExplicitExportBoundaryProposal.

Inductive MissingProofPolicyDecision : Type :=
| MissingProofStillUnresolved
| MissingProofAssumptionCandidate
| MissingProofExportCandidate
| MissingProofBoundaryRejected.

Definition decideMissingProofPolicy
  (policyAllowsAssumption policyAllowsExport : bool)
  (proposal : MissingProofProposalTag) : MissingProofPolicyDecision :=
  match proposal with
  | NoExplicitBoundaryProposal => MissingProofStillUnresolved
  | ExplicitAssumptionBoundaryProposal =>
      if policyAllowsAssumption
      then MissingProofAssumptionCandidate
      else MissingProofBoundaryRejected
  | ExplicitExportBoundaryProposal =>
      if policyAllowsExport
      then MissingProofExportCandidate
      else MissingProofBoundaryRejected
  end.

Theorem no_explicit_boundary_stays_unresolved_under_any_policy :
  forall policyAllowsAssumption policyAllowsExport,
    decideMissingProofPolicy
      policyAllowsAssumption policyAllowsExport NoExplicitBoundaryProposal =
      MissingProofStillUnresolved.
Proof.
  reflexivity.
Qed.

Theorem proof_absence_cannot_silently_select_assumption :
  forall policyAllowsAssumption policyAllowsExport,
    decideMissingProofPolicy
      policyAllowsAssumption policyAllowsExport NoExplicitBoundaryProposal <>
      MissingProofAssumptionCandidate.
Proof.
  intros policyAllowsAssumption policyAllowsExport Hcontra.
  discriminate Hcontra.
Qed.

Theorem proof_absence_cannot_silently_select_export :
  forall policyAllowsAssumption policyAllowsExport,
    decideMissingProofPolicy
      policyAllowsAssumption policyAllowsExport NoExplicitBoundaryProposal <>
      MissingProofExportCandidate.
Proof.
  intros policyAllowsAssumption policyAllowsExport Hcontra.
  discriminate Hcontra.
Qed.

Theorem implementation_policy_cannot_override_intrinsic_rejection :
  forall workflowPolicy,
    decideIntrinsicWorkflow false workflowPolicy = WorkflowRejected.
Proof.
  apply intrinsic_rejection_is_terminal.
Qed.
