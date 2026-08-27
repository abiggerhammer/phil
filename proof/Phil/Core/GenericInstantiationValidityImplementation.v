From Stdlib Require Import Bool.Bool Arith.PeanoNat.

From Phil.Core Require Import GenericStructural GenericInstantiation.

(*
  PHIL-GEN-INST-IMPL-001, tranche B — executable per-disposition validity.

  Concrete production requirement identities are richer than the normalized
  GenericInstantiation proof atoms. This layer therefore extracts the
  acceptance/error-class decision over representation-neutral facts. The
  bridge is responsible only for computing primitive equality / structural
  permission facts from concrete values; the extracted decision owns whether
  those facts accept and which semantic error class applies.
*)

Inductive GenericRequirementKind : Type :=
| GenericStructuralRequirementKind
| GenericProviderRequirementKind
| GenericPropositionRequirementKind.

Inductive GenericDispositionKind : Type :=
| GenericStructuralModeDispositionKind
| GenericExactProviderDispositionKind
| GenericProviderRefinementDispositionKind
| GenericEvidenceDispositionKind
| GenericAssumptionDispositionKind
| GenericExportDispositionKind.

Record GenericDispositionValidityFacts : Type := mkGenericDispositionValidityFacts {
  validityRequirementKind : GenericRequirementKind;
  validityDispositionKind : GenericDispositionKind;
  validityStructuralModeAllows : bool;
  validityExactProviderMatches : bool;
  validityProviderRefinementTargets : bool;
  validityPropositionEvidenceMatches : bool;
  validityAllowsAssumptions : bool;
  validityAllowsExports : bool
}.

Inductive GenericDispositionValidityDecision : Type :=
| GenericDispositionValidityAccepted
| GenericDispositionValidityStructuralRejected
| GenericDispositionValidityProviderInterfaceMismatch
| GenericDispositionValidityProviderRefinementMismatch
| GenericDispositionValidityPropositionEvidenceMismatch
| GenericDispositionValidityAssumptionNotPermitted
| GenericDispositionValidityExportNotPermitted
| GenericDispositionValidityKindMismatch.

Definition decideGenericDispositionValidity
  (facts : GenericDispositionValidityFacts)
  : GenericDispositionValidityDecision :=
  match validityDispositionKind facts with
  | GenericAssumptionDispositionKind =>
      if validityAllowsAssumptions facts
      then GenericDispositionValidityAccepted
      else GenericDispositionValidityAssumptionNotPermitted
  | GenericExportDispositionKind =>
      if validityAllowsExports facts
      then GenericDispositionValidityAccepted
      else GenericDispositionValidityExportNotPermitted
  | GenericStructuralModeDispositionKind =>
      match validityRequirementKind facts with
      | GenericStructuralRequirementKind =>
          if validityStructuralModeAllows facts
          then GenericDispositionValidityAccepted
          else GenericDispositionValidityStructuralRejected
      | _ => GenericDispositionValidityKindMismatch
      end
  | GenericExactProviderDispositionKind =>
      match validityRequirementKind facts with
      | GenericProviderRequirementKind =>
          if validityExactProviderMatches facts
          then GenericDispositionValidityAccepted
          else GenericDispositionValidityProviderInterfaceMismatch
      | _ => GenericDispositionValidityKindMismatch
      end
  | GenericProviderRefinementDispositionKind =>
      match validityRequirementKind facts with
      | GenericProviderRequirementKind =>
          if validityProviderRefinementTargets facts
          then GenericDispositionValidityAccepted
          else GenericDispositionValidityProviderRefinementMismatch
      | _ => GenericDispositionValidityKindMismatch
      end
  | GenericEvidenceDispositionKind =>
      match validityRequirementKind facts with
      | GenericPropositionRequirementKind =>
          if validityPropositionEvidenceMatches facts
          then GenericDispositionValidityAccepted
          else GenericDispositionValidityPropositionEvidenceMismatch
      | _ => GenericDispositionValidityKindMismatch
      end
  end.

Definition requirementKindOf
  (requirement : GenericRequirement) : GenericRequirementKind :=
  match requirement with
  | StructuralRequirement _ => GenericStructuralRequirementKind
  | ProviderRequirement _ => GenericProviderRequirementKind
  | PropositionRequirement _ => GenericPropositionRequirementKind
  end.

Definition dispositionKindOf
  (disposition : GenericRequirementDisposition) : GenericDispositionKind :=
  match disposition with
  | SatisfiedByStructuralMode _ => GenericStructuralModeDispositionKind
  | SatisfiedByExactProvider _ => GenericExactProviderDispositionKind
  | SatisfiedByCheckedProviderRefinement _ _ =>
      GenericProviderRefinementDispositionKind
  | SatisfiedByEvidence _ => GenericEvidenceDispositionKind
  | AssumptionDependent => GenericAssumptionDispositionKind
  | Exported => GenericExportDispositionKind
  end.

Definition structuralModeAllowsFact
  (requirement : GenericRequirement)
  (disposition : GenericRequirementDisposition) : bool :=
  match requirement, disposition with
  | StructuralRequirement permission, SatisfiedByStructuralMode mode =>
      modeAllowsStructuralPermission mode permission
  | _, _ => false
  end.

Definition exactProviderMatchesFact
  (requirement : GenericRequirement)
  (disposition : GenericRequirementDisposition) : bool :=
  match requirement, disposition with
  | ProviderRequirement required, SatisfiedByExactProvider actual =>
      Nat.eqb actual required
  | _, _ => false
  end.

Definition providerRefinementTargetsFact
  (requirement : GenericRequirement)
  (disposition : GenericRequirementDisposition) : bool :=
  match requirement, disposition with
  | ProviderRequirement required,
      SatisfiedByCheckedProviderRefinement _ target =>
      Nat.eqb target required
  | _, _ => false
  end.

Definition propositionEvidenceMatchesFact
  (requirement : GenericRequirement)
  (disposition : GenericRequirementDisposition) : bool :=
  match requirement, disposition with
  | PropositionRequirement expected, SatisfiedByEvidence actual =>
      Nat.eqb actual expected
  | _, _ => false
  end.

Definition validityFactsOf
  (policy : GenericInstantiationPolicy)
  (requirement : GenericRequirement)
  (disposition : GenericRequirementDisposition)
  : GenericDispositionValidityFacts :=
  mkGenericDispositionValidityFacts
    (requirementKindOf requirement)
    (dispositionKindOf disposition)
    (structuralModeAllowsFact requirement disposition)
    (exactProviderMatchesFact requirement disposition)
    (providerRefinementTargetsFact requirement disposition)
    (propositionEvidenceMatchesFact requirement disposition)
    (allowsAssumptions policy)
    (allowsExports policy).

Definition dispositionValidityDecisionAcceptedb
  (decision : GenericDispositionValidityDecision) : bool :=
  match decision with
  | GenericDispositionValidityAccepted => true
  | _ => false
  end.

Lemma disposition_validity_decision_eq_accepted_iff :
  forall decision,
    decision = GenericDispositionValidityAccepted <->
    dispositionValidityDecisionAcceptedb decision = true.
Proof.
  intros decision.
  destruct decision; cbn; split; intro H;
    try reflexivity; try discriminate.
Qed.

Theorem validity_decision_agrees_with_certified_disposition_valid :
  forall policy requirement disposition,
    dispositionValidityDecisionAcceptedb
      (decideGenericDispositionValidity
        (validityFactsOf policy requirement disposition)) =
    dispositionValid policy requirement disposition.
Proof.
  intros [allowsAssumptions0 allowsExports0] requirement disposition.
  destruct requirement as [permission | required | expected];
    destruct disposition as
      [mode | actual | actual target | evidence | | ]; cbn.
  - destruct (modeAllowsStructuralPermission mode permission); reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct allowsAssumptions0; reflexivity.
  - destruct allowsExports0; reflexivity.
  - reflexivity.
  - destruct (Nat.eqb actual required); reflexivity.
  - destruct (Nat.eqb target required); reflexivity.
  - reflexivity.
  - destruct allowsAssumptions0; reflexivity.
  - destruct allowsExports0; reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (Nat.eqb evidence expected); reflexivity.
  - destruct allowsAssumptions0; reflexivity.
  - destruct allowsExports0; reflexivity.
Qed.

Theorem generic_instantiation_validity_decision_accept_iff :
  forall policy requirement disposition,
    decideGenericDispositionValidity
      (validityFactsOf policy requirement disposition) =
      GenericDispositionValidityAccepted <->
    dispositionValid policy requirement disposition = true.
Proof.
  intros policy requirement disposition.
  rewrite disposition_validity_decision_eq_accepted_iff.
  rewrite validity_decision_agrees_with_certified_disposition_valid.
  reflexivity.
Qed.

Theorem strict_assumption_decision_rejects :
  forall requirement,
    decideGenericDispositionValidity
      (validityFactsOf strictInstantiationPolicy requirement AssumptionDependent) =
      GenericDispositionValidityAssumptionNotPermitted.
Proof.
  intros requirement.
  destruct requirement; reflexivity.
Qed.

Theorem strict_export_decision_rejects :
  forall requirement,
    decideGenericDispositionValidity
      (validityFactsOf strictInstantiationPolicy requirement Exported) =
      GenericDispositionValidityExportNotPermitted.
Proof.
  intros requirement.
  destruct requirement; reflexivity.
Qed.

Theorem provider_binding_kind_does_not_discharge_proposition :
  forall proposition providerInterface,
    decideGenericDispositionValidity
      (validityFactsOf strictInstantiationPolicy
        (PropositionRequirement proposition)
        (SatisfiedByExactProvider providerInterface)) =
      GenericDispositionValidityKindMismatch.
Proof.
  reflexivity.
Qed.
