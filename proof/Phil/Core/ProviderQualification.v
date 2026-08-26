From Phil.Core Require Import CallableRefinement ResourceJoin.

(*
  PHIL-PROV-QUAL-001 — total explicit provider semantic qualification.

  The normalized provider model deliberately excludes source/runtime symbol
  inference. Every public operation has one explicit correspondence to an exact
  implementation entry, ordinary CALL-012 callable refinement, no stronger
  preconditions, explicit total implementation-outcome mapping, and exact
  per-outcome resource residue equality.
*)

Definition ProviderOperationKey := nat.
Definition ProviderEntryKey := nat.
Definition ProviderOutcomeKey := nat.
Definition ProviderPreconditionSet := BoolSet.

Record ProviderResourceResidue : Type := mkProviderResourceResidue {
  residueBorrowedInputs : BoolSet;
  residueConsumedInputs : BoolSet;
  residueReturnedPredecessors : BoolSet;
  residueSuccessors : BoolSet;
  residueProducedResources : BoolSet
}.

Record ProviderOperationContract : Type := mkProviderOperationContract {
  contractCallableSurface : CallableRefinementSurface;
  contractPreconditions : ProviderPreconditionSet;
  contractOutcomeResidues : ProviderOutcomeKey -> option ProviderResourceResidue
}.

Record ProviderImplementationOperation : Type := mkProviderImplementationOperation {
  implementationCallableSurface : CallableRefinementSurface;
  implementationPreconditions : ProviderPreconditionSet;
  implementationOutcomeResidues : ProviderOutcomeKey -> option ProviderResourceResidue
}.

Record ProviderContract : Type := mkProviderContract {
  providerInterfaceRevision : nat;
  providerOperations : ProviderOperationKey -> option ProviderOperationContract
}.

Record ProviderImplementation : Type := mkProviderImplementation {
  providerDefinitionRevision : nat;
  providerEntries : ProviderEntryKey -> option ProviderImplementationOperation;
  providerSymbols : BoolSet
}.

Record ProviderOperationCorrespondence : Type := mkProviderOperationCorrespondence {
  correspondenceEntry : ProviderEntryKey;
  correspondenceOutcomes : ProviderOutcomeKey -> option ProviderOutcomeKey
}.

Record ProviderQualificationClaim : Type := mkProviderQualificationClaim {
  claimRequiredInterface : nat;
  claimImplementationRevision : nat;
  claimCorrespondences : ProviderOperationKey -> option ProviderOperationCorrespondence
}.

Definition OutcomeCorrespondenceExact
  (contract : ProviderOperationContract)
  (implementation : ProviderImplementationOperation)
  (correspondence : ProviderOperationCorrespondence) : Prop :=
  (forall implementationOutcome implementationResidue,
    implementationOutcomeResidues implementation implementationOutcome = Some implementationResidue ->
    exists contractOutcome contractResidue,
      correspondenceOutcomes correspondence implementationOutcome = Some contractOutcome /\
      contractOutcomeResidues contract contractOutcome = Some contractResidue /\
      implementationResidue = contractResidue) /\
  (forall implementationOutcome contractOutcome,
    correspondenceOutcomes correspondence implementationOutcome = Some contractOutcome ->
    exists implementationResidue contractResidue,
      implementationOutcomeResidues implementation implementationOutcome = Some implementationResidue /\
      contractOutcomeResidues contract contractOutcome = Some contractResidue /\
      implementationResidue = contractResidue).

Definition ProviderOperationQualifies
  (contract : ProviderOperationContract)
  (implementation : ProviderImplementationOperation)
  (correspondence : ProviderOperationCorrespondence) : Prop :=
  callableRefines
    (contractCallableSurface contract)
    (implementationCallableSurface implementation) /\
  setSubset
    (implementationPreconditions implementation)
    (contractPreconditions contract) /\
  OutcomeCorrespondenceExact contract implementation correspondence.

Definition ProviderQualifies
  (contract : ProviderContract)
  (implementation : ProviderImplementation)
  (claim : ProviderQualificationClaim) : Prop :=
  claimRequiredInterface claim = providerInterfaceRevision contract /\
  claimImplementationRevision claim = providerDefinitionRevision implementation /\
  (forall operation operationContract,
    providerOperations contract operation = Some operationContract ->
    exists correspondence implementationOperation,
      claimCorrespondences claim operation = Some correspondence /\
      providerEntries implementation (correspondenceEntry correspondence) =
        Some implementationOperation /\
      ProviderOperationQualifies operationContract implementationOperation correspondence) /\
  (forall operation correspondence,
    claimCorrespondences claim operation = Some correspondence ->
    exists operationContract,
      providerOperations contract operation = Some operationContract).

Definition withProviderSymbols
  (symbols : BoolSet)
  (implementation : ProviderImplementation) : ProviderImplementation :=
  mkProviderImplementation
    (providerDefinitionRevision implementation)
    (providerEntries implementation)
    symbols.

Theorem qualified_provider_has_exact_contract_revision :
  forall contract implementation claim,
    ProviderQualifies contract implementation claim ->
    claimRequiredInterface claim = providerInterfaceRevision contract.
Proof.
  intros contract implementation claim Hqualified.
  exact (proj1 Hqualified).
Qed.

Theorem qualified_provider_has_exact_implementation_revision :
  forall contract implementation claim,
    ProviderQualifies contract implementation claim ->
    claimImplementationRevision claim = providerDefinitionRevision implementation.
Proof.
  intros contract implementation claim Hqualified.
  exact (proj1 (proj2 Hqualified)).
Qed.

Theorem every_public_operation_has_explicit_correspondence :
  forall contract implementation claim operation operationContract,
    ProviderQualifies contract implementation claim ->
    providerOperations contract operation = Some operationContract ->
    exists correspondence implementationOperation,
      claimCorrespondences claim operation = Some correspondence /\
      providerEntries implementation (correspondenceEntry correspondence) =
        Some implementationOperation /\
      ProviderOperationQualifies operationContract implementationOperation correspondence.
Proof.
  intros contract implementation claim operation operationContract Hqualified Hoperation.
  destruct Hqualified as [_ [_ [Htotal _]]].
  eapply Htotal.
  exact Hoperation.
Qed.

Theorem missing_public_operation_correspondence_rejects :
  forall contract implementation claim operation operationContract,
    providerOperations contract operation = Some operationContract ->
    claimCorrespondences claim operation = None ->
    ~ ProviderQualifies contract implementation claim.
Proof.
  intros contract implementation claim operation operationContract Hoperation Hmissing Hqualified.
  destruct (every_public_operation_has_explicit_correspondence
    contract implementation claim operation operationContract Hqualified Hoperation)
    as [correspondence [implementationOperation [Hcorrespondence _]]].
  rewrite Hmissing in Hcorrespondence.
  discriminate.
Qed.

Theorem unexpected_operation_correspondence_rejects :
  forall contract implementation claim operation correspondence,
    providerOperations contract operation = None ->
    claimCorrespondences claim operation = Some correspondence ->
    ~ ProviderQualifies contract implementation claim.
Proof.
  intros contract implementation claim operation correspondence Hmissing Hcorrespondence Hqualified.
  destruct Hqualified as [_ [_ [_ Hunexpected]]].
  destruct (Hunexpected operation correspondence Hcorrespondence) as [operationContract Hoperation].
  rewrite Hmissing in Hoperation.
  discriminate.
Qed.

Theorem qualified_operation_uses_callable_refinement :
  forall contract implementation claim operation operationContract correspondence implementationOperation,
    ProviderQualifies contract implementation claim ->
    providerOperations contract operation = Some operationContract ->
    claimCorrespondences claim operation = Some correspondence ->
    providerEntries implementation (correspondenceEntry correspondence) = Some implementationOperation ->
    ProviderOperationQualifies operationContract implementationOperation correspondence ->
    callableRefines
      (contractCallableSurface operationContract)
      (implementationCallableSurface implementationOperation).
Proof.
  intros contract implementation claim operation operationContract correspondence implementationOperation
    Hqualified Hoperation Hcorrespondence Hentry HoperationQualified.
  exact (proj1 HoperationQualified).
Qed.

Theorem qualified_operation_has_no_stronger_preconditions :
  forall operationContract implementationOperation correspondence,
    ProviderOperationQualifies operationContract implementationOperation correspondence ->
    setSubset
      (implementationPreconditions implementationOperation)
      (contractPreconditions operationContract).
Proof.
  intros operationContract implementationOperation correspondence Hqualified.
  exact (proj1 (proj2 Hqualified)).
Qed.

Theorem every_implementation_outcome_is_explicitly_mapped :
  forall operationContract implementationOperation correspondence implementationOutcome implementationResidue,
    ProviderOperationQualifies operationContract implementationOperation correspondence ->
    implementationOutcomeResidues implementationOperation implementationOutcome = Some implementationResidue ->
    exists contractOutcome contractResidue,
      correspondenceOutcomes correspondence implementationOutcome = Some contractOutcome /\
      contractOutcomeResidues operationContract contractOutcome = Some contractResidue /\
      implementationResidue = contractResidue.
Proof.
  intros operationContract implementationOperation correspondence implementationOutcome implementationResidue
    Hqualified Hresidue.
  destruct Hqualified as [_ [_ [Htotal _]]].
  eapply Htotal.
  exact Hresidue.
Qed.

Theorem every_declared_outcome_mapping_has_exact_resource_residue :
  forall operationContract implementationOperation correspondence implementationOutcome contractOutcome,
    ProviderOperationQualifies operationContract implementationOperation correspondence ->
    correspondenceOutcomes correspondence implementationOutcome = Some contractOutcome ->
    exists implementationResidue contractResidue,
      implementationOutcomeResidues implementationOperation implementationOutcome = Some implementationResidue /\
      contractOutcomeResidues operationContract contractOutcome = Some contractResidue /\
      implementationResidue = contractResidue.
Proof.
  intros operationContract implementationOperation correspondence implementationOutcome contractOutcome
    Hqualified Hmapping.
  destruct Hqualified as [_ [_ [_ Hsound]]].
  eapply Hsound.
  exact Hmapping.
Qed.

Theorem exact_resource_residue_preserves_all_categories :
  forall expected actual,
    expected = actual ->
    sameSet (residueBorrowedInputs expected) (residueBorrowedInputs actual) /\
    sameSet (residueConsumedInputs expected) (residueConsumedInputs actual) /\
    sameSet (residueReturnedPredecessors expected) (residueReturnedPredecessors actual) /\
    sameSet (residueSuccessors expected) (residueSuccessors actual) /\
    sameSet (residueProducedResources expected) (residueProducedResources actual).
Proof.
  intros expected actual Hequal.
  subst actual.
  unfold sameSet.
  repeat split; intros element; reflexivity.
Qed.

Theorem implementation_symbols_are_nonsemantic :
  forall contract implementation claim symbols,
    ProviderQualifies contract implementation claim ->
    ProviderQualifies contract (withProviderSymbols symbols implementation) claim.
Proof.
  intros contract implementation claim symbols Hqualified.
  unfold ProviderQualifies, withProviderSymbols in *.
  simpl.
  exact Hqualified.
Qed.

Theorem qualified_operation_never_strengthens_authority :
  forall operationContract implementationOperation correspondence,
    ProviderOperationQualifies operationContract implementationOperation correspondence ->
    setSubset
      (surfaceAuthority (implementationCallableSurface implementationOperation))
      (surfaceAuthority (contractCallableSurface operationContract)).
Proof.
  intros operationContract implementationOperation correspondence Hqualified.
  apply refinement_never_strengthens_caller_authority.
  exact (proj1 Hqualified).
Qed.

Theorem qualified_operation_never_widens_effects :
  forall operationContract implementationOperation correspondence,
    ProviderOperationQualifies operationContract implementationOperation correspondence ->
    setSubset
      (surfaceEffects (implementationCallableSurface implementationOperation))
      (surfaceEffects (contractCallableSurface operationContract)).
Proof.
  intros operationContract implementationOperation correspondence Hqualified.
  apply refinement_never_widens_effects.
  exact (proj1 Hqualified).
Qed.

Theorem qualified_operation_never_adds_failures :
  forall operationContract implementationOperation correspondence,
    ProviderOperationQualifies operationContract implementationOperation correspondence ->
    setSubset
      (surfaceFailures (implementationCallableSurface implementationOperation))
      (surfaceFailures (contractCallableSurface operationContract)).
Proof.
  intros operationContract implementationOperation correspondence Hqualified.
  apply refinement_never_adds_failures.
  exact (proj1 Hqualified).
Qed.
