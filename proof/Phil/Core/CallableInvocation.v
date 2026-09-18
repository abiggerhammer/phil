From Stdlib Require Import Bool.Bool Arith.PeanoNat.

From Phil.Core Require Import
  AuthorityPossession
  CallableEffects
  CallableLifecycle
  CallableRefinement
  CallableOutcomeFidelity.

(*
  PHIL-CALL-INVOKE-001 / CALL-019 — ordinary callable invocation composition.

  This theorem family starts after ordinary Surface expression checking has
  established argument/result shape and structural transfer.  It composes the
  already-Certified callable/authority authorities rather than redefining them:

  - exact semantic callable resolution by declaration identity;
  - possessed caller authority;
  - callable refinement and effect/failure confinement;
  - exact outcome-class coverage and exact branch semantic buckets;
  - distinct continuing, declared-terminal, and declared-fatal caller control;
  - exact residual-obligation and caller-resource correspondence; and
  - exact Preserve/Consume/Replace callee lifecycle.

  Concrete Text/Map/Set/list normalization, SourceSpan identity, source traversal,
  diagnostic ordering, source elaboration, and GHC/runtime behavior remain
  explicit implementation-correspondence boundaries.
*)

Definition InvocationDeclarationKey := nat.

Record InvocationResolutionFacts : Type := mkInvocationResolutionFacts {
  invocationSurfaceAccepted : bool;
  invocationResolvedDeclaration : InvocationDeclarationKey;
  invocationSemanticContractDeclaration : InvocationDeclarationKey;
  invocationOrdinaryCallableNamespace : bool
}.

Definition InvocationResolutionValid
  (resolution : InvocationResolutionFacts) : Prop :=
  invocationSurfaceAccepted resolution = true /\
  invocationResolvedDeclaration resolution <> 0 /\
  invocationResolvedDeclaration resolution =
    invocationSemanticContractDeclaration resolution /\
  invocationOrdinaryCallableNamespace resolution = true.

Definition InvocationAuthorityRequirementSet : Type :=
  AuthorityRequirement -> bool.

Definition InvocationAuthorityEnvironment : Type :=
  AuthorityRequirement -> option AuthorityCapability.

Definition InvocationAuthorityValid
  (required : InvocationAuthorityRequirementSet)
  (available : InvocationAuthorityEnvironment) : Prop :=
  forall requirement,
    required requirement = true ->
    exists capability,
      available requirement = Some capability /\
      authorityExerciseAllowed
        requirement
        PossessedCapability
        capability = true.

Inductive InvocationOutcomeClass : Type :=
| InvocationSuccess
| InvocationTypedNegative : nat -> InvocationOutcomeClass
| InvocationDeclaredTerminal : nat -> InvocationOutcomeClass
| InvocationFatal : nat -> InvocationOutcomeClass.

Inductive InvocationCallerControl : Type :=
| InvocationCallerContinues
| InvocationCallerTerminates : nat -> InvocationCallerControl
| InvocationCallerFatals : nat -> InvocationCallerControl.

Definition exactInvocationCallerControl
  (outcomeClass : InvocationOutcomeClass)
  (control : InvocationCallerControl) : bool :=
  match outcomeClass, control with
  | InvocationSuccess, InvocationCallerContinues => true
  | InvocationTypedNegative _, InvocationCallerContinues => true
  | InvocationDeclaredTerminal expected, InvocationCallerTerminates actual =>
      Nat.eqb expected actual
  | InvocationFatal expected, InvocationCallerFatals actual =>
      Nat.eqb expected actual
  | _, _ => false
  end.

Record InvocationOutcomeBranchFacts : Type := mkInvocationOutcomeBranchFacts {
  invocationBranchClass : InvocationOutcomeClass;
  invocationBranchControl : InvocationCallerControl;
  invocationBranchExpectedState : nat;
  invocationBranchActualState : nat;
  invocationBranchExpectedTransition : nat;
  invocationBranchActualTransition : nat;
  invocationBranchExpectedPostconditions : nat;
  invocationBranchActualPostconditions : nat;
  invocationBranchExpectedResidual : nat;
  invocationBranchActualResidual : nat;
  invocationBranchExpectedAssumptions : nat;
  invocationBranchActualAssumptions : nat;
  invocationBranchExpectedEffects : nat;
  invocationBranchActualEffects : nat;
  invocationBranchExpectedDischarged : nat;
  invocationBranchActualDischarged : nat;
  invocationBranchResidualDisposition : ResidualDisposition
}.

Definition InvocationOutcomeBranchValid
  (branch : InvocationOutcomeBranchFacts) : Prop :=
  checkOutcomeBranch
    (invocationBranchExpectedState branch)
    (invocationBranchActualState branch)
    (invocationBranchExpectedTransition branch)
    (invocationBranchActualTransition branch)
    (invocationBranchExpectedPostconditions branch)
    (invocationBranchActualPostconditions branch)
    (invocationBranchExpectedResidual branch)
    (invocationBranchActualResidual branch)
    (invocationBranchExpectedAssumptions branch)
    (invocationBranchActualAssumptions branch)
    (invocationBranchExpectedEffects branch)
    (invocationBranchActualEffects branch)
    (invocationBranchExpectedDischarged branch)
    (invocationBranchActualDischarged branch)
    (invocationBranchResidualDisposition branch) =
      CallableOutcomeSuccess /\
  exactInvocationCallerControl
    (invocationBranchClass branch)
    (invocationBranchControl branch) = true.

Definition InvocationOutcomeClassSet : Type := nat -> bool.
Definition InvocationOutcomeEnvironment : Type :=
  nat -> option InvocationOutcomeBranchFacts.

Definition sameInvocationOutcomeClassSet
  (first second : InvocationOutcomeClassSet) : Prop :=
  forall key, first key = second key.

Definition InvocationOutcomeClosureValid
  (expected actual : InvocationOutcomeClassSet)
  (branches : InvocationOutcomeEnvironment) : Prop :=
  sameInvocationOutcomeClassSet expected actual /\
  (forall key,
    expected key = true ->
    exists branch,
      branches key = Some branch /\
      InvocationOutcomeBranchValid branch) /\
  (forall key branch,
    branches key = Some branch ->
    expected key = true).

Inductive InvocationLifecycleEvidence : Type :=
| InvocationPreserveLifecycle :
    CaptureSet -> CaptureSet -> option CallableSuccessor ->
    InvocationLifecycleEvidence
| InvocationConsumeLifecycle :
    CaptureSet -> option CallableSuccessor ->
    InvocationLifecycleEvidence
| InvocationReplaceLifecycle :
    nat -> ResourceState -> nat -> option nat ->
    CaptureSet -> option CallableSuccessor ->
    InvocationLifecycleEvidence.

Definition InvocationLifecycleValid
  (evidence : InvocationLifecycleEvidence) : Prop :=
  match evidence with
  | InvocationPreserveLifecycle expectedResidue actualResidue successor =>
      preserveTransitionValid expectedResidue actualResidue successor
  | InvocationConsumeLifecycle actualResidue successor =>
      consumeTransitionValid actualResidue successor
  | InvocationReplaceLifecycle
      predecessor state expectedInterface expectedState actualResidue successor =>
      replaceTransitionValid
        predecessor state expectedInterface expectedState actualResidue successor
  end.

Record CallableInvocationFacts : Type := mkCallableInvocationFacts {
  callableInvocationResolution : InvocationResolutionFacts;
  callableInvocationRequiredAuthority : InvocationAuthorityRequirementSet;
  callableInvocationAuthorityEnvironment : InvocationAuthorityEnvironment;
  callableInvocationExpectedSurface : CallableRefinementSurface;
  callableInvocationActualSurface : CallableRefinementSurface;
  callableInvocationEffectInterface : nat;
  callableInvocationInferredEffects : EffectSet;
  callableInvocationPublicEffects : EffectSet;
  callableInvocationCheckedEffects : CheckedEffectBound;
  callableInvocationReachableFailures : BoolSet;
  callableInvocationPublicFailures : BoolSet;
  callableInvocationExpectedOutcomeClasses : InvocationOutcomeClassSet;
  callableInvocationActualOutcomeClasses : InvocationOutcomeClassSet;
  callableInvocationOutcomeBranches : InvocationOutcomeEnvironment;
  callableInvocationResidualObligationsExact : bool;
  callableInvocationCallerResourceResidueExact : bool;
  callableInvocationLifecycleEvidence : InvocationLifecycleEvidence
}.

Definition CallableInvocationValid
  (facts : CallableInvocationFacts) : Prop :=
  InvocationResolutionValid (callableInvocationResolution facts) /\
  InvocationAuthorityValid
    (callableInvocationRequiredAuthority facts)
    (callableInvocationAuthorityEnvironment facts) /\
  callableRefines
    (callableInvocationExpectedSurface facts)
    (callableInvocationActualSurface facts) /\
  checkedEffectBoundAllowed
    (callableInvocationEffectInterface facts)
    (callableInvocationInferredEffects facts)
    (callableInvocationPublicEffects facts)
    (callableInvocationCheckedEffects facts) /\
  setSubset
    (callableInvocationReachableFailures facts)
    (callableInvocationPublicFailures facts) /\
  InvocationOutcomeClosureValid
    (callableInvocationExpectedOutcomeClasses facts)
    (callableInvocationActualOutcomeClasses facts)
    (callableInvocationOutcomeBranches facts) /\
  callableInvocationResidualObligationsExact facts = true /\
  callableInvocationCallerResourceResidueExact facts = true /\
  InvocationLifecycleValid (callableInvocationLifecycleEvidence facts).

Theorem accepted_invocation_uses_exact_semantic_declaration :
  forall facts,
    CallableInvocationValid facts ->
    invocationResolvedDeclaration (callableInvocationResolution facts) =
      invocationSemanticContractDeclaration
        (callableInvocationResolution facts).
Proof.
  intros facts Hvalid.
  destruct Hvalid as [Hresolution _].
  exact (proj1 (proj2 (proj2 Hresolution))).
Qed.

Theorem accepted_invocation_is_ordinary_callable_namespace :
  forall facts,
    CallableInvocationValid facts ->
    invocationOrdinaryCallableNamespace
      (callableInvocationResolution facts) = true.
Proof.
  intros facts Hvalid.
  destruct Hvalid as [Hresolution _].
  exact (proj2 (proj2 (proj2 Hresolution))).
Qed.

Theorem accepted_invocation_authority_is_possession_backed :
  forall facts requirement,
    CallableInvocationValid facts ->
    callableInvocationRequiredAuthority facts requirement = true ->
    exists capability,
      callableInvocationAuthorityEnvironment facts requirement =
        Some capability /\
      authorityExerciseAllowed requirement PossessedCapability capability = true.
Proof.
  intros facts requirement Hvalid Hrequired.
  destruct Hvalid as [_ [Hauthority _]].
  eapply Hauthority.
  exact Hrequired.
Qed.

Theorem accepted_invocation_never_widens_callable_effects :
  forall facts,
    CallableInvocationValid facts ->
    setSubset
      (surfaceEffects (callableInvocationActualSurface facts))
      (surfaceEffects (callableInvocationExpectedSurface facts)).
Proof.
  intros facts Hvalid.
  destruct Hvalid as [_ [_ [Hrefinement _]]].
  apply refinement_never_widens_effects.
  exact Hrefinement.
Qed.

Theorem accepted_invocation_never_adds_callable_failures :
  forall facts,
    CallableInvocationValid facts ->
    setSubset
      (surfaceFailures (callableInvocationActualSurface facts))
      (surfaceFailures (callableInvocationExpectedSurface facts)).
Proof.
  intros facts Hvalid.
  destruct Hvalid as [_ [_ [Hrefinement _]]].
  apply refinement_never_adds_failures.
  exact Hrefinement.
Qed.

Theorem accepted_invocation_keeps_exact_callee_transition :
  forall facts,
    CallableInvocationValid facts ->
    surfaceTransition (callableInvocationActualSurface facts) =
      surfaceTransition (callableInvocationExpectedSurface facts).
Proof.
  intros facts Hvalid.
  destruct Hvalid as [_ [_ [Hrefinement _]]].
  apply refinement_requires_exact_callee_transition.
  exact Hrefinement.
Qed.

Theorem accepted_invocation_effects_fit_caller_bound :
  forall facts,
    CallableInvocationValid facts ->
    effectSubset
      (callableInvocationInferredEffects facts)
      (callableInvocationPublicEffects facts).
Proof.
  intros facts Hvalid.
  destruct Hvalid as [_ [_ [_ [Heffects _]]]].
  exact (proj2 (proj2 (proj2 Heffects))).
Qed.

Theorem accepted_invocation_failures_fit_caller_bound :
  forall facts,
    CallableInvocationValid facts ->
    setSubset
      (callableInvocationReachableFailures facts)
      (callableInvocationPublicFailures facts).
Proof.
  intros facts Hvalid.
  destruct Hvalid as [_ [_ [_ [_ [Hfailures _]]]]].
  exact Hfailures.
Qed.

Theorem accepted_invocation_has_exact_outcome_domain :
  forall facts,
    CallableInvocationValid facts ->
    sameInvocationOutcomeClassSet
      (callableInvocationExpectedOutcomeClasses facts)
      (callableInvocationActualOutcomeClasses facts).
Proof.
  intros facts Hvalid.
  destruct Hvalid as [_ [_ [_ [_ [_ [Houtcomes _]]]]]].
  exact (proj1 Houtcomes).
Qed.

Theorem accepted_invocation_every_expected_outcome_has_exact_branch :
  forall facts key,
    CallableInvocationValid facts ->
    callableInvocationExpectedOutcomeClasses facts key = true ->
    exists branch,
      callableInvocationOutcomeBranches facts key = Some branch /\
      InvocationOutcomeBranchValid branch.
Proof.
  intros facts key Hvalid Hexpected.
  destruct Hvalid as [_ [_ [_ [_ [_ [Houtcomes _]]]]]].
  destruct Houtcomes as [_ [Hcoverage _]].
  eapply Hcoverage.
  exact Hexpected.
Qed.

Theorem accepted_invocation_branch_preserves_all_semantic_buckets :
  forall branch,
    InvocationOutcomeBranchValid branch ->
    invocationBranchExpectedState branch =
      invocationBranchActualState branch /\
    invocationBranchExpectedTransition branch =
      invocationBranchActualTransition branch /\
    invocationBranchResidualDisposition branch = ResidualExact /\
    invocationBranchExpectedResidual branch =
      invocationBranchActualResidual branch /\
    invocationBranchExpectedPostconditions branch =
      invocationBranchActualPostconditions branch /\
    invocationBranchExpectedAssumptions branch =
      invocationBranchActualAssumptions branch /\
    invocationBranchExpectedEffects branch =
      invocationBranchActualEffects branch /\
    invocationBranchExpectedDischarged branch =
      invocationBranchActualDischarged branch.
Proof.
  intros branch Hvalid.
  destruct Hvalid as [Hbranch _].
  eapply successful_branch_is_exact.
  exact Hbranch.
Qed.

Theorem success_and_typed_negative_continue_exactly :
  forall outcome,
    exactInvocationCallerControl
      InvocationSuccess InvocationCallerContinues = true /\
    exactInvocationCallerControl
      (InvocationTypedNegative outcome) InvocationCallerContinues = true.
Proof.
  intros.
  split; reflexivity.
Qed.

Theorem declared_terminal_control_is_exact_and_not_fatal :
  forall outcome,
    exactInvocationCallerControl
      (InvocationDeclaredTerminal outcome)
      (InvocationCallerTerminates outcome) = true /\
    exactInvocationCallerControl
      (InvocationDeclaredTerminal outcome)
      (InvocationCallerFatals outcome) = false.
Proof.
  intros.
  split.
  - simpl. apply Nat.eqb_refl.
  - reflexivity.
Qed.

Theorem fatal_control_is_exact_and_not_generic_or_declared_terminal :
  forall outcome,
    exactInvocationCallerControl
      (InvocationFatal outcome)
      (InvocationCallerFatals outcome) = true /\
    exactInvocationCallerControl
      (InvocationFatal outcome)
      InvocationCallerContinues = false /\
    exactInvocationCallerControl
      (InvocationFatal outcome)
      (InvocationCallerTerminates outcome) = false.
Proof.
  intros.
  split.
  - simpl. apply Nat.eqb_refl.
  - split; reflexivity.
Qed.

Theorem accepted_invocation_preserves_exact_residual_obligations :
  forall facts,
    CallableInvocationValid facts ->
    callableInvocationResidualObligationsExact facts = true.
Proof.
  intros facts Hvalid.
  destruct Hvalid as [_ [_ [_ [_ [_ [_ [Hresidual _]]]]]]].
  exact Hresidual.
Qed.

Theorem accepted_invocation_preserves_exact_caller_resource_residue :
  forall facts,
    CallableInvocationValid facts ->
    callableInvocationCallerResourceResidueExact facts = true.
Proof.
  intros facts Hvalid.
  destruct Hvalid as [_ [_ [_ [_ [_ [_ [_ [Hresources _]]]]]]]].
  exact Hresources.
Qed.

Theorem accepted_invocation_has_valid_lifecycle :
  forall facts,
    CallableInvocationValid facts ->
    InvocationLifecycleValid (callableInvocationLifecycleEvidence facts).
Proof.
  intros facts Hvalid.
  destruct Hvalid as [_ [_ [_ [_ [_ [_ [_ [_ Hlifecycle]]]]]]]].
  exact Hlifecycle.
Qed.

Theorem preserve_invocation_retains_exact_restricted_residue :
  forall expected actual successor,
    InvocationLifecycleValid
      (InvocationPreserveLifecycle expected actual successor) ->
    sameCaptureSet expected actual.
Proof.
  intros expected actual successor Hvalid.
  apply preserve_requires_exact_restricted_residue with (successor := successor).
  exact Hvalid.
Qed.

Theorem consume_invocation_requires_empty_restricted_residue :
  forall actual successor,
    InvocationLifecycleValid
      (InvocationConsumeLifecycle actual successor) ->
    captureSetEmpty actual.
Proof.
  intros actual successor Hvalid.
  apply consume_requires_empty_restricted_residue with (successor := successor).
  exact Hvalid.
Qed.

Theorem replace_invocation_requires_fresh_distinct_successor :
  forall predecessor state expectedInterface expectedState actual successor,
    InvocationLifecycleValid
      (InvocationReplaceLifecycle
        predecessor state expectedInterface expectedState actual
        (Some successor)) ->
    successorOccurrence successor <> predecessor /\
    state (successorOccurrence successor) = false /\
    successorInterface successor = expectedInterface /\
    successorState successor = expectedState.
Proof.
  intros predecessor state expectedInterface expectedState actual successor Hvalid.
  split.
  - eapply replace_requires_distinct_successor_occurrence.
    exact Hvalid.
  - split.
    + eapply replace_requires_fresh_successor_occurrence.
      exact Hvalid.
    + split.
      * eapply replace_requires_exact_successor_interface.
        exact Hvalid.
      * eapply replace_requires_exact_successor_state.
        exact Hvalid.
Qed.
