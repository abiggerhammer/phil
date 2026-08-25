From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat.

Import ListNotations.

From Phil.Core Require Import GenericStructural GenericRequirements.

(*
  PHIL-GEN-INST-001 — exact generic requirement discharge.

  This model is deliberately layered on the certified PHIL-GEN-STRUCT-001
  structural algebra and the PHIL-GEN-REQ-001 stabilized-public-requirement
  model.  Requirement identities are normalized semantic atoms here: provider
  InterfaceRevision and proposition identity are represented by nat, while
  structural requirements reuse the already-certified StructuralPermission and
  Mode definitions.

  Provider refinement is an already-checked input relation.  This theorem family
  proves that instantiation checks the exact target relation it is given; it
  does not prove ADR-021 provider qualification or proposition truth.
*)

Inductive GenericRequirement : Type :=
| StructuralRequirement (permission : StructuralPermission)
| ProviderRequirement (requiredInterface : nat)
| PropositionRequirement (proposition : nat).

Inductive GenericRequirementDisposition : Type :=
| SatisfiedByStructuralMode (mode : Mode)
| SatisfiedByExactProvider (actualInterface : nat)
| SatisfiedByCheckedProviderRefinement
    (actualInterface refinementTarget : nat)
| SatisfiedByEvidence (evidenceProposition : nat)
| AssumptionDependent
| Exported.

Record GenericInstantiationPolicy : Type := mkInstantiationPolicy {
  allowsAssumptions : bool;
  allowsExports : bool
}.

Definition strictInstantiationPolicy : GenericInstantiationPolicy :=
  mkInstantiationPolicy false false.

Definition dispositionValid
  (policy : GenericInstantiationPolicy)
  (requirement : GenericRequirement)
  (disposition : GenericRequirementDisposition) : bool :=
  match requirement, disposition with
  | StructuralRequirement permission, SatisfiedByStructuralMode mode =>
      modeAllowsStructuralPermission mode permission
  | ProviderRequirement required, SatisfiedByExactProvider actual =>
      Nat.eqb actual required
  | ProviderRequirement required,
      SatisfiedByCheckedProviderRefinement _ target =>
      Nat.eqb target required
  | PropositionRequirement expected, SatisfiedByEvidence actual =>
      Nat.eqb actual expected
  | _, AssumptionDependent => allowsAssumptions policy
  | _, Exported => allowsExports policy
  | _, _ => false
  end.

Definition exactDispositionDomain
  (requirements : list GenericRequirement)
  (dispositions : list (GenericRequirement * GenericRequirementDisposition))
  : Prop :=
  NoDup (map fst dispositions) /\
  (forall requirement,
      In requirement requirements ->
      exists disposition, In (requirement, disposition) dispositions) /\
  (forall requirement disposition,
      In (requirement, disposition) dispositions ->
      In requirement requirements).

Definition acceptedInstantiation
  (policy : GenericInstantiationPolicy)
  (requirements : list GenericRequirement)
  (dispositions : list (GenericRequirement * GenericRequirementDisposition))
  : Prop :=
  exactDispositionDomain requirements dispositions /\
  forall requirement disposition,
    In (requirement, disposition) dispositions ->
    dispositionValid policy requirement disposition = true.

Theorem accepted_instantiation_has_no_duplicate_requirement_keys :
  forall policy requirements dispositions,
    acceptedInstantiation policy requirements dispositions ->
    NoDup (map fst dispositions).
Proof.
  intros policy requirements dispositions Haccepted.
  destruct Haccepted as [[Hnodup [_ _]] _].
  exact Hnodup.
Qed.

Theorem accepted_instantiation_has_disposition_for_every_requirement :
  forall policy requirements dispositions requirement,
    acceptedInstantiation policy requirements dispositions ->
    In requirement requirements ->
    exists disposition, In (requirement, disposition) dispositions.
Proof.
  intros policy requirements dispositions requirement Haccepted Hin.
  destruct Haccepted as [[_ [Hcomplete _]] _].
  apply Hcomplete.
  exact Hin.
Qed.

Theorem accepted_instantiation_has_no_unexposed_disposition :
  forall policy requirements dispositions requirement disposition,
    acceptedInstantiation policy requirements dispositions ->
    In (requirement, disposition) dispositions ->
    In requirement requirements.
Proof.
  intros policy requirements dispositions requirement disposition Haccepted Hin.
  destruct Haccepted as [[_ [_ Hexpected]] _].
  apply (Hexpected requirement disposition).
  exact Hin.
Qed.

Theorem missing_requirement_never_becomes_implicit_assumption :
  forall policy requirement,
    ~ acceptedInstantiation policy [requirement] [].
Proof.
  intros policy requirement Haccepted.
  destruct Haccepted as [[_ [Hcomplete _]] _].
  specialize (Hcomplete requirement (or_introl eq_refl)).
  destruct Hcomplete as [disposition Hin].
  inversion Hin.
Qed.

Theorem duplicate_requirement_dispositions_reject :
  forall policy requirement first second,
    ~ acceptedInstantiation policy [requirement]
        [(requirement, first); (requirement, second)].
Proof.
  intros policy requirement first second Haccepted.
  pose proof
    (accepted_instantiation_has_no_duplicate_requirement_keys
      policy [requirement]
      [(requirement, first); (requirement, second)] Haccepted) as Hnodup.
  simpl in Hnodup.
  inversion Hnodup as [|x xs Hnotin Htail].
  apply Hnotin.
  simpl.
  auto.
Qed.

Theorem unexposed_requirement_disposition_rejects :
  forall policy requirement disposition,
    ~ acceptedInstantiation policy [] [(requirement, disposition)].
Proof.
  intros policy requirement disposition Haccepted.
  pose proof
    (accepted_instantiation_has_no_unexposed_disposition
      policy [] [(requirement, disposition)]
      requirement disposition Haccepted (or_introl eq_refl)) as Hin.
  inversion Hin.
Qed.

Theorem accepted_disposition_is_valid :
  forall policy requirements dispositions requirement disposition,
    acceptedInstantiation policy requirements dispositions ->
    In (requirement, disposition) dispositions ->
    dispositionValid policy requirement disposition = true.
Proof.
  intros policy requirements dispositions requirement disposition Haccepted Hin.
  destruct Haccepted as [_ Hvalid].
  apply (Hvalid requirement disposition).
  exact Hin.
Qed.

Theorem exact_provider_satisfaction_requires_exact_interface :
  forall required actual,
    dispositionValid strictInstantiationPolicy
      (ProviderRequirement required)
      (SatisfiedByExactProvider actual) = true ->
    actual = required.
Proof.
  intros required actual Hvalid.
  simpl in Hvalid.
  apply Nat.eqb_eq.
  exact Hvalid.
Qed.

Theorem merely_different_nominal_provider_does_not_satisfy :
  forall required actual,
    actual <> required ->
    dispositionValid strictInstantiationPolicy
      (ProviderRequirement required)
      (SatisfiedByExactProvider actual) = false.
Proof.
  intros required actual Hneq.
  simpl.
  apply Nat.eqb_neq.
  exact Hneq.
Qed.

Theorem checked_provider_refinement_must_target_exact_required_interface :
  forall required actual target,
    dispositionValid strictInstantiationPolicy
      (ProviderRequirement required)
      (SatisfiedByCheckedProviderRefinement actual target) = true ->
    target = required.
Proof.
  intros required actual target Hvalid.
  simpl in Hvalid.
  apply Nat.eqb_eq.
  exact Hvalid.
Qed.

Theorem provider_binding_does_not_discharge_proposition_requirement :
  forall proposition providerInterface,
    dispositionValid strictInstantiationPolicy
      (PropositionRequirement proposition)
      (SatisfiedByExactProvider providerInterface) = false.
Proof.
  reflexivity.
Qed.

Theorem proposition_evidence_must_name_exact_proposition :
  forall expected actual,
    dispositionValid strictInstantiationPolicy
      (PropositionRequirement expected)
      (SatisfiedByEvidence actual) = true ->
    actual = expected.
Proof.
  intros expected actual Hvalid.
  simpl in Hvalid.
  apply Nat.eqb_eq.
  exact Hvalid.
Qed.

Theorem evidence_for_other_proposition_rejects :
  forall expected actual,
    actual <> expected ->
    dispositionValid strictInstantiationPolicy
      (PropositionRequirement expected)
      (SatisfiedByEvidence actual) = false.
Proof.
  intros expected actual Hneq.
  simpl.
  apply Nat.eqb_neq.
  exact Hneq.
Qed.

Theorem strict_policy_rejects_assumption_disposition :
  forall requirement,
    dispositionValid strictInstantiationPolicy requirement AssumptionDependent = false.
Proof.
  intros requirement.
  destruct requirement; reflexivity.
Qed.

Theorem explicit_assumption_policy_admits_assumption_disposition :
  forall requirement exports,
    dispositionValid (mkInstantiationPolicy true exports)
      requirement AssumptionDependent = true.
Proof.
  intros requirement exports.
  destruct requirement; reflexivity.
Qed.

Theorem strict_policy_rejects_export_disposition :
  forall requirement,
    dispositionValid strictInstantiationPolicy requirement Exported = false.
Proof.
  intros requirement.
  destruct requirement; reflexivity.
Qed.

Theorem explicit_export_policy_admits_export_disposition :
  forall requirement assumptions,
    dispositionValid (mkInstantiationPolicy assumptions true)
      requirement Exported = true.
Proof.
  intros requirement assumptions.
  destruct requirement; reflexivity.
Qed.

Theorem affine_satisfies_structural_weakening_requirement :
  dispositionValid strictInstantiationPolicy
    (StructuralRequirement WeakeningPermission)
    (SatisfiedByStructuralMode Affine) = true.
Proof.
  reflexivity.
Qed.

Theorem linear_rejects_structural_weakening_requirement :
  dispositionValid strictInstantiationPolicy
    (StructuralRequirement WeakeningPermission)
    (SatisfiedByStructuralMode Linear) = false.
Proof.
  reflexivity.
Qed.

Theorem wrong_disposition_kind_rejects :
  forall required proposition,
    dispositionValid strictInstantiationPolicy
      (ProviderRequirement required)
      (SatisfiedByEvidence proposition) = false.
Proof.
  reflexivity.
Qed.

Theorem strict_accepted_instantiation_contains_no_assumptions :
  forall requirements dispositions requirement,
    acceptedInstantiation strictInstantiationPolicy requirements dispositions ->
    In (requirement, AssumptionDependent) dispositions -> False.
Proof.
  intros requirements dispositions requirement Haccepted Hin.
  pose proof
    (accepted_disposition_is_valid strictInstantiationPolicy requirements dispositions
      requirement AssumptionDependent Haccepted Hin) as Hvalid.
  rewrite strict_policy_rejects_assumption_disposition in Hvalid.
  discriminate.
Qed.

Theorem strict_accepted_instantiation_contains_no_exports :
  forall requirements dispositions requirement,
    acceptedInstantiation strictInstantiationPolicy requirements dispositions ->
    In (requirement, Exported) dispositions -> False.
Proof.
  intros requirements dispositions requirement Haccepted Hin.
  pose proof
    (accepted_disposition_is_valid strictInstantiationPolicy requirements dispositions
      requirement Exported Haccepted Hin) as Hvalid.
  rewrite strict_policy_rejects_export_disposition in Hvalid.
  discriminate.
Qed.
