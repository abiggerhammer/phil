From Stdlib Require Import Bool.Bool Arith.PeanoNat.

(*
  PHIL-GEN-CATEGORY-001 — exact generic requirement-category fidelity (GEN-014).

  This normalized model captures the semantic handoff contract implemented by
  Phil.Core.Generic.RequirementCategory. Concrete Text/SemanticForm identity,
  finite Map/Set normalization, duplicate detection/order, diagnostic payloads,
  and the truth/competence of each category-specific checker remain explicit
  correspondence or predecessor boundaries.
*)

Inductive GenericRequirementCategory : Type :=
| GenericStructuralCategory
| GenericPropositionCategory
| GenericProviderCategory
| GenericCallableCategory
| GenericBoundaryCategory
| GenericArchitectureCategory
| GenericEffectsCategory
| GenericAuthorityCategory
| GenericBoundaryRepresentationCategory
| GenericRepresentationCategory
| GenericPlacementCategory
| GenericCostCategory
| GenericEnvironmentCategory.

Inductive GenericRequirementCompetence : Type :=
| StructuralRequirementChecker
| PropositionRequirementChecker
| ProviderRequirementChecker
| CallableRequirementChecker
| BoundaryRequirementChecker
| ArchitectureRequirementChecker
| EffectsRequirementChecker
| AuthorityRequirementChecker
| BoundaryRepresentationRequirementChecker
| RepresentationRequirementChecker
| PlacementRequirementChecker
| CostRequirementChecker
| EnvironmentRequirementChecker.

Definition competenceForRequirementCategory
  (category : GenericRequirementCategory) : GenericRequirementCompetence :=
  match category with
  | GenericStructuralCategory => StructuralRequirementChecker
  | GenericPropositionCategory => PropositionRequirementChecker
  | GenericProviderCategory => ProviderRequirementChecker
  | GenericCallableCategory => CallableRequirementChecker
  | GenericBoundaryCategory => BoundaryRequirementChecker
  | GenericArchitectureCategory => ArchitectureRequirementChecker
  | GenericEffectsCategory => EffectsRequirementChecker
  | GenericAuthorityCategory => AuthorityRequirementChecker
  | GenericBoundaryRepresentationCategory => BoundaryRepresentationRequirementChecker
  | GenericRepresentationCategory => RepresentationRequirementChecker
  | GenericPlacementCategory => PlacementRequirementChecker
  | GenericCostCategory => CostRequirementChecker
  | GenericEnvironmentCategory => EnvironmentRequirementChecker
  end.

Theorem competence_for_requirement_category_is_injective :
  forall first second,
    competenceForRequirementCategory first =
    competenceForRequirementCategory second ->
    first = second.
Proof.
  intros first second Hequal.
  destruct first, second; simpl in Hequal; try discriminate; reflexivity.
Qed.

Definition GenericRequirementKey := nat.
Definition GenericRequirementSemanticForm := nat.
Definition GenericAssumptionDetail := nat.

Record GenericPublicRequirement : Type := mkGenericPublicRequirement {
  requirementKey : GenericRequirementKey;
  requirementCategory : GenericRequirementCategory;
  requirementSemanticForm : GenericRequirementSemanticForm
}.

Inductive GenericRequirementHandoffTarget : Type :=
| GenericHandoffToCompetence (competence : GenericRequirementCompetence)
| GenericHandoffAsAssumption (detail : GenericAssumptionDetail).

Record GenericRequirementHandoff : Type := mkGenericRequirementHandoff {
  handoffRequirementKey : GenericRequirementKey;
  handoffRequirementCategory : GenericRequirementCategory;
  handoffTarget : GenericRequirementHandoffTarget
}.

Record CheckedGenericRequirementHandoff : Type := mkCheckedGenericRequirementHandoff {
  checkedRequirementKey : GenericRequirementKey;
  checkedRequirementCategory : GenericRequirementCategory;
  checkedRequirementSemanticForm : GenericRequirementSemanticForm;
  checkedRequirementCompetence : GenericRequirementCompetence
}.

Definition RequirementHandoffAccepts
  (requirement : GenericPublicRequirement)
  (handoff : GenericRequirementHandoff)
  (checked : CheckedGenericRequirementHandoff) : Prop :=
  handoffRequirementKey handoff = requirementKey requirement /\
  handoffRequirementCategory handoff = requirementCategory requirement /\
  handoffTarget handoff =
    GenericHandoffToCompetence
      (competenceForRequirementCategory (requirementCategory requirement)) /\
  checkedRequirementKey checked = requirementKey requirement /\
  checkedRequirementCategory checked = requirementCategory requirement /\
  checkedRequirementSemanticForm checked = requirementSemanticForm requirement /\
  checkedRequirementCompetence checked =
    competenceForRequirementCategory (requirementCategory requirement).

Theorem accepted_handoff_preserves_exact_requirement_identity :
  forall requirement handoff checked,
    RequirementHandoffAccepts requirement handoff checked ->
    checkedRequirementKey checked = requirementKey requirement /\
    checkedRequirementCategory checked = requirementCategory requirement /\
    checkedRequirementSemanticForm checked = requirementSemanticForm requirement /\
    checkedRequirementCompetence checked =
      competenceForRequirementCategory (requirementCategory requirement).
Proof.
  intros requirement handoff checked Haccepts.
  destruct Haccepts as [_ [_ [_ Hchecked]]].
  exact Hchecked.
Qed.

Theorem category_substitution_cannot_be_accepted :
  forall requirement handoff checked,
    handoffRequirementCategory handoff <> requirementCategory requirement ->
    ~ RequirementHandoffAccepts requirement handoff checked.
Proof.
  intros requirement handoff checked Hmismatch Haccepts.
  destruct Haccepts as [_ [Hcategory _]].
  exact (Hmismatch Hcategory).
Qed.

Theorem silent_assumption_cannot_be_a_generic_handoff :
  forall requirement handoff checked detail,
    handoffTarget handoff = GenericHandoffAsAssumption detail ->
    ~ RequirementHandoffAccepts requirement handoff checked.
Proof.
  intros requirement handoff checked detail Hassumption Haccepts.
  destruct Haccepts as [_ [_ [Htarget _]]].
  rewrite Hassumption in Htarget.
  discriminate Htarget.
Qed.

Theorem wrong_competence_cannot_be_accepted :
  forall requirement handoff checked actualCompetence,
    handoffTarget handoff = GenericHandoffToCompetence actualCompetence ->
    actualCompetence <>
      competenceForRequirementCategory (requirementCategory requirement) ->
    ~ RequirementHandoffAccepts requirement handoff checked.
Proof.
  intros requirement handoff checked actualCompetence Htarget Hwrong Haccepts.
  destruct Haccepts as [_ [_ [Hexact _]]].
  rewrite Htarget in Hexact.
  inversion Hexact.
  contradiction.
Qed.

Theorem competence_identity_fixes_requirement_category :
  forall firstCategory secondCategory,
    competenceForRequirementCategory firstCategory =
      competenceForRequirementCategory secondCategory ->
    firstCategory = secondCategory.
Proof.
  exact competence_for_requirement_category_is_injective.
Qed.

Definition GenericRequirementRegistry :=
  GenericRequirementKey -> option GenericPublicRequirement.

Definition GenericHandoffRegistry :=
  GenericRequirementKey -> option GenericRequirementHandoff.

Definition CheckedGenericRequirementRegistry :=
  GenericRequirementKey -> option CheckedGenericRequirementHandoff.

Record CheckedGenericRequirementInterfaceValid
  (requirements : GenericRequirementRegistry)
  (handoffs : GenericHandoffRegistry)
  (checked : CheckedGenericRequirementRegistry) : Prop :=
  mkCheckedGenericRequirementInterfaceValid {
    interfaceExactHandoffDomain :
      forall key,
        (exists requirement, requirements key = Some requirement) <->
        (exists handoff, handoffs key = Some handoff);

    interfaceExactCheckedDomain :
      forall key,
        (exists requirement, requirements key = Some requirement) <->
        (exists result, checked key = Some result);

    interfaceEveryRequirementAccepted :
      forall key requirement,
        requirements key = Some requirement ->
        exists handoff result,
          handoffs key = Some handoff /\
          checked key = Some result /\
          RequirementHandoffAccepts requirement handoff result
  }.

Theorem missing_handoff_prevents_interface_acceptance :
  forall requirements handoffs checked key requirement,
    requirements key = Some requirement ->
    handoffs key = None ->
    ~ CheckedGenericRequirementInterfaceValid requirements handoffs checked.
Proof.
  intros requirements handoffs checked key requirement Hrequirement Hmissing Hvalid.
  pose proof
    (interfaceExactHandoffDomain requirements handoffs checked Hvalid key)
    as Hdomain.
  destruct Hdomain as [Hforward _].
  destruct (Hforward (ex_intro _ requirement Hrequirement)) as [handoff Hpresent].
  rewrite Hmissing in Hpresent.
  discriminate Hpresent.
Qed.

Theorem unexpected_handoff_prevents_interface_acceptance :
  forall requirements handoffs checked key handoff,
    requirements key = None ->
    handoffs key = Some handoff ->
    ~ CheckedGenericRequirementInterfaceValid requirements handoffs checked.
Proof.
  intros requirements handoffs checked key handoff Hmissing Hhandoff Hvalid.
  pose proof
    (interfaceExactHandoffDomain requirements handoffs checked Hvalid key)
    as Hdomain.
  destruct Hdomain as [_ Hbackward].
  destruct (Hbackward (ex_intro _ handoff Hhandoff)) as [requirement Hpresent].
  rewrite Hmissing in Hpresent.
  discriminate Hpresent.
Qed.

Theorem accepted_interface_preserves_every_requirement_category_and_payload :
  forall requirements handoffs checked key requirement,
    CheckedGenericRequirementInterfaceValid requirements handoffs checked ->
    requirements key = Some requirement ->
    exists handoff result,
      handoffs key = Some handoff /\
      checked key = Some result /\
      checkedRequirementKey result = requirementKey requirement /\
      checkedRequirementCategory result = requirementCategory requirement /\
      checkedRequirementSemanticForm result = requirementSemanticForm requirement /\
      checkedRequirementCompetence result =
        competenceForRequirementCategory (requirementCategory requirement).
Proof.
  intros requirements handoffs checked key requirement Hvalid Hrequirement.
  destruct
    (interfaceEveryRequirementAccepted
      requirements handoffs checked Hvalid key requirement Hrequirement)
    as [handoff [result [Hhandoff [Hchecked Haccepts]]]].
  exists handoff, result.
  split.
  - exact Hhandoff.
  - split.
    + exact Hchecked.
    + exact (accepted_handoff_preserves_exact_requirement_identity
        requirement handoff result Haccepts).
Qed.
