From Stdlib Require Import Bool.Bool.
From Phil.Core Require Import GenericInstantiation.
From Phil.Assurance Require Import GenericAssurance.

Inductive GenericAssuranceDecision : Type :=
| GenericAssuranceAccepted
| GenericAssuranceDeclarationMismatch
| GenericAssuranceInterfaceMismatch
| GenericAssuranceDefinitionMismatch
| GenericAssurancePublicRequirementRevisionMismatch
| GenericAssuranceDispositionDomainMismatch.

Definition decideGenericAssuranceByFacts
  (declarationMatches : bool)
  (interfaceMatches : bool)
  (definitionMatches : bool)
  (publicRequirementRevisionsMatch : bool)
  (dispositionDomainMatches : bool)
  : GenericAssuranceDecision :=
  if declarationMatches then
    if interfaceMatches then
      if definitionMatches then
        if publicRequirementRevisionsMatch then
          if dispositionDomainMatches then
            GenericAssuranceAccepted
          else GenericAssuranceDispositionDomainMismatch
        else GenericAssurancePublicRequirementRevisionMismatch
      else GenericAssuranceDefinitionMismatch
    else GenericAssuranceInterfaceMismatch
  else GenericAssuranceDeclarationMismatch.

Theorem declaration_mismatch_is_first :
  forall interfaceMatches definitionMatches revisionsMatch domainMatches,
    decideGenericAssuranceByFacts
      false interfaceMatches definitionMatches revisionsMatch domainMatches =
    GenericAssuranceDeclarationMismatch.
Proof. reflexivity. Qed.

Theorem interface_mismatch_is_second :
  forall definitionMatches revisionsMatch domainMatches,
    decideGenericAssuranceByFacts
      true false definitionMatches revisionsMatch domainMatches =
    GenericAssuranceInterfaceMismatch.
Proof. reflexivity. Qed.

Theorem definition_mismatch_is_third :
  forall revisionsMatch domainMatches,
    decideGenericAssuranceByFacts
      true true false revisionsMatch domainMatches =
    GenericAssuranceDefinitionMismatch.
Proof. reflexivity. Qed.

Theorem public_requirement_revision_mismatch_precedes_domain_check :
  forall domainMatches,
    decideGenericAssuranceByFacts true true true false domainMatches =
    GenericAssurancePublicRequirementRevisionMismatch.
Proof. reflexivity. Qed.

Theorem disposition_domain_mismatch_is_last_rejection :
  decideGenericAssuranceByFacts true true true true false =
  GenericAssuranceDispositionDomainMismatch.
Proof. reflexivity. Qed.

Theorem all_exact_facts_accept :
  decideGenericAssuranceByFacts true true true true true =
  GenericAssuranceAccepted.
Proof. reflexivity. Qed.

Theorem generic_assurance_decision_accept_iff_all_facts :
  forall declarationMatches interfaceMatches definitionMatches
    revisionsMatch domainMatches,
    decideGenericAssuranceByFacts
      declarationMatches interfaceMatches definitionMatches
      revisionsMatch domainMatches = GenericAssuranceAccepted <->
    declarationMatches = true /\
    interfaceMatches = true /\
    definitionMatches = true /\
    revisionsMatch = true /\
    domainMatches = true.
Proof.
  intros declarationMatches interfaceMatches definitionMatches
    revisionsMatch domainMatches.
  split.
  - destruct declarationMatches, interfaceMatches, definitionMatches,
      revisionsMatch, domainMatches; simpl; intros H; try discriminate;
      repeat split; reflexivity.
  - intros [Hdeclaration [Hinterface [Hdefinition [Hrevisions Hdomain]]]].
    rewrite Hdeclaration, Hinterface, Hdefinition, Hrevisions, Hdomain.
    reflexivity.
Qed.

Record GenericAssuranceFactReflection
  (body : ReusableGenericBodyAssurance)
  (currentRequirements : list GenericRequirement)
  (currentRequirementRevisions : list RequirementRevision)
  (lineage : GenericApplicationLineage)
  (declarationMatches interfaceMatches definitionMatches
    revisionsMatch domainMatches : bool) : Prop :=
  mkGenericAssuranceFactReflection {
    declarationFactReflects :
      declarationMatches = true <->
      genericApplicationDeclaration lineage = genericBodyDeclaration body;
    interfaceFactReflects :
      interfaceMatches = true <->
      genericApplicationInterface lineage = genericBodyInterface body;
    definitionFactReflects :
      definitionMatches = true <->
      genericApplicationDefinition lineage = genericBodyDefinition body;
    requirementRevisionFactReflects :
      revisionsMatch = true <->
      currentRequirements = genericBodyRequirements body /\
      currentRequirementRevisions = genericBodyRequirementRevisions body;
    dispositionDomainFactReflects :
      domainMatches = true <->
      exactDispositionDomain
        currentRequirements (genericApplicationDispositions lineage)
  }.

Theorem accepted_generic_assurance_decision_is_sound :
  forall policy body currentRequirements currentRequirementRevisions lineage
    declarationMatches interfaceMatches definitionMatches revisionsMatch domainMatches,
    GenericAssuranceFactReflection
      body currentRequirements currentRequirementRevisions lineage
      declarationMatches interfaceMatches definitionMatches revisionsMatch domainMatches ->
    acceptedInstantiation
      policy currentRequirements (genericApplicationDispositions lineage) ->
    decideGenericAssuranceByFacts
      declarationMatches interfaceMatches definitionMatches revisionsMatch domainMatches =
      GenericAssuranceAccepted ->
    CheckedGenericApplicationAssurance
      policy body currentRequirements currentRequirementRevisions lineage
      (mkGenericApplicationAssurance body lineage).
Proof.
  intros policy body currentRequirements currentRequirementRevisions lineage
    declarationMatches interfaceMatches definitionMatches revisionsMatch domainMatches
    Hreflection Haccepted Hdecision.
  destruct Hreflection as
    [HdeclarationReflects HinterfaceReflects HdefinitionReflects
      HrevisionsReflects HdomainReflects].
  pose proof
    (proj1
      (generic_assurance_decision_accept_iff_all_facts
        declarationMatches interfaceMatches definitionMatches
        revisionsMatch domainMatches) Hdecision) as Hall.
  destruct Hall as
    [Hdeclaration [Hinterface [Hdefinition [Hrevisions Hdomain]]]].
  pose proof (proj1 HdeclarationReflects Hdeclaration) as HdeclarationExact.
  pose proof (proj1 HinterfaceReflects Hinterface) as HinterfaceExact.
  pose proof (proj1 HdefinitionReflects Hdefinition) as HdefinitionExact.
  pose proof (proj1 HrevisionsReflects Hrevisions) as HrequirementExact.
  destruct HrequirementExact as [Hrequirements HrequirementRevisions].
  pose proof (proj1 HdomainReflects Hdomain) as HdomainExact.
  unfold CheckedGenericApplicationAssurance.
  simpl.
  split; [reflexivity |].
  split; [reflexivity |].
  split; [exact HdeclarationExact |].
  split; [exact HinterfaceExact |].
  split; [exact HdefinitionExact |].
  split; [exact Hrequirements |].
  split; [exact HrequirementRevisions |].
  exact Haccepted.
Qed.

Theorem checked_generic_assurance_is_complete_for_reflected_facts :
  forall policy body currentRequirements currentRequirementRevisions lineage assurance
    declarationMatches interfaceMatches definitionMatches revisionsMatch domainMatches,
    GenericAssuranceFactReflection
      body currentRequirements currentRequirementRevisions lineage
      declarationMatches interfaceMatches definitionMatches revisionsMatch domainMatches ->
    CheckedGenericApplicationAssurance
      policy body currentRequirements currentRequirementRevisions lineage assurance ->
    decideGenericAssuranceByFacts
      declarationMatches interfaceMatches definitionMatches revisionsMatch domainMatches =
      GenericAssuranceAccepted.
Proof.
  intros policy body currentRequirements currentRequirementRevisions lineage assurance
    declarationMatches interfaceMatches definitionMatches revisionsMatch domainMatches
    Hreflection Hchecked.
  destruct Hreflection as
    [HdeclarationReflects HinterfaceReflects HdefinitionReflects
      HrevisionsReflects HdomainReflects].
  destruct Hchecked as
    [_ [_ [HdeclarationExact [HinterfaceExact [HdefinitionExact
      [Hrequirements [HrequirementRevisions Haccepted]]]]]]].
  pose proof (proj2 HdeclarationReflects HdeclarationExact) as Hdeclaration.
  pose proof (proj2 HinterfaceReflects HinterfaceExact) as Hinterface.
  pose proof (proj2 HdefinitionReflects HdefinitionExact) as Hdefinition.
  pose proof
    (proj2 HrevisionsReflects (conj Hrequirements HrequirementRevisions))
    as Hrevisions.
  destruct Haccepted as [HdomainExact Hvalid].
  pose proof (proj2 HdomainReflects HdomainExact) as Hdomain.
  apply (proj2
    (generic_assurance_decision_accept_iff_all_facts
      declarationMatches interfaceMatches definitionMatches
      revisionsMatch domainMatches)).
  repeat split; assumption.
Qed.
