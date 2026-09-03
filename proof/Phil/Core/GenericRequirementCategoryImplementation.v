From Stdlib Require Import Bool.Bool.
From Phil.Core Require Import GenericRequirementCategory.

(*
  Executable correspondence for PHIL-GEN-CATEGORY-001.

  Production remains responsible for concrete finite Map/Set/Text/SemanticForm
  facts.  This layer owns only the final representation-neutral semantic
  decisions reflected from those facts.
*)

Inductive RequirementHandoffDecision : Type :=
| RequirementHandoffKeyDecision
| RequirementHandoffCategoryDecision
| RequirementHandoffTargetDecision
| RequirementCheckedKeyDecision
| RequirementCheckedCategoryDecision
| RequirementCheckedSemanticFormDecision
| RequirementCheckedCompetenceDecision
| RequirementHandoffAcceptedDecision.

Definition decideRequirementHandoffByFacts
  (handoffKeyMatches
   handoffCategoryMatches
   handoffTargetMatches
   checkedKeyMatches
   checkedCategoryMatches
   checkedSemanticFormMatches
   checkedCompetenceMatches : bool) : RequirementHandoffDecision :=
  if handoffKeyMatches then
    if handoffCategoryMatches then
      if handoffTargetMatches then
        if checkedKeyMatches then
          if checkedCategoryMatches then
            if checkedSemanticFormMatches then
              if checkedCompetenceMatches then
                RequirementHandoffAcceptedDecision
              else RequirementCheckedCompetenceDecision
            else RequirementCheckedSemanticFormDecision
          else RequirementCheckedCategoryDecision
        else RequirementCheckedKeyDecision
      else RequirementHandoffTargetDecision
    else RequirementHandoffCategoryDecision
  else RequirementHandoffKeyDecision.

Theorem requirement_handoff_decision_accept_iff_facts :
  forall handoffKeyMatches
         handoffCategoryMatches
         handoffTargetMatches
         checkedKeyMatches
         checkedCategoryMatches
         checkedSemanticFormMatches
         checkedCompetenceMatches,
    decideRequirementHandoffByFacts
      handoffKeyMatches
      handoffCategoryMatches
      handoffTargetMatches
      checkedKeyMatches
      checkedCategoryMatches
      checkedSemanticFormMatches
      checkedCompetenceMatches = RequirementHandoffAcceptedDecision <->
    handoffKeyMatches = true /\
    handoffCategoryMatches = true /\
    handoffTargetMatches = true /\
    checkedKeyMatches = true /\
    checkedCategoryMatches = true /\
    checkedSemanticFormMatches = true /\
    checkedCompetenceMatches = true.
Proof.
  intros handoffKeyMatches handoffCategoryMatches handoffTargetMatches
    checkedKeyMatches checkedCategoryMatches checkedSemanticFormMatches
    checkedCompetenceMatches.
  destruct handoffKeyMatches, handoffCategoryMatches, handoffTargetMatches,
    checkedKeyMatches, checkedCategoryMatches, checkedSemanticFormMatches,
    checkedCompetenceMatches; simpl; intuition discriminate.
Qed.

Theorem requirement_handoff_decision_accept_iff_certified :
  forall requirement handoff checked
         handoffKeyMatches
         handoffCategoryMatches
         handoffTargetMatches
         checkedKeyMatches
         checkedCategoryMatches
         checkedSemanticFormMatches
         checkedCompetenceMatches,
    (handoffKeyMatches = true <->
      handoffRequirementKey handoff = requirementKey requirement) ->
    (handoffCategoryMatches = true <->
      handoffRequirementCategory handoff = requirementCategory requirement) ->
    (handoffTargetMatches = true <->
      handoffTarget handoff =
        GenericHandoffToCompetence
          (competenceForRequirementCategory (requirementCategory requirement))) ->
    (checkedKeyMatches = true <->
      checkedRequirementKey checked = requirementKey requirement) ->
    (checkedCategoryMatches = true <->
      checkedRequirementCategory checked = requirementCategory requirement) ->
    (checkedSemanticFormMatches = true <->
      checkedRequirementSemanticForm checked = requirementSemanticForm requirement) ->
    (checkedCompetenceMatches = true <->
      checkedRequirementCompetence checked =
        competenceForRequirementCategory (requirementCategory requirement)) ->
    decideRequirementHandoffByFacts
      handoffKeyMatches
      handoffCategoryMatches
      handoffTargetMatches
      checkedKeyMatches
      checkedCategoryMatches
      checkedSemanticFormMatches
      checkedCompetenceMatches = RequirementHandoffAcceptedDecision <->
    RequirementHandoffAccepts requirement handoff checked.
Proof.
  intros requirement handoff checked
    handoffKeyMatches handoffCategoryMatches handoffTargetMatches
    checkedKeyMatches checkedCategoryMatches checkedSemanticFormMatches
    checkedCompetenceMatches
    Hkey Hcategory Htarget HcheckedKey HcheckedCategory
    HcheckedSemanticForm HcheckedCompetence.
  rewrite requirement_handoff_decision_accept_iff_facts.
  split.
  - intros [HkeyFact [HcategoryFact [HtargetFact [HcheckedKeyFact
      [HcheckedCategoryFact [HcheckedSemanticFormFact HcheckedCompetenceFact]]]]]].
    repeat split.
    + exact ((proj1 Hkey) HkeyFact).
    + exact ((proj1 Hcategory) HcategoryFact).
    + exact ((proj1 Htarget) HtargetFact).
    + exact ((proj1 HcheckedKey) HcheckedKeyFact).
    + exact ((proj1 HcheckedCategory) HcheckedCategoryFact).
    + exact ((proj1 HcheckedSemanticForm) HcheckedSemanticFormFact).
    + exact ((proj1 HcheckedCompetence) HcheckedCompetenceFact).
  - intros [HkeyEq [HcategoryEq [HtargetEq [HcheckedKeyEq
      [HcheckedCategoryEq [HcheckedSemanticFormEq HcheckedCompetenceEq]]]]]].
    repeat split.
    + exact ((proj2 Hkey) HkeyEq).
    + exact ((proj2 Hcategory) HcategoryEq).
    + exact ((proj2 Htarget) HtargetEq).
    + exact ((proj2 HcheckedKey) HcheckedKeyEq).
    + exact ((proj2 HcheckedCategory) HcheckedCategoryEq).
    + exact ((proj2 HcheckedSemanticForm) HcheckedSemanticFormEq).
    + exact ((proj2 HcheckedCompetence) HcheckedCompetenceEq).
Qed.

Inductive RequirementInterfaceDomainDecision : Type :=
| RequirementInterfaceHandoffDomainDecision
| RequirementInterfaceCheckedDomainDecision
| RequirementInterfaceDomainAcceptedDecision.

Definition decideRequirementInterfaceDomainByFacts
  (handoffDomainExact checkedDomainExact : bool) : RequirementInterfaceDomainDecision :=
  if handoffDomainExact then
    if checkedDomainExact then
      RequirementInterfaceDomainAcceptedDecision
    else RequirementInterfaceCheckedDomainDecision
  else RequirementInterfaceHandoffDomainDecision.

Theorem requirement_interface_domain_decision_accept_iff_facts :
  forall handoffDomainExact checkedDomainExact,
    decideRequirementInterfaceDomainByFacts handoffDomainExact checkedDomainExact =
      RequirementInterfaceDomainAcceptedDecision <->
    handoffDomainExact = true /\ checkedDomainExact = true.
Proof.
  intros handoffDomainExact checkedDomainExact.
  destruct handoffDomainExact, checkedDomainExact; simpl; intuition discriminate.
Qed.

Definition ExactHandoffDomain
  (requirements : GenericRequirementRegistry)
  (handoffs : GenericHandoffRegistry) : Prop :=
  forall key,
    (exists requirement, requirements key = Some requirement) <->
    (exists handoff, handoffs key = Some handoff).

Definition ExactCheckedDomain
  (requirements : GenericRequirementRegistry)
  (checked : CheckedGenericRequirementRegistry) : Prop :=
  forall key,
    (exists requirement, requirements key = Some requirement) <->
    (exists result, checked key = Some result).

Theorem requirement_interface_domain_decision_accept_iff_certified_domains :
  forall requirements handoffs checked handoffDomainExact checkedDomainExact,
    (handoffDomainExact = true <-> ExactHandoffDomain requirements handoffs) ->
    (checkedDomainExact = true <-> ExactCheckedDomain requirements checked) ->
    decideRequirementInterfaceDomainByFacts handoffDomainExact checkedDomainExact =
      RequirementInterfaceDomainAcceptedDecision <->
    ExactHandoffDomain requirements handoffs /\ ExactCheckedDomain requirements checked.
Proof.
  intros requirements handoffs checked handoffDomainExact checkedDomainExact
    HhandoffDomain HcheckedDomain.
  rewrite requirement_interface_domain_decision_accept_iff_facts.
  split.
  - intros [Hhandoff Hchecked].
    split.
    + exact ((proj1 HhandoffDomain) Hhandoff).
    + exact ((proj1 HcheckedDomain) Hchecked).
  - intros [Hhandoff Hchecked].
    split.
    + exact ((proj2 HhandoffDomain) Hhandoff).
    + exact ((proj2 HcheckedDomain) Hchecked).
Qed.

Theorem certified_interface_supplies_exact_domains :
  forall requirements handoffs checked,
    CheckedGenericRequirementInterfaceValid requirements handoffs checked ->
    ExactHandoffDomain requirements handoffs /\
    ExactCheckedDomain requirements checked.
Proof.
  intros requirements handoffs checked Hvalid.
  split.
  - exact (interfaceExactHandoffDomain requirements handoffs checked Hvalid).
  - exact (interfaceExactCheckedDomain requirements handoffs checked Hvalid).
Qed.
