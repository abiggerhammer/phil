From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import ResourceLoop.

Inductive LoopProjectionDecision : Type :=
| LoopProjectionAcceptedDecision
| LoopProjectionKindDecision
| LoopProjectionResourceDecision
| LoopProjectionSlotDomainDecision
| LoopProjectionRequirementDecision.

Definition decideLoopProjectionByFacts
  (kindMatches resourceProjectionAccepted slotDomainExact requirementsExact : bool)
  : LoopProjectionDecision :=
  if kindMatches then
    if resourceProjectionAccepted then
      if slotDomainExact then
        if requirementsExact then
          LoopProjectionAcceptedDecision
        else
          LoopProjectionRequirementDecision
      else
        LoopProjectionSlotDomainDecision
    else
      LoopProjectionResourceDecision
  else
    LoopProjectionKindDecision.

Definition ExpectedLoopProjectionAccepted
  (expected : LoopProjectionKind)
  (succession : SuccessionEvidence)
  (telescope : LoopStateTelescope)
  (projection : LoopStateProjection) : Prop :=
  loopProjectionKind projection = expected /\
  LoopProjectionAccepted succession telescope projection.

Theorem loop_projection_decision_corresponds_acceptance :
  forall expected succession telescope projection
    kindMatches resourceProjectionAccepted slotDomainExact requirementsExact,
    (kindMatches = true <-> loopProjectionKind projection = expected) ->
    (resourceProjectionAccepted = true <->
      ResourceProjectionSuccess succession (loopProjectionResource projection)) ->
    (slotDomainExact = true <->
      forall slot,
        loopStateSlots telescope slot = true <->
          exists owner,
            projectionBindings (loopProjectionResource projection) slot = Some owner) ->
    (requirementsExact = true <->
      forall slot,
        loopStateSlots telescope slot = true ->
        projectionRequirements (loopProjectionResource projection) slot =
          loopStateRequirements telescope slot) ->
    (decideLoopProjectionByFacts
       kindMatches resourceProjectionAccepted slotDomainExact requirementsExact =
       LoopProjectionAcceptedDecision <->
     ExpectedLoopProjectionAccepted expected succession telescope projection).
Proof.
  intros expected succession telescope projection
    kindMatches resourceProjectionAccepted slotDomainExact requirementsExact
    Hkind Hresource Hslots Hrequirements.
  unfold decideLoopProjectionByFacts, ExpectedLoopProjectionAccepted,
    LoopProjectionAccepted, ProjectionUsesLoopTelescope.
  destruct kindMatches;
    destruct resourceProjectionAccepted;
    destruct slotDomainExact;
    destruct requirementsExact; simpl in *.
  all: split.
  all: try discriminate.
  all: try (intros [HkindProp [HresourceProp [HslotsProp HrequirementsProp]]];
            first [
              apply (proj2 Hkind) in HkindProp; discriminate
            | apply (proj2 Hresource) in HresourceProp; discriminate
            | apply (proj2 Hslots) in HslotsProp; discriminate
            | apply (proj2 Hrequirements) in HrequirementsProp; discriminate
            ]).
  - intros _. repeat split.
    + apply (proj1 Hkind). reflexivity.
    + apply (proj1 Hresource). reflexivity.
    + apply (proj1 Hslots). reflexivity.
    + apply (proj1 Hrequirements). reflexivity.
  - intros _. reflexivity.
Qed.

Inductive StateTransportDecision : Type :=
| StateTransportAcceptedDecision
| StateTransportExplicitEvidenceDecision.

Definition decideStateTransportByFacts
  (definitionallyEqual explicitEvidenceAccepted : bool)
  : StateTransportDecision :=
  if definitionallyEqual then
    StateTransportAcceptedDecision
  else if explicitEvidenceAccepted then
    StateTransportAcceptedDecision
  else
    StateTransportExplicitEvidenceDecision.

Theorem state_transport_decision_corresponds_checked_transport :
  forall source target definitionallyEqual explicitEvidenceAccepted,
    (definitionallyEqual = true <-> source = target) ->
    (explicitEvidenceAccepted = true <-> AcceptedEqualityEvidence source target) ->
    (decideStateTransportByFacts definitionallyEqual explicitEvidenceAccepted =
       StateTransportAcceptedDecision <->
     CheckedStateTransport source target).
Proof.
  intros source target definitionallyEqual explicitEvidenceAccepted
    Hdefeq Hevidence.
  unfold decideStateTransportByFacts, CheckedStateTransport.
  destruct definitionallyEqual;
    destruct explicitEvidenceAccepted; simpl in *.
  - split.
    + intros _. left. apply (proj1 Hdefeq). reflexivity.
    + intros _. reflexivity.
  - split.
    + intros _. left. apply (proj1 Hdefeq). reflexivity.
    + intros _. reflexivity.
  - split.
    + intros _. right. apply (proj1 Hevidence). reflexivity.
    + intros _. reflexivity.
  - split.
    + discriminate.
    + intros [Hequal | Haccepted].
      * apply (proj2 Hdefeq) in Hequal. discriminate.
      * apply (proj2 Hevidence) in Haccepted. discriminate.
Qed.
