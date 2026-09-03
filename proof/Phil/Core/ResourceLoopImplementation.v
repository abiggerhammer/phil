From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import ResourceJoin ResourceLoop.

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

Theorem loop_projection_decision_exact :
  forall kindMatches resourceProjectionAccepted slotDomainExact requirementsExact,
    (decideLoopProjectionByFacts
       kindMatches resourceProjectionAccepted slotDomainExact requirementsExact =
       LoopProjectionAcceptedDecision <->
     kindMatches = true /\
     resourceProjectionAccepted = true /\
     slotDomainExact = true /\
     requirementsExact = true).
Proof.
  intros kindMatches resourceProjectionAccepted slotDomainExact requirementsExact.
  split.
  - intro Hdecision.
    unfold decideLoopProjectionByFacts in Hdecision.
    destruct kindMatches eqn:Hkind; try discriminate.
    destruct resourceProjectionAccepted eqn:Hresource; try discriminate.
    destruct slotDomainExact eqn:Hslots; try discriminate.
    destruct requirementsExact eqn:Hrequirements; try discriminate.
    repeat split; assumption.
  - intros [Hkind [Hresource [Hslots Hrequirements]]].
    rewrite Hkind, Hresource, Hslots, Hrequirements.
    reflexivity.
Qed.

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
  split.
  - intro Hdecision.
    apply (proj1 (loop_projection_decision_exact
      kindMatches resourceProjectionAccepted slotDomainExact requirementsExact))
      in Hdecision.
    destruct Hdecision as [HkindBool [HresourceBool [HslotsBool HrequirementsBool]]].
    unfold ExpectedLoopProjectionAccepted.
    split.
    + exact ((proj1 Hkind) HkindBool).
    + unfold LoopProjectionAccepted.
      split.
      * exact ((proj1 Hresource) HresourceBool).
      * unfold ProjectionUsesLoopTelescope.
        split.
        -- exact ((proj1 Hslots) HslotsBool).
        -- exact ((proj1 Hrequirements) HrequirementsBool).
  - intro Haccepted.
    unfold ExpectedLoopProjectionAccepted in Haccepted.
    destruct Haccepted as [HkindProp Hloop].
    unfold LoopProjectionAccepted in Hloop.
    destruct Hloop as [HresourceProp Htelescope].
    unfold ProjectionUsesLoopTelescope in Htelescope.
    destruct Htelescope as [HslotsProp HrequirementsProp].
    apply (proj2 (loop_projection_decision_exact
      kindMatches resourceProjectionAccepted slotDomainExact requirementsExact)).
    split.
    + exact ((proj2 Hkind) HkindProp).
    + split.
      * exact ((proj2 Hresource) HresourceProp).
      * split.
        -- exact ((proj2 Hslots) HslotsProp).
        -- exact ((proj2 Hrequirements) HrequirementsProp).
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
    + intros _. left. exact ((proj1 Hdefeq) eq_refl).
    + intros _. reflexivity.
  - split.
    + intros _. left. exact ((proj1 Hdefeq) eq_refl).
    + intros _. reflexivity.
  - split.
    + intros _. right. exact ((proj1 Hevidence) eq_refl).
    + intros _. reflexivity.
  - split.
    + discriminate.
    + intros [Hequal | Haccepted].
      * pose proof ((proj2 Hdefeq) Hequal) as Hfalse.
        discriminate.
      * pose proof ((proj2 Hevidence) Haccepted) as Hfalse.
        discriminate.
Qed.
