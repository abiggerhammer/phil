From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat.
Import ListNotations.

From Phil.Core Require Import ConcurrencySemantics.

(*
  PHIL-CONC-ACTIVATE-001 — exact process activation, participant
  classification, and initial ownership/reachability partition.

  This proof composes the Certified PHIL-CONC-SEM-001 population semantics with
  the additional CONC-003/010/011 activation boundary.  It intentionally models
  concrete Haskell Map/Set/Text values extensionally.  ProcessKey persistence,
  parser/source correspondence, architecture binding extraction, provider
  qualification details, and concrete unrestricted-wrapper traversal remain
  correspondence boundaries exercised by the unchanged Haskell corpus.
*)

Definition ResourceOccurrenceKey := nat.
Definition StatefulOccurrenceKey := nat.
Definition ProtocolRoleOccurrence := nat.

Inductive ActivationBindingOrigin : Type :=
| ExplicitArchitectureBinding
| AmbientBinding.

Record ActivationBinding : Type := mkActivationBinding {
  activationBindingProcess : ProcessKey;
  activationBindingResource : ResourceOccurrenceKey;
  activationBindingOrigin : ActivationBindingOrigin;
  activationBindingRestricted : bool;
  activationBindingDirectStateful : option StatefulOccurrenceKey
}.

Definition ActivationBindings := list ActivationBinding.
Definition RestrictedInitialOwner := ResourceOccurrenceKey -> option ProcessKey.
Definition DirectStatefulOwner := StatefulOccurrenceKey -> option ProcessKey.

Record ActivationContextValid
  (population : ProcessPopulation)
  (activation : ActivationMap)
  (bindings : ActivationBindings)
  (restrictedOwner : RestrictedInitialOwner)
  (directStatefulOwner : DirectStatefulOwner) : Prop :=
  mkActivationContextValid {
    activationContextPopulationValid :
      StaticPopulationValid population activation;
    activationContextBindingsExplicit :
      forall binding,
        In binding bindings ->
        activationBindingOrigin binding = ExplicitArchitectureBinding;
    activationContextBindingsNameActivatedProcess :
      forall binding,
        In binding bindings ->
        exists target,
          activation (activationBindingProcess binding) = Some target;
    activationContextRestrictedBindingExact :
      forall binding,
        In binding bindings ->
        activationBindingRestricted binding = true ->
        restrictedOwner (activationBindingResource binding) =
          Some (activationBindingProcess binding);
    activationContextNoInventedRestrictedOwner :
      forall resource process,
        restrictedOwner resource = Some process ->
        exists binding,
          In binding bindings /\
          activationBindingRestricted binding = true /\
          activationBindingResource binding = resource /\
          activationBindingProcess binding = process;
    activationContextDirectStatefulBindingExact :
      forall binding stateful,
        In binding bindings ->
        activationBindingDirectStateful binding = Some stateful ->
        directStatefulOwner stateful = Some (activationBindingProcess binding);
    activationContextNoInventedDirectStatefulOwner :
      forall stateful process,
        directStatefulOwner stateful = Some process ->
        exists binding,
          In binding bindings /\
          activationBindingDirectStateful binding = Some stateful /\
          activationBindingProcess binding = process
  }.

Theorem activation_context_rejects_ambient_binding :
  forall population activation bindings restrictedOwner directStatefulOwner binding,
    ActivationContextValid
      population activation bindings restrictedOwner directStatefulOwner ->
    In binding bindings ->
    activationBindingOrigin binding = AmbientBinding ->
    False.
Proof.
  intros population activation bindings restrictedOwner directStatefulOwner
    binding Hvalid Hin Hambient.
  destruct Hvalid as [_ Hexplicit _ _ _ _ _].
  pose proof (Hexplicit binding Hin) as Horigin.
  rewrite Hambient in Horigin.
  discriminate.
Qed.

Theorem activation_binding_names_existing_activation :
  forall population activation bindings restrictedOwner directStatefulOwner binding,
    ActivationContextValid
      population activation bindings restrictedOwner directStatefulOwner ->
    In binding bindings ->
    exists target,
      activation (activationBindingProcess binding) = Some target.
Proof.
  intros population activation bindings restrictedOwner directStatefulOwner
    binding Hvalid Hin.
  destruct Hvalid as [_ _ Hactivated _ _ _ _].
  eapply Hactivated.
  exact Hin.
Qed.

Theorem restricted_initial_owner_is_functional :
  forall (owners : RestrictedInitialOwner) resource first second,
    owners resource = Some first ->
    owners resource = Some second ->
    first = second.
Proof.
  intros owners resource first second Hfirst Hsecond.
  rewrite Hfirst in Hsecond.
  inversion Hsecond.
  reflexivity.
Qed.

Theorem restricted_binding_has_exact_initial_owner :
  forall population activation bindings restrictedOwner directStatefulOwner binding,
    ActivationContextValid
      population activation bindings restrictedOwner directStatefulOwner ->
    In binding bindings ->
    activationBindingRestricted binding = true ->
    restrictedOwner (activationBindingResource binding) =
      Some (activationBindingProcess binding).
Proof.
  intros population activation bindings restrictedOwner directStatefulOwner
    binding Hvalid Hin Hrestricted.
  destruct Hvalid as [_ _ _ Hexact _ _ _].
  eapply Hexact; eauto.
Qed.

Theorem restricted_owner_cannot_be_manufactured :
  forall population activation bindings restrictedOwner directStatefulOwner
         resource process,
    ActivationContextValid
      population activation bindings restrictedOwner directStatefulOwner ->
    restrictedOwner resource = Some process ->
    exists binding,
      In binding bindings /\
      activationBindingRestricted binding = true /\
      activationBindingResource binding = resource /\
      activationBindingProcess binding = process.
Proof.
  intros population activation bindings restrictedOwner directStatefulOwner
    resource process Hvalid Hlookup.
  destruct Hvalid as [_ _ _ _ Hnoinvent _ _].
  eapply Hnoinvent.
  exact Hlookup.
Qed.

Theorem direct_stateful_owner_is_functional :
  forall (owners : DirectStatefulOwner) stateful first second,
    owners stateful = Some first ->
    owners stateful = Some second ->
    first = second.
Proof.
  intros owners stateful first second Hfirst Hsecond.
  rewrite Hfirst in Hsecond.
  inversion Hsecond.
  reflexivity.
Qed.

Theorem unrestricted_wrapper_cannot_authorize_second_direct_stateful_owner :
  forall (owners : DirectStatefulOwner) stateful owner other,
    owners stateful = Some owner ->
    other <> owner ->
    owners stateful <> Some other.
Proof.
  intros owners stateful owner other Howner Hneq Hother.
  apply Hneq.
  eapply direct_stateful_owner_is_functional.
  - exact Hother.
  - exact Howner.
Qed.

Inductive ParticipantClassification : Type :=
| InternalParticipant : ProcessKey -> ParticipantClassification
| ExternalParticipant : ParticipantClassification.

Definition ExpectedProtocolRoles := ProtocolRoleOccurrence -> bool.
Definition ParticipantMap := ProtocolRoleOccurrence -> option ParticipantClassification.

Record ParticipantClassificationValid
  (population : ProcessPopulation)
  (activation : ActivationMap)
  (expected : ExpectedProtocolRoles)
  (participants : ParticipantMap) : Prop :=
  mkParticipantClassificationValid {
    participantClassificationExact :
      forall role,
        expected role = true <->
        exists participant, participants role = Some participant;
    participantClassificationInternalActivated :
      forall role process,
        participants role = Some (InternalParticipant process) ->
        exists target, activation process = Some target;
    participantClassificationInternalPopulation :
      forall role process,
        participants role = Some (InternalParticipant process) ->
        exists occurrence,
          In occurrence population /\
          staticProcessKey occurrence = process;
    participantClassificationNoEmptyRole : expected 0 = false
  }.

Theorem every_expected_role_is_explicitly_classified :
  forall population activation expected participants role,
    ParticipantClassificationValid population activation expected participants ->
    expected role = true ->
    exists participant, participants role = Some participant.
Proof.
  intros population activation expected participants role Hvalid Hexpected.
  destruct Hvalid as [Hexact _ _ _].
  apply (proj1 (Hexact role)).
  exact Hexpected.
Qed.

Theorem missing_participant_classification_cannot_validate :
  forall population activation expected participants role,
    ParticipantClassificationValid population activation expected participants ->
    expected role = true ->
    participants role = None ->
    False.
Proof.
  intros population activation expected participants role Hvalid Hexpected Hnone.
  pose proof
    (every_expected_role_is_explicitly_classified
      population activation expected participants role Hvalid Hexpected)
    as [participant Hsome].
  rewrite Hnone in Hsome.
  discriminate.
Qed.

Theorem internal_participant_names_activated_process :
  forall population activation expected participants role process,
    ParticipantClassificationValid population activation expected participants ->
    participants role = Some (InternalParticipant process) ->
    exists target, activation process = Some target.
Proof.
  intros population activation expected participants role process Hvalid Hlookup.
  destruct Hvalid as [_ Hactivated _ _].
  eapply Hactivated.
  exact Hlookup.
Qed.

Theorem internal_participant_names_static_process :
  forall population activation expected participants role process,
    ParticipantClassificationValid population activation expected participants ->
    participants role = Some (InternalParticipant process) ->
    exists occurrence,
      In occurrence population /\
      staticProcessKey occurrence = process.
Proof.
  intros population activation expected participants role process Hvalid Hlookup.
  destruct Hvalid as [_ _ Hpopulation _].
  eapply Hpopulation.
  exact Hlookup.
Qed.

(* Externality is exactly a participant classification.  It carries no
   ProcessKey and therefore cannot by itself manufacture an internal process
   activation or terminal fact. *)
Theorem external_participant_has_no_internal_process_key :
  forall process,
    ExternalParticipant <> InternalParticipant process.
Proof.
  intros process Hsame.
  discriminate.
Qed.

Record CertifiedConcurrencyActivation
  (population : ProcessPopulation)
  (activation : ActivationMap)
  (bindings : ActivationBindings)
  (restrictedOwner : RestrictedInitialOwner)
  (directStatefulOwner : DirectStatefulOwner)
  (expected : ExpectedProtocolRoles)
  (participants : ParticipantMap) : Prop :=
  mkCertifiedConcurrencyActivation {
    certifiedActivationContext :
      ActivationContextValid
        population activation bindings restrictedOwner directStatefulOwner;
    certifiedParticipantClassification :
      ParticipantClassificationValid population activation expected participants
  }.

Theorem certified_activation_inherits_exact_static_population :
  forall population activation bindings restrictedOwner directStatefulOwner
         expected participants,
    CertifiedConcurrencyActivation
      population activation bindings restrictedOwner directStatefulOwner
      expected participants ->
    StaticPopulationValid population activation.
Proof.
  intros population activation bindings restrictedOwner directStatefulOwner
    expected participants Hcertified.
  destruct Hcertified as [Hactivation _].
  destruct Hactivation as [Hpopulation _ _ _ _ _ _].
  exact Hpopulation.
Qed.

Theorem certified_activation_combines_explicit_binding_and_participant_closure :
  forall population activation bindings restrictedOwner directStatefulOwner
         expected participants binding role,
    CertifiedConcurrencyActivation
      population activation bindings restrictedOwner directStatefulOwner
      expected participants ->
    In binding bindings ->
    expected role = true ->
    activationBindingOrigin binding = ExplicitArchitectureBinding /\
    exists participant, participants role = Some participant.
Proof.
  intros population activation bindings restrictedOwner directStatefulOwner
    expected participants binding role Hcertified Hin Hexpected.
  destruct Hcertified as [Hactivation Hparticipants].
  split.
  - destruct Hactivation as [_ Hexplicit _ _ _ _ _].
    eapply Hexplicit.
    exact Hin.
  - eapply every_expected_role_is_explicitly_classified.
    + exact Hparticipants.
    + exact Hexpected.
Qed.
