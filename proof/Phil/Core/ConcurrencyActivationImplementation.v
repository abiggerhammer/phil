From Stdlib Require Import Lists.List Bool.Bool.
Import ListNotations.

From Phil.Core Require Import ConcurrencySemantics ConcurrencyActivation.

(*
  Machine-facing decision surface for PHIL-CONC-ACTIVATE-001.

  The decisions remain representation-neutral.  Concrete Haskell Map/Set/Text
  traversal, ProcessKey serialization, source/architecture extraction, and
  unrestricted-wrapper reachability are correspondence facts reflected into
  these booleans by the implementation boundary.
*)

Definition decideActivationBindingExplicitByFacts
  (bindingExplicit : bool) : bool :=
  bindingExplicit.

Definition decideRestrictedInitialOwnershipByFacts
  (restrictedBindingsExact noInventedRestrictedOwner : bool) : bool :=
  andb restrictedBindingsExact noInventedRestrictedOwner.

Definition decideDirectStatefulOwnershipByFacts
  (directStatefulBindingsExact noInventedDirectStatefulOwner : bool) : bool :=
  andb directStatefulBindingsExact noInventedDirectStatefulOwner.

Definition decideActivationContextByFacts
  (populationValid bindingsExplicit bindingProcessesActivated
   restrictedBindingsExact noInventedRestrictedOwner
   directStatefulBindingsExact noInventedDirectStatefulOwner : bool) : bool :=
  andb populationValid
    (andb bindingsExplicit
      (andb bindingProcessesActivated
        (andb restrictedBindingsExact
          (andb noInventedRestrictedOwner
            (andb directStatefulBindingsExact
              noInventedDirectStatefulOwner))))).

Definition decideParticipantClassificationByFacts
  (classificationExact internalParticipantsActivated
   internalParticipantsStatic noEmptyRole : bool) : bool :=
  andb classificationExact
    (andb internalParticipantsActivated
      (andb internalParticipantsStatic noEmptyRole)).

Definition decideCertifiedConcurrencyActivationByFacts
  (activationContextValid participantClassificationValid : bool) : bool :=
  andb activationContextValid participantClassificationValid.

Theorem decideActivationBindingExplicitByFacts_classifies :
  forall binding bindingExplicit,
    (bindingExplicit = true <->
      activationBindingOrigin binding = ExplicitArchitectureBinding) ->
    decideActivationBindingExplicitByFacts bindingExplicit = true <->
    activationBindingOrigin binding = ExplicitArchitectureBinding.
Proof.
  intros binding bindingExplicit Hexplicit.
  unfold decideActivationBindingExplicitByFacts.
  exact Hexplicit.
Qed.

Theorem decideRestrictedInitialOwnershipByFacts_classifies :
  forall bindings restrictedOwner restrictedBindingsExact
         noInventedRestrictedOwner,
    (restrictedBindingsExact = true <->
      forall binding,
        In binding bindings ->
        activationBindingRestricted binding = true ->
        restrictedOwner (activationBindingResource binding) =
          Some (activationBindingProcess binding)) ->
    (noInventedRestrictedOwner = true <->
      forall resource process,
        restrictedOwner resource = Some process ->
        exists binding,
          In binding bindings /\
          activationBindingRestricted binding = true /\
          activationBindingResource binding = resource /\
          activationBindingProcess binding = process) ->
    decideRestrictedInitialOwnershipByFacts
      restrictedBindingsExact noInventedRestrictedOwner = true <->
    (forall binding,
      In binding bindings ->
      activationBindingRestricted binding = true ->
      restrictedOwner (activationBindingResource binding) =
        Some (activationBindingProcess binding)) /\
    (forall resource process,
      restrictedOwner resource = Some process ->
      exists binding,
        In binding bindings /\
        activationBindingRestricted binding = true /\
        activationBindingResource binding = resource /\
        activationBindingProcess binding = process).
Proof.
  intros bindings restrictedOwner restrictedBindingsExact
    noInventedRestrictedOwner Hexact Hnoinvent.
  unfold decideRestrictedInitialOwnershipByFacts.
  rewrite andb_true_iff.
  rewrite Hexact, Hnoinvent.
  reflexivity.
Qed.

Theorem decideDirectStatefulOwnershipByFacts_classifies :
  forall bindings directStatefulOwner directStatefulBindingsExact
         noInventedDirectStatefulOwner,
    (directStatefulBindingsExact = true <->
      forall binding stateful,
        In binding bindings ->
        activationBindingDirectStateful binding = Some stateful ->
        directStatefulOwner stateful = Some (activationBindingProcess binding)) ->
    (noInventedDirectStatefulOwner = true <->
      forall stateful process,
        directStatefulOwner stateful = Some process ->
        exists binding,
          In binding bindings /\
          activationBindingDirectStateful binding = Some stateful /\
          activationBindingProcess binding = process) ->
    decideDirectStatefulOwnershipByFacts
      directStatefulBindingsExact noInventedDirectStatefulOwner = true <->
    (forall binding stateful,
      In binding bindings ->
      activationBindingDirectStateful binding = Some stateful ->
      directStatefulOwner stateful = Some (activationBindingProcess binding)) /\
    (forall stateful process,
      directStatefulOwner stateful = Some process ->
      exists binding,
        In binding bindings /\
        activationBindingDirectStateful binding = Some stateful /\
        activationBindingProcess binding = process).
Proof.
  intros bindings directStatefulOwner directStatefulBindingsExact
    noInventedDirectStatefulOwner Hexact Hnoinvent.
  unfold decideDirectStatefulOwnershipByFacts.
  rewrite andb_true_iff.
  rewrite Hexact, Hnoinvent.
  reflexivity.
Qed.

Theorem decideActivationContextByFacts_classifies :
  forall population activation bindings restrictedOwner directStatefulOwner
         populationValid bindingsExplicit bindingProcessesActivated
         restrictedBindingsExact noInventedRestrictedOwner
         directStatefulBindingsExact noInventedDirectStatefulOwner,
    (populationValid = true <-> StaticPopulationValid population activation) ->
    (bindingsExplicit = true <->
      forall binding,
        In binding bindings ->
        activationBindingOrigin binding = ExplicitArchitectureBinding) ->
    (bindingProcessesActivated = true <->
      forall binding,
        In binding bindings ->
        exists target,
          activation (activationBindingProcess binding) = Some target) ->
    (restrictedBindingsExact = true <->
      forall binding,
        In binding bindings ->
        activationBindingRestricted binding = true ->
        restrictedOwner (activationBindingResource binding) =
          Some (activationBindingProcess binding)) ->
    (noInventedRestrictedOwner = true <->
      forall resource process,
        restrictedOwner resource = Some process ->
        exists binding,
          In binding bindings /\
          activationBindingRestricted binding = true /\
          activationBindingResource binding = resource /\
          activationBindingProcess binding = process) ->
    (directStatefulBindingsExact = true <->
      forall binding stateful,
        In binding bindings ->
        activationBindingDirectStateful binding = Some stateful ->
        directStatefulOwner stateful = Some (activationBindingProcess binding)) ->
    (noInventedDirectStatefulOwner = true <->
      forall stateful process,
        directStatefulOwner stateful = Some process ->
        exists binding,
          In binding bindings /\
          activationBindingDirectStateful binding = Some stateful /\
          activationBindingProcess binding = process) ->
    decideActivationContextByFacts
      populationValid bindingsExplicit bindingProcessesActivated
      restrictedBindingsExact noInventedRestrictedOwner
      directStatefulBindingsExact noInventedDirectStatefulOwner = true <->
    ActivationContextValid
      population activation bindings restrictedOwner directStatefulOwner.
Proof.
  intros population activation bindings restrictedOwner directStatefulOwner
    populationValid bindingsExplicit bindingProcessesActivated
    restrictedBindingsExact noInventedRestrictedOwner
    directStatefulBindingsExact noInventedDirectStatefulOwner
    Hpopulation Hexplicit Hactivated Hrestricted HnoRestricted
    Hdirect HnoDirect.
  unfold decideActivationContextByFacts.
  repeat rewrite andb_true_iff.
  split.
  - intros [HpopulationBool
      [HexplicitBool
        [HactivatedBool
          [HrestrictedBool
            [HnoRestrictedBool [HdirectBool HnoDirectBool]]]]]].
    constructor.
    + apply (proj1 Hpopulation). exact HpopulationBool.
    + apply (proj1 Hexplicit). exact HexplicitBool.
    + apply (proj1 Hactivated). exact HactivatedBool.
    + apply (proj1 Hrestricted). exact HrestrictedBool.
    + apply (proj1 HnoRestricted). exact HnoRestrictedBool.
    + apply (proj1 Hdirect). exact HdirectBool.
    + apply (proj1 HnoDirect). exact HnoDirectBool.
  - intros Hvalid.
    destruct Hvalid as
      [HpopulationProp HexplicitProp HactivatedProp HrestrictedProp
       HnoRestrictedProp HdirectProp HnoDirectProp].
    split.
    + apply (proj2 Hpopulation). exact HpopulationProp.
    + split.
      * apply (proj2 Hexplicit). exact HexplicitProp.
      * split.
        -- apply (proj2 Hactivated). exact HactivatedProp.
        -- split.
           ++ apply (proj2 Hrestricted). exact HrestrictedProp.
           ++ split.
              ** apply (proj2 HnoRestricted). exact HnoRestrictedProp.
              ** split.
                 --- apply (proj2 Hdirect). exact HdirectProp.
                 --- apply (proj2 HnoDirect). exact HnoDirectProp.
Qed.

Theorem decideParticipantClassificationByFacts_classifies :
  forall population activation expected participants classificationExact
         internalParticipantsActivated internalParticipantsStatic noEmptyRole,
    (classificationExact = true <->
      forall role,
        expected role = true <->
        exists participant, participants role = Some participant) ->
    (internalParticipantsActivated = true <->
      forall role process,
        participants role = Some (InternalParticipant process) ->
        exists target, activation process = Some target) ->
    (internalParticipantsStatic = true <->
      forall role process,
        participants role = Some (InternalParticipant process) ->
        exists occurrence,
          In occurrence population /\
          staticProcessKey occurrence = process) ->
    (noEmptyRole = true <-> expected 0 = false) ->
    decideParticipantClassificationByFacts
      classificationExact internalParticipantsActivated
      internalParticipantsStatic noEmptyRole = true <->
    ParticipantClassificationValid population activation expected participants.
Proof.
  intros population activation expected participants classificationExact
    internalParticipantsActivated internalParticipantsStatic noEmptyRole
    Hexact Hactivated Hstatic Hempty.
  unfold decideParticipantClassificationByFacts.
  repeat rewrite andb_true_iff.
  split.
  - intros [HexactBool [HactivatedBool [HstaticBool HemptyBool]]].
    constructor.
    + apply (proj1 Hexact). exact HexactBool.
    + apply (proj1 Hactivated). exact HactivatedBool.
    + apply (proj1 Hstatic). exact HstaticBool.
    + apply (proj1 Hempty). exact HemptyBool.
  - intros Hvalid.
    destruct Hvalid as [HexactProp HactivatedProp HstaticProp HemptyProp].
    split.
    + apply (proj2 Hexact). exact HexactProp.
    + split.
      * apply (proj2 Hactivated). exact HactivatedProp.
      * split.
        -- apply (proj2 Hstatic). exact HstaticProp.
        -- apply (proj2 Hempty). exact HemptyProp.
Qed.

Theorem decideCertifiedConcurrencyActivationByFacts_classifies :
  forall population activation bindings restrictedOwner directStatefulOwner
         expected participants activationContextValid
         participantClassificationValid,
    (activationContextValid = true <->
      ActivationContextValid
        population activation bindings restrictedOwner directStatefulOwner) ->
    (participantClassificationValid = true <->
      ParticipantClassificationValid population activation expected participants) ->
    decideCertifiedConcurrencyActivationByFacts
      activationContextValid participantClassificationValid = true <->
    CertifiedConcurrencyActivation
      population activation bindings restrictedOwner directStatefulOwner
      expected participants.
Proof.
  intros population activation bindings restrictedOwner directStatefulOwner
    expected participants activationContextValid participantClassificationValid
    Hactivation Hparticipants.
  unfold decideCertifiedConcurrencyActivationByFacts.
  rewrite andb_true_iff.
  split.
  - intros [HactivationBool HparticipantsBool].
    constructor.
    + apply (proj1 Hactivation). exact HactivationBool.
    + apply (proj1 Hparticipants). exact HparticipantsBool.
  - intros Hcertified.
    destruct Hcertified as [HactivationProp HparticipantsProp].
    split.
    + apply (proj2 Hactivation). exact HactivationProp.
    + apply (proj2 Hparticipants). exact HparticipantsProp.
Qed.
