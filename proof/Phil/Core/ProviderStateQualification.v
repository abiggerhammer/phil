From Stdlib Require Import Lists.List.
Import ListNotations.

From Phil.Core Require Import ProviderQualification.

(*
  PHIL-PROV-STATE-001 — provider state simulation, provider-wide laws,
  and lifecycle/interruption qualification (PROV-006 through PROV-008).

  This normalized model consumes the already-qualified PROV-001--005 operation
  and outcome correspondence as an exact semantic map. Concrete Haskell Map/Set
  representation and corpus/model completeness remain correspondence/evidence
  boundaries rather than being smuggled into the proposition.
*)

Definition ProviderAbstractStateKey := nat.
Definition ProviderImplementationStateKey := nat.
Definition ProviderStateRelationRevision := nat.
Definition ProviderLawRevision := nat.
Definition ProviderLawStateKey := nat.
Definition ProviderObservationBoundaryKey := nat.
Definition ProviderInterruptionPointKey := nat.
Definition ProviderObservableStateKey := nat.
Definition ProviderLifecycleRevision := nat.

Definition ProviderQualifiedOutcomeMap :=
  ProviderOperationKey -> option (ProviderOutcomeKey -> option ProviderOutcomeKey).

(* PROV-006: asymmetric state simulation. *)

Record ProviderImplementationStateTransition : Type :=
  mkProviderImplementationStateTransition {
    stateImplementationTransitionOperation : ProviderOperationKey;
    stateImplementationTransitionFrom : ProviderImplementationStateKey;
    stateImplementationTransitionOutcome : ProviderOutcomeKey;
    stateImplementationTransitionTo : ProviderImplementationStateKey
  }.

Record ProviderContractStateTransition : Type :=
  mkProviderContractStateTransition {
    stateContractTransitionOperation : ProviderOperationKey;
    stateContractTransitionFrom : ProviderAbstractStateKey;
    stateContractTransitionOutcome : ProviderOutcomeKey;
    stateContractTransitionTo : ProviderAbstractStateKey
  }.

Record ProviderStateRefinementModel : Type := mkProviderStateRefinementModel {
  stateRelationRevision : ProviderStateRelationRevision;
  stateRelated : ProviderImplementationStateKey -> ProviderAbstractStateKey -> Prop;
  stateVisibleInitial : ProviderImplementationStateKey -> Prop;
  stateAdmissibleInitial : ProviderAbstractStateKey -> Prop;
  stateInitialCorrespondence : ProviderImplementationStateKey -> option ProviderAbstractStateKey;
  stateImplementationTransitions : ProviderImplementationStateTransition -> Prop;
  stateContractTransitions : ProviderContractStateTransition -> Prop
}.

Definition ProviderStateQualifies
  (qualifiedOutcomes : ProviderQualifiedOutcomeMap)
  (model : ProviderStateRefinementModel) : Prop :=
  (forall implementationState,
    stateVisibleInitial model implementationState <->
    exists abstractState,
      stateInitialCorrespondence model implementationState = Some abstractState) /\
  (forall implementationState abstractState,
    stateInitialCorrespondence model implementationState = Some abstractState ->
    stateAdmissibleInitial model abstractState /\
    stateRelated model implementationState abstractState) /\
  (forall transition,
    stateImplementationTransitions model transition ->
    exists outcomeMap contractOutcome,
      qualifiedOutcomes (stateImplementationTransitionOperation transition) = Some outcomeMap /\
      outcomeMap (stateImplementationTransitionOutcome transition) = Some contractOutcome /\
      (exists abstractPre,
        stateRelated model (stateImplementationTransitionFrom transition) abstractPre) /\
      (forall abstractPre,
        stateRelated model (stateImplementationTransitionFrom transition) abstractPre ->
        exists contractTransition,
          stateContractTransitions model contractTransition /\
          stateContractTransitionOperation contractTransition =
            stateImplementationTransitionOperation transition /\
          stateContractTransitionFrom contractTransition = abstractPre /\
          stateContractTransitionOutcome contractTransition = contractOutcome /\
          stateRelated model
            (stateImplementationTransitionTo transition)
            (stateContractTransitionTo contractTransition))).

Theorem provider_state_initial_domain_is_exact :
  forall qualifiedOutcomes model implementationState,
    ProviderStateQualifies qualifiedOutcomes model ->
    (stateVisibleInitial model implementationState <->
     exists abstractState,
       stateInitialCorrespondence model implementationState = Some abstractState).
Proof.
  intros qualifiedOutcomes model implementationState Hqualified.
  exact (proj1 Hqualified implementationState).
Qed.

Theorem missing_provider_initial_correspondence_rejects :
  forall qualifiedOutcomes model implementationState,
    stateVisibleInitial model implementationState ->
    stateInitialCorrespondence model implementationState = None ->
    ~ ProviderStateQualifies qualifiedOutcomes model.
Proof.
  intros qualifiedOutcomes model implementationState Hvisible Hmissing Hqualified.
  destruct (proj1 (proj1 Hqualified implementationState) Hvisible)
    as [abstractState Hmapped].
  rewrite Hmissing in Hmapped.
  discriminate.
Qed.

Theorem unexpected_provider_initial_correspondence_rejects :
  forall qualifiedOutcomes model implementationState abstractState,
    ~ stateVisibleInitial model implementationState ->
    stateInitialCorrespondence model implementationState = Some abstractState ->
    ~ ProviderStateQualifies qualifiedOutcomes model.
Proof.
  intros qualifiedOutcomes model implementationState abstractState HnotVisible Hmapped Hqualified.
  apply HnotVisible.
  apply (proj2 (proj1 Hqualified implementationState)).
  exists abstractState.
  exact Hmapped.
Qed.

Theorem provider_initial_pair_is_admissible_and_related :
  forall qualifiedOutcomes model implementationState abstractState,
    ProviderStateQualifies qualifiedOutcomes model ->
    stateInitialCorrespondence model implementationState = Some abstractState ->
    stateAdmissibleInitial model abstractState /\
    stateRelated model implementationState abstractState.
Proof.
  intros qualifiedOutcomes model implementationState abstractState Hqualified Hmapped.
  exact (proj1 (proj2 Hqualified) implementationState abstractState Hmapped).
Qed.

Theorem provider_state_transition_has_qualified_outcome :
  forall qualifiedOutcomes model transition,
    ProviderStateQualifies qualifiedOutcomes model ->
    stateImplementationTransitions model transition ->
    exists outcomeMap contractOutcome,
      qualifiedOutcomes (stateImplementationTransitionOperation transition) = Some outcomeMap /\
      outcomeMap (stateImplementationTransitionOutcome transition) = Some contractOutcome.
Proof.
  intros qualifiedOutcomes model transition Hqualified Htransition.
  destruct (proj2 (proj2 Hqualified) transition Htransition)
    as [outcomeMap [contractOutcome [Hoperation [Houtcome _]]]].
  exists outcomeMap, contractOutcome.
  split.
  - exact Hoperation.
  - exact Houtcome.
Qed.

Theorem provider_state_transition_starts_inside_relation :
  forall qualifiedOutcomes model transition,
    ProviderStateQualifies qualifiedOutcomes model ->
    stateImplementationTransitions model transition ->
    exists abstractPre,
      stateRelated model (stateImplementationTransitionFrom transition) abstractPre.
Proof.
  intros qualifiedOutcomes model transition Hqualified Htransition.
  destruct (proj2 (proj2 Hqualified) transition Htransition)
    as [outcomeMap [contractOutcome [Hoperation [Houtcome [Hstart Hsimulation]]]]].
  exact Hstart.
Qed.

Theorem provider_state_simulates_every_related_prestate :
  forall qualifiedOutcomes model transition abstractPre,
    ProviderStateQualifies qualifiedOutcomes model ->
    stateImplementationTransitions model transition ->
    stateRelated model (stateImplementationTransitionFrom transition) abstractPre ->
    exists outcomeMap contractOutcome contractTransition,
      qualifiedOutcomes (stateImplementationTransitionOperation transition) = Some outcomeMap /\
      outcomeMap (stateImplementationTransitionOutcome transition) = Some contractOutcome /\
      stateContractTransitions model contractTransition /\
      stateContractTransitionOperation contractTransition =
        stateImplementationTransitionOperation transition /\
      stateContractTransitionFrom contractTransition = abstractPre /\
      stateContractTransitionOutcome contractTransition = contractOutcome /\
      stateRelated model
        (stateImplementationTransitionTo transition)
        (stateContractTransitionTo contractTransition).
Proof.
  intros qualifiedOutcomes model transition abstractPre Hqualified Htransition Hrelated.
  destruct (proj2 (proj2 Hqualified) transition Htransition)
    as [outcomeMap [contractOutcome [Hoperation [Houtcome [Hstart Hsimulation]]]]].
  destruct (Hsimulation abstractPre Hrelated) as
    [contractTransition [Hcontract [Hop [Hfrom [HcontractOutcome Hsuccessor]]]]].
  exists outcomeMap, contractOutcome, contractTransition.
  repeat split; assumption.
Qed.

(* PROV-007: deterministic provider-wide public-history laws. *)

Record ProviderImplementationEvent : Type := mkProviderImplementationEvent {
  lawImplementationEventOperation : ProviderOperationKey;
  lawImplementationEventOutcome : ProviderOutcomeKey
}.

Record ProviderPublicEvent : Type := mkProviderPublicEvent {
  lawPublicEventOperation : ProviderOperationKey;
  lawPublicEventOutcome : ProviderOutcomeKey
}.

Record ProviderLaw : Type := mkProviderLaw {
  providerLawRevision : ProviderLawRevision;
  providerLawInitialState : ProviderLawStateKey;
  providerLawTransition : ProviderLawStateKey -> ProviderPublicEvent -> option ProviderLawStateKey
}.

Definition translateProviderEvent
  (qualifiedOutcomes : ProviderQualifiedOutcomeMap)
  (event : ProviderImplementationEvent) : option ProviderPublicEvent :=
  match qualifiedOutcomes (lawImplementationEventOperation event) with
  | None => None
  | Some outcomeMap =>
      match outcomeMap (lawImplementationEventOutcome event) with
      | None => None
      | Some publicOutcome =>
          Some (mkProviderPublicEvent
            (lawImplementationEventOperation event)
            publicOutcome)
      end
  end.

Fixpoint translateProviderTrace
  (qualifiedOutcomes : ProviderQualifiedOutcomeMap)
  (trace : list ProviderImplementationEvent) : option (list ProviderPublicEvent) :=
  match trace with
  | [] => Some []
  | event :: rest =>
      match translateProviderEvent qualifiedOutcomes event,
            translateProviderTrace qualifiedOutcomes rest with
      | Some publicEvent, Some publicRest => Some (publicEvent :: publicRest)
      | _, _ => None
      end
  end.

Fixpoint runProviderLaw
  (law : ProviderLaw)
  (state : ProviderLawStateKey)
  (trace : list ProviderPublicEvent) : option ProviderLawStateKey :=
  match trace with
  | [] => Some state
  | event :: rest =>
      match providerLawTransition law state event with
      | None => None
      | Some nextState => runProviderLaw law nextState rest
      end
  end.

Definition ProviderLawTraceAccepts
  (qualifiedOutcomes : ProviderQualifiedOutcomeMap)
  (law : ProviderLaw)
  (implementationTrace : list ProviderImplementationEvent) : Prop :=
  exists publicTrace finalState,
    translateProviderTrace qualifiedOutcomes implementationTrace = Some publicTrace /\
    runProviderLaw law (providerLawInitialState law) publicTrace = Some finalState.

Theorem provider_law_empty_trace_accepts :
  forall qualifiedOutcomes law,
    ProviderLawTraceAccepts qualifiedOutcomes law [].
Proof.
  intros qualifiedOutcomes law.
  exists [], (providerLawInitialState law).
  split; reflexivity.
Qed.

Theorem accepted_provider_law_trace_has_exact_translation :
  forall qualifiedOutcomes law implementationTrace,
    ProviderLawTraceAccepts qualifiedOutcomes law implementationTrace ->
    exists publicTrace,
      translateProviderTrace qualifiedOutcomes implementationTrace = Some publicTrace.
Proof.
  intros qualifiedOutcomes law implementationTrace Haccepted.
  destruct Haccepted as [publicTrace [finalState [Htranslate Hrun]]].
  exists publicTrace.
  exact Htranslate.
Qed.

Theorem provider_law_translation_preserves_operation :
  forall qualifiedOutcomes event publicEvent,
    translateProviderEvent qualifiedOutcomes event = Some publicEvent ->
    lawPublicEventOperation publicEvent = lawImplementationEventOperation event.
Proof.
  intros qualifiedOutcomes event publicEvent Htranslated.
  unfold translateProviderEvent in Htranslated.
  destruct (qualifiedOutcomes (lawImplementationEventOperation event))
    as [outcomeMap |] eqn:Hoperation; try discriminate.
  destruct (outcomeMap (lawImplementationEventOutcome event))
    as [publicOutcome |] eqn:Houtcome; try discriminate.
  injection Htranslated as Hpublic.
  subst publicEvent.
  reflexivity.
Qed.

Theorem provider_law_translation_uses_exact_outcome_mapping :
  forall qualifiedOutcomes event publicEvent,
    translateProviderEvent qualifiedOutcomes event = Some publicEvent ->
    exists outcomeMap,
      qualifiedOutcomes (lawImplementationEventOperation event) = Some outcomeMap /\
      outcomeMap (lawImplementationEventOutcome event) =
        Some (lawPublicEventOutcome publicEvent).
Proof.
  intros qualifiedOutcomes event publicEvent Htranslated.
  unfold translateProviderEvent in Htranslated.
  destruct (qualifiedOutcomes (lawImplementationEventOperation event))
    as [outcomeMap |] eqn:Hoperation; try discriminate.
  destruct (outcomeMap (lawImplementationEventOutcome event))
    as [publicOutcome |] eqn:Houtcome; try discriminate.
  injection Htranslated as Hpublic.
  subst publicEvent.
  exists outcomeMap.
  split.
  - exact Hoperation.
  - cbn. exact Houtcome.
Qed.

Theorem unqualified_first_provider_event_rejects :
  forall qualifiedOutcomes law event rest,
    qualifiedOutcomes (lawImplementationEventOperation event) = None ->
    ~ ProviderLawTraceAccepts qualifiedOutcomes law (event :: rest).
Proof.
  intros qualifiedOutcomes law event rest Hmissing Haccepted.
  destruct Haccepted as [publicTrace [finalState [Htranslate Hrun]]].
  cbn in Htranslate.
  unfold translateProviderEvent in Htranslate.
  rewrite Hmissing in Htranslate.
  discriminate.
Qed.

Theorem unmapped_first_provider_outcome_rejects :
  forall qualifiedOutcomes law event rest outcomeMap,
    qualifiedOutcomes (lawImplementationEventOperation event) = Some outcomeMap ->
    outcomeMap (lawImplementationEventOutcome event) = None ->
    ~ ProviderLawTraceAccepts qualifiedOutcomes law (event :: rest).
Proof.
  intros qualifiedOutcomes law event rest outcomeMap Hoperation Hmissing Haccepted.
  destruct Haccepted as [publicTrace [finalState [Htranslate Hrun]]].
  cbn in Htranslate.
  unfold translateProviderEvent in Htranslate.
  rewrite Hoperation, Hmissing in Htranslate.
  discriminate.
Qed.

Theorem missing_provider_law_transition_rejects :
  forall law state event rest,
    providerLawTransition law state event = None ->
    runProviderLaw law state (event :: rest) = None.
Proof.
  intros law state event rest Hmissing.
  cbn.
  rewrite Hmissing.
  reflexivity.
Qed.

Theorem provider_law_run_is_deterministic :
  forall law state trace first second,
    runProviderLaw law state trace = Some first ->
    runProviderLaw law state trace = Some second ->
    first = second.
Proof.
  intros law state trace first second Hfirst Hsecond.
  rewrite Hfirst in Hsecond.
  injection Hsecond.
  trivial.
Qed.

(* PROV-008: lifecycle/crash/interruption qualification. *)

Inductive ProviderRetryDisposition : Type :=
| ProviderRetryForbidden
| ProviderRetrySameOperation
| ProviderRetryFromObservableState (state : ProviderObservableStateKey).

Record ProviderLifecyclePoint : Type := mkProviderLifecyclePoint {
  lifecyclePointOperation : ProviderOperationKey;
  lifecyclePointInterruption : ProviderInterruptionPointKey
}.

Record ProviderLifecycleAllowance : Type := mkProviderLifecycleAllowance {
  lifecycleAllowedObservableState : ProviderObservableStateKey -> Prop;
  lifecycleAllowedCleanupResidue : ProviderResourceResidue -> Prop;
  lifecycleAllowedRetryDisposition : ProviderRetryDisposition -> Prop
}.

Record ProviderInterruptionObservation : Type := mkProviderInterruptionObservation {
  lifecycleObservationBoundary : ProviderObservationBoundaryKey;
  lifecycleObservableState : ProviderObservableStateKey;
  lifecycleCleanupResidue : ProviderResourceResidue;
  lifecycleRetryDisposition : ProviderRetryDisposition
}.

Record ProviderLifecycleContract : Type := mkProviderLifecycleContract {
  lifecycleRevision : ProviderLifecycleRevision;
  lifecycleContractObservationBoundary : ProviderObservationBoundaryKey;
  lifecycleAllowances : ProviderLifecyclePoint -> option ProviderLifecycleAllowance
}.

Record ProviderLifecycleModel : Type := mkProviderLifecycleModel {
  lifecycleImplementationObservations :
    ProviderLifecyclePoint -> option (ProviderInterruptionObservation -> Prop)
}.

Definition ProviderLifecycleQualifies
  (qualifiedOperation : ProviderOperationKey -> Prop)
  (contract : ProviderLifecycleContract)
  (model : ProviderLifecycleModel) : Prop :=
  (forall point allowance,
    lifecycleAllowances contract point = Some allowance ->
    exists observations,
      lifecycleImplementationObservations model point = Some observations /\
      qualifiedOperation (lifecyclePointOperation point) /\
      (forall observation,
        observations observation ->
        lifecycleObservationBoundary observation =
          lifecycleContractObservationBoundary contract /\
        lifecycleAllowedObservableState allowance
          (lifecycleObservableState observation) /\
        lifecycleAllowedCleanupResidue allowance
          (lifecycleCleanupResidue observation) /\
        lifecycleAllowedRetryDisposition allowance
          (lifecycleRetryDisposition observation))) /\
  (forall point observations,
    lifecycleImplementationObservations model point = Some observations ->
    exists allowance,
      lifecycleAllowances contract point = Some allowance).

Theorem missing_provider_lifecycle_point_rejects :
  forall qualifiedOperation contract model point allowance,
    lifecycleAllowances contract point = Some allowance ->
    lifecycleImplementationObservations model point = None ->
    ~ ProviderLifecycleQualifies qualifiedOperation contract model.
Proof.
  intros qualifiedOperation contract model point allowance Hallowance Hmissing Hqualified.
  destruct Hqualified as [Htotal Hunexpected].
  destruct (Htotal point allowance Hallowance)
    as [observations [Hobservations _]].
  rewrite Hmissing in Hobservations.
  discriminate.
Qed.

Theorem unexpected_provider_lifecycle_point_rejects :
  forall qualifiedOperation contract model point observations,
    lifecycleAllowances contract point = None ->
    lifecycleImplementationObservations model point = Some observations ->
    ~ ProviderLifecycleQualifies qualifiedOperation contract model.
Proof.
  intros qualifiedOperation contract model point observations Hmissing Hobservations Hqualified.
  destruct Hqualified as [Htotal Hunexpected].
  destruct (Hunexpected point observations Hobservations) as [allowance Hallowance].
  rewrite Hmissing in Hallowance.
  discriminate.
Qed.

Theorem qualified_provider_lifecycle_point_uses_qualified_operation :
  forall qualifiedOperation contract model point allowance,
    ProviderLifecycleQualifies qualifiedOperation contract model ->
    lifecycleAllowances contract point = Some allowance ->
    qualifiedOperation (lifecyclePointOperation point).
Proof.
  intros qualifiedOperation contract model point allowance Hqualified Hallowance.
  destruct Hqualified as [Htotal Hunexpected].
  destruct (Htotal point allowance Hallowance)
    as [observations [Hobservations [Hoperation Hall]]].
  exact Hoperation.
Qed.

Theorem qualified_provider_lifecycle_observation_is_exact :
  forall qualifiedOperation contract model point allowance observations observation,
    ProviderLifecycleQualifies qualifiedOperation contract model ->
    lifecycleAllowances contract point = Some allowance ->
    lifecycleImplementationObservations model point = Some observations ->
    observations observation ->
    lifecycleObservationBoundary observation =
      lifecycleContractObservationBoundary contract /\
    lifecycleAllowedObservableState allowance
      (lifecycleObservableState observation) /\
    lifecycleAllowedCleanupResidue allowance
      (lifecycleCleanupResidue observation) /\
    lifecycleAllowedRetryDisposition allowance
      (lifecycleRetryDisposition observation).
Proof.
  intros qualifiedOperation contract model point allowance observations observation
    Hqualified Hallowance Hobservations Hobserved.
  destruct Hqualified as [Htotal Hunexpected].
  destruct (Htotal point allowance Hallowance)
    as [expectedObservations [Hexpected [Hoperation Hall]]].
  rewrite Hobservations in Hexpected.
  injection Hexpected as Heq.
  subst expectedObservations.
  exact (Hall observation Hobserved).
Qed.

Theorem forbidden_provider_observable_state_rejects :
  forall qualifiedOperation contract model point allowance observations observation,
    lifecycleAllowances contract point = Some allowance ->
    lifecycleImplementationObservations model point = Some observations ->
    observations observation ->
    ~ lifecycleAllowedObservableState allowance
        (lifecycleObservableState observation) ->
    ~ ProviderLifecycleQualifies qualifiedOperation contract model.
Proof.
  intros qualifiedOperation contract model point allowance observations observation
    Hallowance Hobservations Hobserved Hforbidden Hqualified.
  pose proof (qualified_provider_lifecycle_observation_is_exact
    qualifiedOperation contract model point allowance observations observation
    Hqualified Hallowance Hobservations Hobserved) as Hexact.
  destruct Hexact as [Hboundary [Hstate [Hcleanup Hretry]]].
  contradiction.
Qed.

Theorem forbidden_provider_cleanup_residue_rejects :
  forall qualifiedOperation contract model point allowance observations observation,
    lifecycleAllowances contract point = Some allowance ->
    lifecycleImplementationObservations model point = Some observations ->
    observations observation ->
    ~ lifecycleAllowedCleanupResidue allowance
        (lifecycleCleanupResidue observation) ->
    ~ ProviderLifecycleQualifies qualifiedOperation contract model.
Proof.
  intros qualifiedOperation contract model point allowance observations observation
    Hallowance Hobservations Hobserved Hforbidden Hqualified.
  pose proof (qualified_provider_lifecycle_observation_is_exact
    qualifiedOperation contract model point allowance observations observation
    Hqualified Hallowance Hobservations Hobserved) as Hexact.
  destruct Hexact as [Hboundary [Hstate [Hcleanup Hretry]]].
  contradiction.
Qed.

Theorem forbidden_provider_retry_disposition_rejects :
  forall qualifiedOperation contract model point allowance observations observation,
    lifecycleAllowances contract point = Some allowance ->
    lifecycleImplementationObservations model point = Some observations ->
    observations observation ->
    ~ lifecycleAllowedRetryDisposition allowance
        (lifecycleRetryDisposition observation) ->
    ~ ProviderLifecycleQualifies qualifiedOperation contract model.
Proof.
  intros qualifiedOperation contract model point allowance observations observation
    Hallowance Hobservations Hobserved Hforbidden Hqualified.
  pose proof (qualified_provider_lifecycle_observation_is_exact
    qualifiedOperation contract model point allowance observations observation
    Hqualified Hallowance Hobservations Hobserved) as Hexact.
  destruct Hexact as [Hboundary [Hstate [Hcleanup Hretry]]].
  contradiction.
Qed.
