From Stdlib Require Import Bool.Bool Lists.List.
Import ListNotations.

From Phil.Core Require Import ProviderQualificationImplementationBridge.

(*
  PHIL-PROV-LAW-IMPL-001 — finite executable PROV-007 history-law checking.

  The kernel owns two exact steps: translate each implementation event through
  the already-qualified operation/outcome correspondence, then run the resulting
  public trace through a deterministic finite law-state transition map.
*)

Definition ProviderLawImplementationEvent
  (OperationKey OutcomeKey : Type) : Type :=
  (OperationKey * OutcomeKey)%type.

Definition ProviderLawPublicEvent
  (OperationKey OutcomeKey : Type) : Type :=
  (OperationKey * OutcomeKey)%type.

Definition ProviderLawTransitionKey
  (LawState OperationKey OutcomeKey : Type) : Type :=
  (LawState * ProviderLawPublicEvent OperationKey OutcomeKey)%type.

Definition publicEventEqualb
  {OperationKey OutcomeKey : Type}
  (eqOperation : OperationKey -> OperationKey -> bool)
  (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
  (first second : ProviderLawPublicEvent OperationKey OutcomeKey) : bool :=
  eqOperation (fst first) (fst second) &&
  eqOutcome (snd first) (snd second).

Definition lawTransitionKeyEqualb
  {LawState OperationKey OutcomeKey : Type}
  (eqLawState : LawState -> LawState -> bool)
  (eqOperation : OperationKey -> OperationKey -> bool)
  (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
  (first second : ProviderLawTransitionKey LawState OperationKey OutcomeKey) : bool :=
  eqLawState (fst first) (fst second) &&
  publicEventEqualb eqOperation eqOutcome (snd first) (snd second).

Definition translateProviderLawEvent
  {OperationKey OutcomeKey : Type}
  (eqOperation : OperationKey -> OperationKey -> bool)
  (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
  (qualifiedOutcomes
    : list (OperationKey * list (OutcomeKey * OutcomeKey)))
  (event : ProviderLawImplementationEvent OperationKey OutcomeKey)
  : option (ProviderLawPublicEvent OperationKey OutcomeKey) :=
  match lookupAssoc eqOperation (fst event) qualifiedOutcomes with
  | None => None
  | Some outcomeMap =>
      match lookupAssoc eqOutcome (snd event) outcomeMap with
      | None => None
      | Some publicOutcome => Some (fst event, publicOutcome)
      end
  end.

Fixpoint translateProviderLawTrace
  {OperationKey OutcomeKey : Type}
  (eqOperation : OperationKey -> OperationKey -> bool)
  (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
  (qualifiedOutcomes
    : list (OperationKey * list (OutcomeKey * OutcomeKey)))
  (trace : list (ProviderLawImplementationEvent OperationKey OutcomeKey))
  : option (list (ProviderLawPublicEvent OperationKey OutcomeKey)) :=
  match trace with
  | [] => Some []
  | event :: rest =>
      match translateProviderLawEvent
              eqOperation eqOutcome qualifiedOutcomes event,
            translateProviderLawTrace
              eqOperation eqOutcome qualifiedOutcomes rest with
      | Some publicEvent, Some publicRest => Some (publicEvent :: publicRest)
      | _, _ => None
      end
  end.

Fixpoint runProviderLawKernel
  {LawState OperationKey OutcomeKey : Type}
  (eqLawState : LawState -> LawState -> bool)
  (eqOperation : OperationKey -> OperationKey -> bool)
  (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
  (transitions
    : list (ProviderLawTransitionKey LawState OperationKey OutcomeKey * LawState))
  (state : LawState)
  (trace : list (ProviderLawPublicEvent OperationKey OutcomeKey))
  : option LawState :=
  match trace with
  | [] => Some state
  | event :: rest =>
      match lookupAssoc
        (lawTransitionKeyEqualb eqLawState eqOperation eqOutcome)
        (state, event)
        transitions with
      | None => None
      | Some nextState =>
          runProviderLawKernel
            eqLawState eqOperation eqOutcome transitions nextState rest
      end
  end.

Definition decideProviderLawTrace
  {LawState OperationKey OutcomeKey : Type}
  (eqLawState : LawState -> LawState -> bool)
  (eqOperation : OperationKey -> OperationKey -> bool)
  (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
  (qualifiedOutcomes
    : list (OperationKey * list (OutcomeKey * OutcomeKey)))
  (transitions
    : list (ProviderLawTransitionKey LawState OperationKey OutcomeKey * LawState))
  (initialState : LawState)
  (implementationTrace
    : list (ProviderLawImplementationEvent OperationKey OutcomeKey)) : bool :=
  match translateProviderLawTrace
      eqOperation eqOutcome qualifiedOutcomes implementationTrace with
  | None => false
  | Some publicTrace =>
      match runProviderLawKernel
        eqLawState eqOperation eqOutcome transitions initialState publicTrace with
      | None => false
      | Some _ => true
      end
  end.

Definition ProviderLawTraversalAccepts
  {LawState OperationKey OutcomeKey : Type}
  (eqLawState : LawState -> LawState -> bool)
  (eqOperation : OperationKey -> OperationKey -> bool)
  (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
  (qualifiedOutcomes
    : list (OperationKey * list (OutcomeKey * OutcomeKey)))
  (transitions
    : list (ProviderLawTransitionKey LawState OperationKey OutcomeKey * LawState))
  (initialState : LawState)
  (implementationTrace
    : list (ProviderLawImplementationEvent OperationKey OutcomeKey)) : Prop :=
  exists publicTrace finalState,
    translateProviderLawTrace
      eqOperation eqOutcome qualifiedOutcomes implementationTrace = Some publicTrace /\
    runProviderLawKernel
      eqLawState eqOperation eqOutcome transitions initialState publicTrace = Some finalState.

Theorem decide_provider_law_trace_true_iff :
  forall (LawState OperationKey OutcomeKey : Type)
      (eqLawState : LawState -> LawState -> bool)
      (eqOperation : OperationKey -> OperationKey -> bool)
      (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
      (qualifiedOutcomes
        : list (OperationKey * list (OutcomeKey * OutcomeKey)))
      (transitions
        : list (ProviderLawTransitionKey LawState OperationKey OutcomeKey * LawState))
      (initialState : LawState)
      (implementationTrace
        : list (ProviderLawImplementationEvent OperationKey OutcomeKey)),
    decideProviderLawTrace
      eqLawState eqOperation eqOutcome qualifiedOutcomes
      transitions initialState implementationTrace = true <->
    ProviderLawTraversalAccepts
      eqLawState eqOperation eqOutcome qualifiedOutcomes
      transitions initialState implementationTrace.
Proof.
  intros LawState OperationKey OutcomeKey eqLawState eqOperation eqOutcome
    qualifiedOutcomes transitions initialState implementationTrace.
  split.
  - intro Haccepted.
    unfold decideProviderLawTrace in Haccepted.
    destruct (translateProviderLawTrace
      eqOperation eqOutcome qualifiedOutcomes implementationTrace)
      as [publicTrace |] eqn:Htranslate; try discriminate.
    destruct (runProviderLawKernel
      eqLawState eqOperation eqOutcome transitions initialState publicTrace)
      as [finalState |] eqn:Hrun; try discriminate.
    exists publicTrace, finalState.
    split.
    + exact Htranslate.
    + exact Hrun.
  - intros [publicTrace [finalState [Htranslate Hrun]]].
    unfold decideProviderLawTrace.
    rewrite Htranslate, Hrun.
    reflexivity.
Qed.

Theorem translated_provider_law_event_uses_exact_mapping :
  forall (OperationKey OutcomeKey : Type)
      (eqOperation : OperationKey -> OperationKey -> bool)
      (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
      (qualifiedOutcomes
        : list (OperationKey * list (OutcomeKey * OutcomeKey)))
      (event : ProviderLawImplementationEvent OperationKey OutcomeKey)
      (publicEvent : ProviderLawPublicEvent OperationKey OutcomeKey),
    translateProviderLawEvent
      eqOperation eqOutcome qualifiedOutcomes event = Some publicEvent ->
    fst publicEvent = fst event /\
    exists outcomeMap,
      lookupAssoc eqOperation (fst event) qualifiedOutcomes = Some outcomeMap /\
      lookupAssoc eqOutcome (snd event) outcomeMap = Some (snd publicEvent).
Proof.
  intros OperationKey OutcomeKey eqOperation eqOutcome
    qualifiedOutcomes event publicEvent Htranslated.
  unfold translateProviderLawEvent in Htranslated.
  destruct (lookupAssoc eqOperation (fst event) qualifiedOutcomes)
    as [outcomeMap |] eqn:Hoperation; try discriminate.
  destruct (lookupAssoc eqOutcome (snd event) outcomeMap)
    as [publicOutcome |] eqn:Houtcome; try discriminate.
  injection Htranslated as Hpublic.
  subst publicEvent.
  split.
  - reflexivity.
  - exists outcomeMap.
    split.
    + exact Hoperation.
    + cbn. exact Houtcome.
Qed.

Theorem provider_law_kernel_empty_trace :
  forall (LawState OperationKey OutcomeKey : Type)
      (eqLawState : LawState -> LawState -> bool)
      (eqOperation : OperationKey -> OperationKey -> bool)
      (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
      (transitions
        : list (ProviderLawTransitionKey LawState OperationKey OutcomeKey * LawState))
      (state : LawState),
    runProviderLawKernel
      eqLawState eqOperation eqOutcome transitions state [] = Some state.
Proof.
  reflexivity.
Qed.

Theorem missing_provider_law_kernel_transition_rejects :
  forall (LawState OperationKey OutcomeKey : Type)
      (eqLawState : LawState -> LawState -> bool)
      (eqOperation : OperationKey -> OperationKey -> bool)
      (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
      (transitions
        : list (ProviderLawTransitionKey LawState OperationKey OutcomeKey * LawState))
      (state : LawState)
      (event : ProviderLawPublicEvent OperationKey OutcomeKey)
      (rest : list (ProviderLawPublicEvent OperationKey OutcomeKey)),
    lookupAssoc
      (lawTransitionKeyEqualb eqLawState eqOperation eqOutcome)
      (state, event)
      transitions = None ->
    runProviderLawKernel
      eqLawState eqOperation eqOutcome transitions state (event :: rest) = None.
Proof.
  intros LawState OperationKey OutcomeKey eqLawState eqOperation eqOutcome
    transitions state event rest Hmissing.
  cbn.
  rewrite Hmissing.
  reflexivity.
Qed.

Theorem provider_law_kernel_is_deterministic :
  forall (LawState OperationKey OutcomeKey : Type)
      (eqLawState : LawState -> LawState -> bool)
      (eqOperation : OperationKey -> OperationKey -> bool)
      (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
      (transitions
        : list (ProviderLawTransitionKey LawState OperationKey OutcomeKey * LawState))
      (state : LawState)
      (trace : list (ProviderLawPublicEvent OperationKey OutcomeKey))
      first second,
    runProviderLawKernel
      eqLawState eqOperation eqOutcome transitions state trace = Some first ->
    runProviderLawKernel
      eqLawState eqOperation eqOutcome transitions state trace = Some second ->
    first = second.
Proof.
  intros LawState OperationKey OutcomeKey eqLawState eqOperation eqOutcome
    transitions state trace first second Hfirst Hsecond.
  rewrite Hfirst in Hsecond.
  injection Hsecond.
  trivial.
Qed.
