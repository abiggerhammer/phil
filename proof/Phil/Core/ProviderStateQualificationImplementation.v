From Stdlib Require Import Bool.Bool Lists.List.
Import ListNotations.

From Phil.Core Require Import ProviderQualificationImplementationBridge.

(*
  PHIL-PROV-STATE-IMPL-001 — finite executable PROV-006 state simulation.

  Production Set/Map values are projected to canonical finite lists. This
  bounded kernel owns the traversal structure: exact visible-initial domain,
  initial admissibility/relation checks, qualified operation/outcome lookup,
  nonempty related abstract pre-state discovery, and universal simulation of
  every related pre-state. Concrete Haskell round-trip representation bridges
  and final production binding remain the next tranche.
*)

Record StatePair (ImplementationState AbstractState : Type) : Type :=
  mkStatePair {
    statePairImplementation : ImplementationState;
    statePairAbstract : AbstractState
  }.

Record StateImplementationTransition
    (OperationKey ImplementationState OutcomeKey : Type) : Type :=
  mkStateImplementationTransition {
    stateImplementationOperation : OperationKey;
    stateImplementationFrom : ImplementationState;
    stateImplementationOutcome : OutcomeKey;
    stateImplementationTo : ImplementationState
  }.

Record StateContractTransition
    (OperationKey AbstractState OutcomeKey : Type) : Type :=
  mkStateContractTransition {
    stateContractOperation : OperationKey;
    stateContractFrom : AbstractState;
    stateContractOutcome : OutcomeKey;
    stateContractTo : AbstractState
  }.

Fixpoint memberByb {A : Type}
  (equal : A -> A -> bool)
  (target : A)
  (values : list A) : bool :=
  match values with
  | [] => false
  | value :: rest =>
      if equal target value then true else memberByb equal target rest
  end.

Fixpoint anyFiniteb {A : Type}
  (predicate : A -> bool)
  (values : list A) : bool :=
  match values with
  | [] => false
  | value :: rest => predicate value || anyFiniteb predicate rest
  end.

Fixpoint sameInitialDomainb {ImplementationState AbstractState : Type}
  (eqImplementationState : ImplementationState -> ImplementationState -> bool)
  (visibleInitial : list ImplementationState)
  (initialCorrespondence : list (ImplementationState * AbstractState)) : bool :=
  match visibleInitial, initialCorrespondence with
  | [], [] => true
  | visible :: visibleRest, (implementationState, _) :: correspondenceRest =>
      eqImplementationState visible implementationState &&
      sameInitialDomainb
        eqImplementationState visibleRest correspondenceRest
  | _, _ => false
  end.

Definition statePairEqualb
  {ImplementationState AbstractState : Type}
  (eqImplementationState : ImplementationState -> ImplementationState -> bool)
  (eqAbstractState : AbstractState -> AbstractState -> bool)
  (first second : StatePair ImplementationState AbstractState) : bool :=
  eqImplementationState
    (statePairImplementation _ _ first)
    (statePairImplementation _ _ second) &&
  eqAbstractState
    (statePairAbstract _ _ first)
    (statePairAbstract _ _ second).

Definition decideInitialPair
  {ImplementationState AbstractState : Type}
  (eqImplementationState : ImplementationState -> ImplementationState -> bool)
  (eqAbstractState : AbstractState -> AbstractState -> bool)
  (admissibleInitial : list AbstractState)
  (relatedPairs : list (StatePair ImplementationState AbstractState))
  (entry : ImplementationState * AbstractState) : bool :=
  let implementationState := fst entry in
  let abstractState := snd entry in
  memberByb eqAbstractState abstractState admissibleInitial &&
  memberByb
    (statePairEqualb eqImplementationState eqAbstractState)
    (mkStatePair _ _ implementationState abstractState)
    relatedPairs.

Fixpoint relatedAbstractStates
  {ImplementationState AbstractState : Type}
  (eqImplementationState : ImplementationState -> ImplementationState -> bool)
  (implementationState : ImplementationState)
  (relatedPairs : list (StatePair ImplementationState AbstractState))
  : list AbstractState :=
  match relatedPairs with
  | [] => []
  | statePair :: rest =>
      if eqImplementationState
          implementationState
          (statePairImplementation _ _ statePair)
      then statePairAbstract _ _ statePair ::
           relatedAbstractStates eqImplementationState implementationState rest
      else relatedAbstractStates eqImplementationState implementationState rest
  end.

Definition contractTransitionSimulates
  {OperationKey ImplementationState AbstractState OutcomeKey : Type}
  (eqOperation : OperationKey -> OperationKey -> bool)
  (eqAbstractState : AbstractState -> AbstractState -> bool)
  (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
  (eqImplementationState : ImplementationState -> ImplementationState -> bool)
  (relatedPairs : list (StatePair ImplementationState AbstractState))
  (implementationTransition
    : StateImplementationTransition OperationKey ImplementationState OutcomeKey)
  (contractOutcome : OutcomeKey)
  (abstractPre : AbstractState)
  (contractTransition
    : StateContractTransition OperationKey AbstractState OutcomeKey) : bool :=
  eqOperation
    (stateContractOperation _ _ _ contractTransition)
    (stateImplementationOperation _ _ _ implementationTransition) &&
  (eqAbstractState
    (stateContractFrom _ _ _ contractTransition)
    abstractPre &&
  (eqOutcome
    (stateContractOutcome _ _ _ contractTransition)
    contractOutcome &&
  memberByb
    (statePairEqualb eqImplementationState eqAbstractState)
    (mkStatePair _ _
      (stateImplementationTo _ _ _ implementationTransition)
      (stateContractTo _ _ _ contractTransition))
    relatedPairs)).

Definition decideRelatedPrestate
  {OperationKey ImplementationState AbstractState OutcomeKey : Type}
  (eqOperation : OperationKey -> OperationKey -> bool)
  (eqAbstractState : AbstractState -> AbstractState -> bool)
  (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
  (eqImplementationState : ImplementationState -> ImplementationState -> bool)
  (relatedPairs : list (StatePair ImplementationState AbstractState))
  (contractTransitions
    : list (StateContractTransition OperationKey AbstractState OutcomeKey))
  (implementationTransition
    : StateImplementationTransition OperationKey ImplementationState OutcomeKey)
  (contractOutcome : OutcomeKey)
  (abstractPre : AbstractState) : bool :=
  anyFiniteb
    (contractTransitionSimulates
      eqOperation eqAbstractState eqOutcome eqImplementationState
      relatedPairs implementationTransition contractOutcome abstractPre)
    contractTransitions.

Definition decideStateTransition
  {OperationKey ImplementationState AbstractState OutcomeKey : Type}
  (eqOperation : OperationKey -> OperationKey -> bool)
  (eqImplementationState : ImplementationState -> ImplementationState -> bool)
  (eqAbstractState : AbstractState -> AbstractState -> bool)
  (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
  (qualifiedOutcomes
    : list (OperationKey * list (OutcomeKey * OutcomeKey)))
  (relatedPairs : list (StatePair ImplementationState AbstractState))
  (contractTransitions
    : list (StateContractTransition OperationKey AbstractState OutcomeKey))
  (transition
    : StateImplementationTransition OperationKey ImplementationState OutcomeKey)
  : bool :=
  match lookupAssoc
      eqOperation
      (stateImplementationOperation _ _ _ transition)
      qualifiedOutcomes with
  | None => false
  | Some outcomeMap =>
      match lookupAssoc
          eqOutcome
          (stateImplementationOutcome _ _ _ transition)
          outcomeMap with
      | None => false
      | Some contractOutcome =>
          match relatedAbstractStates
              eqImplementationState
              (stateImplementationFrom _ _ _ transition)
              relatedPairs with
          | [] => false
          | relatedPrestates =>
              allFiniteb
                (decideRelatedPrestate
                  eqOperation eqAbstractState eqOutcome eqImplementationState
                  relatedPairs contractTransitions transition contractOutcome)
                relatedPrestates
          end
      end
  end.

Definition decideProviderStateSimulation
  {OperationKey ImplementationState AbstractState OutcomeKey : Type}
  (eqOperation : OperationKey -> OperationKey -> bool)
  (eqImplementationState : ImplementationState -> ImplementationState -> bool)
  (eqAbstractState : AbstractState -> AbstractState -> bool)
  (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
  (visibleInitial : list ImplementationState)
  (admissibleInitial : list AbstractState)
  (initialCorrespondence : list (ImplementationState * AbstractState))
  (qualifiedOutcomes
    : list (OperationKey * list (OutcomeKey * OutcomeKey)))
  (relatedPairs : list (StatePair ImplementationState AbstractState))
  (implementationTransitions
    : list (StateImplementationTransition OperationKey ImplementationState OutcomeKey))
  (contractTransitions
    : list (StateContractTransition OperationKey AbstractState OutcomeKey))
  : bool :=
  sameInitialDomainb
    eqImplementationState visibleInitial initialCorrespondence &&
  (allFiniteb
    (decideInitialPair
      eqImplementationState eqAbstractState admissibleInitial relatedPairs)
    initialCorrespondence &&
   allFiniteb
    (decideStateTransition
      eqOperation eqImplementationState eqAbstractState eqOutcome
      qualifiedOutcomes relatedPairs contractTransitions)
    implementationTransitions).

Definition ProviderStateTraversalAccepts
  {OperationKey ImplementationState AbstractState OutcomeKey : Type}
  (eqOperation : OperationKey -> OperationKey -> bool)
  (eqImplementationState : ImplementationState -> ImplementationState -> bool)
  (eqAbstractState : AbstractState -> AbstractState -> bool)
  (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
  (visibleInitial : list ImplementationState)
  (admissibleInitial : list AbstractState)
  (initialCorrespondence : list (ImplementationState * AbstractState))
  (qualifiedOutcomes
    : list (OperationKey * list (OutcomeKey * OutcomeKey)))
  (relatedPairs : list (StatePair ImplementationState AbstractState))
  (implementationTransitions
    : list (StateImplementationTransition OperationKey ImplementationState OutcomeKey))
  (contractTransitions
    : list (StateContractTransition OperationKey AbstractState OutcomeKey)) : Prop :=
  sameInitialDomainb
    eqImplementationState visibleInitial initialCorrespondence = true /\
  Forall
    (fun entry =>
      decideInitialPair
        eqImplementationState eqAbstractState admissibleInitial relatedPairs entry = true)
    initialCorrespondence /\
  Forall
    (fun transition =>
      decideStateTransition
        eqOperation eqImplementationState eqAbstractState eqOutcome
        qualifiedOutcomes relatedPairs contractTransitions transition = true)
    implementationTransitions.

Theorem decide_provider_state_simulation_true_iff :
  forall (OperationKey ImplementationState AbstractState OutcomeKey : Type)
      (eqOperation : OperationKey -> OperationKey -> bool)
      (eqImplementationState : ImplementationState -> ImplementationState -> bool)
      (eqAbstractState : AbstractState -> AbstractState -> bool)
      (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
      (visibleInitial : list ImplementationState)
      (admissibleInitial : list AbstractState)
      (initialCorrespondence : list (ImplementationState * AbstractState))
      (qualifiedOutcomes : list (OperationKey * list (OutcomeKey * OutcomeKey)))
      (relatedPairs : list (StatePair ImplementationState AbstractState))
      (implementationTransitions
        : list (StateImplementationTransition OperationKey ImplementationState OutcomeKey))
      (contractTransitions
        : list (StateContractTransition OperationKey AbstractState OutcomeKey)),
    decideProviderStateSimulation
      eqOperation eqImplementationState eqAbstractState eqOutcome
      visibleInitial admissibleInitial initialCorrespondence qualifiedOutcomes
      relatedPairs implementationTransitions contractTransitions = true <->
    ProviderStateTraversalAccepts
      eqOperation eqImplementationState eqAbstractState eqOutcome
      visibleInitial admissibleInitial initialCorrespondence qualifiedOutcomes
      relatedPairs implementationTransitions contractTransitions.
Proof.
  intros OperationKey ImplementationState AbstractState OutcomeKey
    eqOperation eqImplementationState eqAbstractState eqOutcome
    visibleInitial admissibleInitial initialCorrespondence qualifiedOutcomes
    relatedPairs implementationTransitions contractTransitions.
  unfold decideProviderStateSimulation, ProviderStateTraversalAccepts.
  repeat rewrite andb_true_iff.
  repeat rewrite all_finiteb_true_iff.
  reflexivity.
Qed.

Theorem accepted_initial_pair_is_admissible_and_related :
  forall (ImplementationState AbstractState : Type)
      (eqImplementationState : ImplementationState -> ImplementationState -> bool)
      (eqAbstractState : AbstractState -> AbstractState -> bool)
      (admissibleInitial : list AbstractState)
      (relatedPairs : list (StatePair ImplementationState AbstractState))
      (entry : ImplementationState * AbstractState),
    decideInitialPair
      eqImplementationState eqAbstractState admissibleInitial relatedPairs entry = true ->
    memberByb eqAbstractState (snd entry) admissibleInitial = true /\
    memberByb
      (statePairEqualb eqImplementationState eqAbstractState)
      (mkStatePair _ _ (fst entry) (snd entry))
      relatedPairs = true.
Proof.
  intros ImplementationState AbstractState eqImplementationState eqAbstractState
    admissibleInitial relatedPairs entry Haccepted.
  unfold decideInitialPair in Haccepted.
  apply andb_true_iff in Haccepted.
  exact Haccepted.
Qed.

Theorem accepted_state_transition_has_qualified_outcome :
  forall (OperationKey ImplementationState AbstractState OutcomeKey : Type)
      (eqOperation : OperationKey -> OperationKey -> bool)
      (eqImplementationState : ImplementationState -> ImplementationState -> bool)
      (eqAbstractState : AbstractState -> AbstractState -> bool)
      (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
      (qualifiedOutcomes : list (OperationKey * list (OutcomeKey * OutcomeKey)))
      (relatedPairs : list (StatePair ImplementationState AbstractState))
      (contractTransitions
        : list (StateContractTransition OperationKey AbstractState OutcomeKey))
      (transition
        : StateImplementationTransition OperationKey ImplementationState OutcomeKey),
    decideStateTransition
      eqOperation eqImplementationState eqAbstractState eqOutcome
      qualifiedOutcomes relatedPairs contractTransitions transition = true ->
    exists outcomeMap contractOutcome,
      lookupAssoc
        eqOperation
        (stateImplementationOperation _ _ _ transition)
        qualifiedOutcomes = Some outcomeMap /\
      lookupAssoc
        eqOutcome
        (stateImplementationOutcome _ _ _ transition)
        outcomeMap = Some contractOutcome.
Proof.
  intros OperationKey ImplementationState AbstractState OutcomeKey
    eqOperation eqImplementationState eqAbstractState eqOutcome
    qualifiedOutcomes relatedPairs contractTransitions transition Haccepted.
  unfold decideStateTransition in Haccepted.
  destruct (lookupAssoc
    eqOperation
    (stateImplementationOperation _ _ _ transition)
    qualifiedOutcomes) as [outcomeMap|] eqn:Hoperation; try discriminate.
  destruct (lookupAssoc
    eqOutcome
    (stateImplementationOutcome _ _ _ transition)
    outcomeMap) as [contractOutcome|] eqn:Houtcome; try discriminate.
  destruct (relatedAbstractStates
    eqImplementationState
    (stateImplementationFrom _ _ _ transition)
    relatedPairs) as [| abstractPre rest] eqn:Hrelated; try discriminate.
  exists outcomeMap, contractOutcome.
  split; assumption.
Qed.

Theorem accepted_state_transition_has_related_prestate :
  forall (OperationKey ImplementationState AbstractState OutcomeKey : Type)
      (eqOperation : OperationKey -> OperationKey -> bool)
      (eqImplementationState : ImplementationState -> ImplementationState -> bool)
      (eqAbstractState : AbstractState -> AbstractState -> bool)
      (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
      (qualifiedOutcomes : list (OperationKey * list (OutcomeKey * OutcomeKey)))
      (relatedPairs : list (StatePair ImplementationState AbstractState))
      (contractTransitions
        : list (StateContractTransition OperationKey AbstractState OutcomeKey))
      (transition
        : StateImplementationTransition OperationKey ImplementationState OutcomeKey),
    decideStateTransition
      eqOperation eqImplementationState eqAbstractState eqOutcome
      qualifiedOutcomes relatedPairs contractTransitions transition = true ->
    exists abstractPre,
      In abstractPre
        (relatedAbstractStates
          eqImplementationState
          (stateImplementationFrom _ _ _ transition)
          relatedPairs).
Proof.
  intros OperationKey ImplementationState AbstractState OutcomeKey
    eqOperation eqImplementationState eqAbstractState eqOutcome
    qualifiedOutcomes relatedPairs contractTransitions transition Haccepted.
  unfold decideStateTransition in Haccepted.
  destruct (lookupAssoc
    eqOperation
    (stateImplementationOperation _ _ _ transition)
    qualifiedOutcomes) as [outcomeMap|] eqn:Hoperation; try discriminate.
  destruct (lookupAssoc
    eqOutcome
    (stateImplementationOutcome _ _ _ transition)
    outcomeMap) as [contractOutcome|] eqn:Houtcome; try discriminate.
  destruct (relatedAbstractStates
    eqImplementationState
    (stateImplementationFrom _ _ _ transition)
    relatedPairs) as [| abstractPre rest] eqn:Hrelated; try discriminate.
  exists abstractPre.
  rewrite Hrelated.
  left. reflexivity.
Qed.

Theorem accepted_state_transition_simulates_every_related_prestate :
  forall (OperationKey ImplementationState AbstractState OutcomeKey : Type)
      (eqOperation : OperationKey -> OperationKey -> bool)
      (eqImplementationState : ImplementationState -> ImplementationState -> bool)
      (eqAbstractState : AbstractState -> AbstractState -> bool)
      (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
      (qualifiedOutcomes : list (OperationKey * list (OutcomeKey * OutcomeKey)))
      (relatedPairs : list (StatePair ImplementationState AbstractState))
      (contractTransitions
        : list (StateContractTransition OperationKey AbstractState OutcomeKey))
      (transition
        : StateImplementationTransition OperationKey ImplementationState OutcomeKey),
    decideStateTransition
      eqOperation eqImplementationState eqAbstractState eqOutcome
      qualifiedOutcomes relatedPairs contractTransitions transition = true ->
    exists outcomeMap contractOutcome,
      lookupAssoc
        eqOperation
        (stateImplementationOperation _ _ _ transition)
        qualifiedOutcomes = Some outcomeMap /\
      lookupAssoc
        eqOutcome
        (stateImplementationOutcome _ _ _ transition)
        outcomeMap = Some contractOutcome /\
      Forall
        (fun abstractPre =>
          decideRelatedPrestate
            eqOperation eqAbstractState eqOutcome eqImplementationState
            relatedPairs contractTransitions transition contractOutcome abstractPre = true)
        (relatedAbstractStates
          eqImplementationState
          (stateImplementationFrom _ _ _ transition)
          relatedPairs).
Proof.
  intros OperationKey ImplementationState AbstractState OutcomeKey
    eqOperation eqImplementationState eqAbstractState eqOutcome
    qualifiedOutcomes relatedPairs contractTransitions transition Haccepted.
  unfold decideStateTransition in Haccepted.
  destruct (lookupAssoc
    eqOperation
    (stateImplementationOperation _ _ _ transition)
    qualifiedOutcomes) as [outcomeMap|] eqn:Hoperation; try discriminate.
  destruct (lookupAssoc
    eqOutcome
    (stateImplementationOutcome _ _ _ transition)
    outcomeMap) as [contractOutcome|] eqn:Houtcome; try discriminate.
  destruct (relatedAbstractStates
    eqImplementationState
    (stateImplementationFrom _ _ _ transition)
    relatedPairs) as [| abstractPre rest] eqn:Hrelated; try discriminate.
  exists outcomeMap, contractOutcome.
  repeat split; try assumption.
  rewrite Hrelated.
  apply (proj1
    (all_finiteb_true_iff
      AbstractState
      (decideRelatedPrestate
        eqOperation eqAbstractState eqOutcome eqImplementationState
        relatedPairs contractTransitions transition contractOutcome)
      (abstractPre :: rest))).
  exact Haccepted.
Qed.
