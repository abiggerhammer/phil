module ProviderStateQualificationKernel where

import qualified Prelude

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

orb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
orb b1 b2 =
  case b1 of {
   Prelude.True -> Prelude.True;
   Prelude.False -> b2}

fst :: ((,) a1 a2) -> a1
fst p =
  case p of {
   (,) x _ -> x}

snd :: ((,) a1 a2) -> a2
snd p =
  case p of {
   (,) _ y -> y}

lookupAssoc :: (a1 -> a1 -> Prelude.Bool) -> a1 -> ([] ((,) a1 a2)) ->
               Prelude.Maybe a2
lookupAssoc eqKey key entries =
  case entries of {
   [] -> Prelude.Nothing;
   (:) p rest ->
    case p of {
     (,) entryKey value ->
      case eqKey key entryKey of {
       Prelude.True -> Prelude.Just value;
       Prelude.False -> lookupAssoc eqKey key rest}}}

allFiniteb :: (a1 -> Prelude.Bool) -> ([] a1) -> Prelude.Bool
allFiniteb predicate values =
  case values of {
   [] -> Prelude.True;
   (:) value rest -> andb (predicate value) (allFiniteb predicate rest)}

data StatePair implementationState abstractState =
   MkStatePair implementationState abstractState

statePairImplementation :: (StatePair a1 a2) -> a1
statePairImplementation s =
  case s of {
   MkStatePair statePairImplementation0 _ -> statePairImplementation0}

statePairAbstract :: (StatePair a1 a2) -> a2
statePairAbstract s =
  case s of {
   MkStatePair _ statePairAbstract0 -> statePairAbstract0}

data StateImplementationTransition operationKey implementationState outcomeKey =
   MkStateImplementationTransition operationKey implementationState outcomeKey 
 implementationState

stateImplementationOperation :: (StateImplementationTransition a1 a2 
                                a3) -> a1
stateImplementationOperation s =
  case s of {
   MkStateImplementationTransition stateImplementationOperation0 _ _ _ ->
    stateImplementationOperation0}

stateImplementationFrom :: (StateImplementationTransition a1 a2 a3) -> a2
stateImplementationFrom s =
  case s of {
   MkStateImplementationTransition _ stateImplementationFrom0 _ _ ->
    stateImplementationFrom0}

stateImplementationOutcome :: (StateImplementationTransition a1 a2 a3) -> a3
stateImplementationOutcome s =
  case s of {
   MkStateImplementationTransition _ _ stateImplementationOutcome0 _ ->
    stateImplementationOutcome0}

stateImplementationTo :: (StateImplementationTransition a1 a2 a3) -> a2
stateImplementationTo s =
  case s of {
   MkStateImplementationTransition _ _ _ stateImplementationTo0 ->
    stateImplementationTo0}

data StateContractTransition operationKey abstractState outcomeKey =
   MkStateContractTransition operationKey abstractState outcomeKey abstractState

stateContractOperation :: (StateContractTransition a1 a2 a3) -> a1
stateContractOperation s =
  case s of {
   MkStateContractTransition stateContractOperation0 _ _ _ ->
    stateContractOperation0}

stateContractFrom :: (StateContractTransition a1 a2 a3) -> a2
stateContractFrom s =
  case s of {
   MkStateContractTransition _ stateContractFrom0 _ _ -> stateContractFrom0}

stateContractOutcome :: (StateContractTransition a1 a2 a3) -> a3
stateContractOutcome s =
  case s of {
   MkStateContractTransition _ _ stateContractOutcome0 _ ->
    stateContractOutcome0}

stateContractTo :: (StateContractTransition a1 a2 a3) -> a2
stateContractTo s =
  case s of {
   MkStateContractTransition _ _ _ stateContractTo0 -> stateContractTo0}

memberByb :: (a1 -> a1 -> Prelude.Bool) -> a1 -> ([] a1) -> Prelude.Bool
memberByb equal target values =
  case values of {
   [] -> Prelude.False;
   (:) value rest ->
    case equal target value of {
     Prelude.True -> Prelude.True;
     Prelude.False -> memberByb equal target rest}}

anyFiniteb :: (a1 -> Prelude.Bool) -> ([] a1) -> Prelude.Bool
anyFiniteb predicate values =
  case values of {
   [] -> Prelude.False;
   (:) value rest -> orb (predicate value) (anyFiniteb predicate rest)}

sameInitialDomainb :: (a1 -> a1 -> Prelude.Bool) -> ([] a1) -> ([]
                      ((,) a1 a2)) -> Prelude.Bool
sameInitialDomainb eqImplementationState visibleInitial initialCorrespondence =
  case visibleInitial of {
   [] ->
    case initialCorrespondence of {
     [] -> Prelude.True;
     (:) _ _ -> Prelude.False};
   (:) visible visibleRest ->
    case initialCorrespondence of {
     [] -> Prelude.False;
     (:) p correspondenceRest ->
      case p of {
       (,) implementationState _ ->
        andb (eqImplementationState visible implementationState)
          (sameInitialDomainb eqImplementationState visibleRest
            correspondenceRest)}}}

statePairEqualb :: (a1 -> a1 -> Prelude.Bool) -> (a2 -> a2 -> Prelude.Bool)
                   -> (StatePair a1 a2) -> (StatePair a1 a2) -> Prelude.Bool
statePairEqualb eqImplementationState eqAbstractState first second =
  andb
    (eqImplementationState (statePairImplementation first)
      (statePairImplementation second))
    (eqAbstractState (statePairAbstract first) (statePairAbstract second))

decideInitialPair :: (a1 -> a1 -> Prelude.Bool) -> (a2 -> a2 -> Prelude.Bool)
                     -> ([] a2) -> ([] (StatePair a1 a2)) -> ((,) a1 
                     a2) -> Prelude.Bool
decideInitialPair eqImplementationState eqAbstractState admissibleInitial relatedPairs entry =
  let {implementationState = fst entry} in
  let {abstractState = snd entry} in
  andb (memberByb eqAbstractState abstractState admissibleInitial)
    (memberByb (statePairEqualb eqImplementationState eqAbstractState)
      (MkStatePair implementationState abstractState) relatedPairs)

relatedAbstractStates :: (a1 -> a1 -> Prelude.Bool) -> a1 -> ([]
                         (StatePair a1 a2)) -> [] a2
relatedAbstractStates eqImplementationState implementationState relatedPairs =
  case relatedPairs of {
   [] -> [];
   (:) statePair rest ->
    case eqImplementationState implementationState
           (statePairImplementation statePair) of {
     Prelude.True -> (:) (statePairAbstract statePair)
      (relatedAbstractStates eqImplementationState implementationState rest);
     Prelude.False ->
      relatedAbstractStates eqImplementationState implementationState rest}}

contractTransitionSimulates :: (a1 -> a1 -> Prelude.Bool) -> (a3 -> a3 ->
                               Prelude.Bool) -> (a4 -> a4 -> Prelude.Bool) ->
                               (a2 -> a2 -> Prelude.Bool) -> ([]
                               (StatePair a2 a3)) ->
                               (StateImplementationTransition a1 a2 a4) -> a4
                               -> a3 -> (StateContractTransition a1 a3 
                               a4) -> Prelude.Bool
contractTransitionSimulates eqOperation eqAbstractState eqOutcome eqImplementationState relatedPairs implementationTransition contractOutcome abstractPre contractTransition =
  andb
    (eqOperation (stateContractOperation contractTransition)
      (stateImplementationOperation implementationTransition))
    (andb
      (eqAbstractState (stateContractFrom contractTransition) abstractPre)
      (andb
        (eqOutcome (stateContractOutcome contractTransition) contractOutcome)
        (memberByb (statePairEqualb eqImplementationState eqAbstractState)
          (MkStatePair (stateImplementationTo implementationTransition)
          (stateContractTo contractTransition)) relatedPairs)))

decideRelatedPrestate :: (a1 -> a1 -> Prelude.Bool) -> (a3 -> a3 ->
                         Prelude.Bool) -> (a4 -> a4 -> Prelude.Bool) -> (a2
                         -> a2 -> Prelude.Bool) -> ([] (StatePair a2 a3)) ->
                         ([] (StateContractTransition a1 a3 a4)) ->
                         (StateImplementationTransition a1 a2 a4) -> a4 -> a3
                         -> Prelude.Bool
decideRelatedPrestate eqOperation eqAbstractState eqOutcome eqImplementationState relatedPairs contractTransitions implementationTransition contractOutcome abstractPre =
  anyFiniteb
    (contractTransitionSimulates eqOperation eqAbstractState eqOutcome
      eqImplementationState relatedPairs implementationTransition
      contractOutcome abstractPre)
    contractTransitions

decideStateTransition :: (a1 -> a1 -> Prelude.Bool) -> (a2 -> a2 ->
                         Prelude.Bool) -> (a3 -> a3 -> Prelude.Bool) -> (a4
                         -> a4 -> Prelude.Bool) -> ([]
                         ((,) a1 ([] ((,) a4 a4)))) -> ([] (StatePair a2 a3))
                         -> ([] (StateContractTransition a1 a3 a4)) ->
                         (StateImplementationTransition a1 a2 a4) ->
                         Prelude.Bool
decideStateTransition eqOperation eqImplementationState eqAbstractState eqOutcome qualifiedOutcomes relatedPairs contractTransitions transition =
  case lookupAssoc eqOperation (stateImplementationOperation transition)
         qualifiedOutcomes of {
   Prelude.Just outcomeMap ->
    case lookupAssoc eqOutcome (stateImplementationOutcome transition)
           outcomeMap of {
     Prelude.Just contractOutcome ->
      case relatedAbstractStates eqImplementationState
             (stateImplementationFrom transition) relatedPairs of {
       [] -> Prelude.False;
       (:) a l ->
        allFiniteb
          (decideRelatedPrestate eqOperation eqAbstractState eqOutcome
            eqImplementationState relatedPairs contractTransitions transition
            contractOutcome)
          ((:) a l)};
     Prelude.Nothing -> Prelude.False};
   Prelude.Nothing -> Prelude.False}

decideProviderStateSimulation :: (a1 -> a1 -> Prelude.Bool) -> (a2 -> a2 ->
                                 Prelude.Bool) -> (a3 -> a3 -> Prelude.Bool)
                                 -> (a4 -> a4 -> Prelude.Bool) -> ([] 
                                 a2) -> ([] a3) -> ([] ((,) a2 a3)) -> ([]
                                 ((,) a1 ([] ((,) a4 a4)))) -> ([]
                                 (StatePair a2 a3)) -> ([]
                                 (StateImplementationTransition a1 a2 a4)) ->
                                 ([] (StateContractTransition a1 a3 a4)) ->
                                 Prelude.Bool
decideProviderStateSimulation eqOperation eqImplementationState eqAbstractState eqOutcome visibleInitial admissibleInitial initialCorrespondence qualifiedOutcomes relatedPairs implementationTransitions contractTransitions =
  andb
    (sameInitialDomainb eqImplementationState visibleInitial
      initialCorrespondence)
    (andb
      (allFiniteb
        (decideInitialPair eqImplementationState eqAbstractState
          admissibleInitial relatedPairs)
        initialCorrespondence)
      (allFiniteb
        (decideStateTransition eqOperation eqImplementationState
          eqAbstractState eqOutcome qualifiedOutcomes relatedPairs
          contractTransitions)
        implementationTransitions))

