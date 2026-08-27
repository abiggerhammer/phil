module ProviderLawQualificationKernel where

import qualified Prelude

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

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

type ProviderLawImplementationEvent operationKey outcomeKey =
  (,) operationKey outcomeKey

type ProviderLawPublicEvent operationKey outcomeKey =
  (,) operationKey outcomeKey

type ProviderLawTransitionKey lawState operationKey outcomeKey =
  (,) lawState (ProviderLawPublicEvent operationKey outcomeKey)

publicEventEqualb :: (a1 -> a1 -> Prelude.Bool) -> (a2 -> a2 -> Prelude.Bool)
                     -> (ProviderLawPublicEvent a1 a2) ->
                     (ProviderLawPublicEvent a1 a2) -> Prelude.Bool
publicEventEqualb eqOperation eqOutcome first second =
  andb (eqOperation (fst first) (fst second))
    (eqOutcome (snd first) (snd second))

lawTransitionKeyEqualb :: (a1 -> a1 -> Prelude.Bool) -> (a2 -> a2 ->
                          Prelude.Bool) -> (a3 -> a3 -> Prelude.Bool) ->
                          (ProviderLawTransitionKey a1 a2 a3) ->
                          (ProviderLawTransitionKey a1 a2 a3) -> Prelude.Bool
lawTransitionKeyEqualb eqLawState eqOperation eqOutcome first second =
  andb (eqLawState (fst first) (fst second))
    (publicEventEqualb eqOperation eqOutcome (snd first) (snd second))

translateProviderLawEvent :: (a1 -> a1 -> Prelude.Bool) -> (a2 -> a2 ->
                             Prelude.Bool) -> ([] ((,) a1 ([] ((,) a2 a2))))
                             -> (ProviderLawImplementationEvent a1 a2) ->
                             Prelude.Maybe (ProviderLawPublicEvent a1 a2)
translateProviderLawEvent eqOperation eqOutcome qualifiedOutcomes event =
  case lookupAssoc eqOperation (fst event) qualifiedOutcomes of {
   Prelude.Just outcomeMap ->
    case lookupAssoc eqOutcome (snd event) outcomeMap of {
     Prelude.Just publicOutcome -> Prelude.Just ((,) (fst event)
      publicOutcome);
     Prelude.Nothing -> Prelude.Nothing};
   Prelude.Nothing -> Prelude.Nothing}

translateProviderLawTrace :: (a1 -> a1 -> Prelude.Bool) -> (a2 -> a2 ->
                             Prelude.Bool) -> ([] ((,) a1 ([] ((,) a2 a2))))
                             -> ([] (ProviderLawImplementationEvent a1 a2))
                             -> Prelude.Maybe
                             ([] (ProviderLawPublicEvent a1 a2))
translateProviderLawTrace eqOperation eqOutcome qualifiedOutcomes trace =
  case trace of {
   [] -> Prelude.Just [];
   (:) event rest ->
    case translateProviderLawEvent eqOperation eqOutcome qualifiedOutcomes
           event of {
     Prelude.Just publicEvent ->
      case translateProviderLawTrace eqOperation eqOutcome qualifiedOutcomes
             rest of {
       Prelude.Just publicRest -> Prelude.Just ((:) publicEvent publicRest);
       Prelude.Nothing -> Prelude.Nothing};
     Prelude.Nothing -> Prelude.Nothing}}

runProviderLawKernel :: (a1 -> a1 -> Prelude.Bool) -> (a2 -> a2 ->
                        Prelude.Bool) -> (a3 -> a3 -> Prelude.Bool) -> ([]
                        ((,) (ProviderLawTransitionKey a1 a2 a3) a1)) -> a1
                        -> ([] (ProviderLawPublicEvent a2 a3)) ->
                        Prelude.Maybe a1
runProviderLawKernel eqLawState eqOperation eqOutcome transitions state trace =
  case trace of {
   [] -> Prelude.Just state;
   (:) event rest ->
    case lookupAssoc
           (lawTransitionKeyEqualb eqLawState eqOperation eqOutcome) ((,)
           state event) transitions of {
     Prelude.Just nextState ->
      runProviderLawKernel eqLawState eqOperation eqOutcome transitions
        nextState rest;
     Prelude.Nothing -> Prelude.Nothing}}

decideProviderLawTrace :: (a1 -> a1 -> Prelude.Bool) -> (a2 -> a2 ->
                          Prelude.Bool) -> (a3 -> a3 -> Prelude.Bool) -> ([]
                          ((,) a2 ([] ((,) a3 a3)))) -> ([]
                          ((,) (ProviderLawTransitionKey a1 a2 a3) a1)) -> a1
                          -> ([] (ProviderLawImplementationEvent a2 a3)) ->
                          Prelude.Bool
decideProviderLawTrace eqLawState eqOperation eqOutcome qualifiedOutcomes transitions initialState implementationTrace =
  case translateProviderLawTrace eqOperation eqOutcome qualifiedOutcomes
         implementationTrace of {
   Prelude.Just publicTrace ->
    case runProviderLawKernel eqLawState eqOperation eqOutcome transitions
           initialState publicTrace of {
     Prelude.Just _ -> Prelude.True;
     Prelude.Nothing -> Prelude.False};
   Prelude.Nothing -> Prelude.False}

