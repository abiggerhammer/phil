module ProviderLifecycleQualificationKernel where

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

sameKeyDomainb :: (a1 -> a1 -> Prelude.Bool) -> ([] ((,) a1 a2)) -> ([]
                  ((,) a1 a3)) -> Prelude.Bool
sameKeyDomainb eqKey first second =
  case first of {
   [] -> case second of {
          [] -> Prelude.True;
          (:) _ _ -> Prelude.False};
   (:) p firstRest ->
    case p of {
     (,) firstKey _ ->
      case second of {
       [] -> Prelude.False;
       (:) p0 secondRest ->
        case p0 of {
         (,) secondKey _ ->
          andb (eqKey firstKey secondKey)
            (sameKeyDomainb eqKey firstRest secondRest)}}}}

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

type ProviderLifecyclePointProjection operationKey interruptionKey =
  (,) operationKey interruptionKey

type ProviderLifecycleAllowanceProjection
  observableState cleanupResidue retryDisposition =
  (,) ([] observableState) ((,) ([] cleanupResidue) ([] retryDisposition))

type ProviderLifecycleObservationProjection
  boundary observableState cleanupResidue retryDisposition =
  (,) boundary ((,) observableState ((,) cleanupResidue retryDisposition))

memberb :: (a1 -> a1 -> Prelude.Bool) -> a1 -> ([] a1) -> Prelude.Bool
memberb eqA needle values =
  case values of {
   [] -> Prelude.False;
   (:) value rest -> orb (eqA needle value) (memberb eqA needle rest)}

lifecyclePointEqualb :: (a1 -> a1 -> Prelude.Bool) -> (a2 -> a2 ->
                        Prelude.Bool) -> (ProviderLifecyclePointProjection 
                        a1 a2) -> (ProviderLifecyclePointProjection a1 
                        a2) -> Prelude.Bool
lifecyclePointEqualb eqOperation eqInterruption first second =
  andb (eqOperation (fst first) (fst second))
    (eqInterruption (snd first) (snd second))

checkProviderLifecycleObservation :: (a1 -> a1 -> Prelude.Bool) -> (a2 -> a2
                                     -> Prelude.Bool) -> (a3 -> a3 ->
                                     Prelude.Bool) -> (a4 -> a4 ->
                                     Prelude.Bool) -> a1 ->
                                     (ProviderLifecycleAllowanceProjection 
                                     a2 a3 a4) ->
                                     (ProviderLifecycleObservationProjection
                                     a1 a2 a3 a4) -> Prelude.Bool
checkProviderLifecycleObservation eqBoundary eqObservableState eqCleanupResidue eqRetryDisposition contractBoundary allowance observation =
  andb
    (andb
      (andb (eqBoundary contractBoundary (fst observation))
        (memberb eqObservableState (fst (snd observation)) (fst allowance)))
      (memberb eqCleanupResidue (fst (snd (snd observation)))
        (fst (snd allowance))))
    (memberb eqRetryDisposition (snd (snd (snd observation)))
      (snd (snd allowance)))

checkProviderLifecyclePoint :: (a1 -> a1 -> Prelude.Bool) -> (a2 -> a2 ->
                               Prelude.Bool) -> (a3 -> a3 -> Prelude.Bool) ->
                               (a4 -> a4 -> Prelude.Bool) -> (a5 -> a5 ->
                               Prelude.Bool) -> (a6 -> a6 -> Prelude.Bool) ->
                               ([] a1) -> a3 -> ([]
                               ((,) (ProviderLifecyclePointProjection a1 a2)
                               ([]
                               (ProviderLifecycleObservationProjection 
                               a3 a4 a5 a6)))) -> ((,)
                               (ProviderLifecyclePointProjection a1 a2)
                               (ProviderLifecycleAllowanceProjection 
                               a4 a5 a6)) -> Prelude.Bool
checkProviderLifecyclePoint eqOperation eqInterruption eqBoundary eqObservableState eqCleanupResidue eqRetryDisposition qualifiedOperations contractBoundary observations entry =
  let {point = fst entry} in
  let {allowance = snd entry} in
  case lookupAssoc (lifecyclePointEqualb eqOperation eqInterruption) point
         observations of {
   Prelude.Just pointObservations ->
    andb (memberb eqOperation (fst point) qualifiedOperations)
      (allFiniteb
        (checkProviderLifecycleObservation eqBoundary eqObservableState
          eqCleanupResidue eqRetryDisposition contractBoundary allowance)
        pointObservations);
   Prelude.Nothing -> Prelude.False}

decideProviderLifecycleQualification :: (a1 -> a1 -> Prelude.Bool) -> (a2 ->
                                        a2 -> Prelude.Bool) -> (a3 -> a3 ->
                                        Prelude.Bool) -> (a4 -> a4 ->
                                        Prelude.Bool) -> (a5 -> a5 ->
                                        Prelude.Bool) -> (a6 -> a6 ->
                                        Prelude.Bool) -> ([] a1) -> a3 -> ([]
                                        ((,)
                                        (ProviderLifecyclePointProjection 
                                        a1 a2)
                                        (ProviderLifecycleAllowanceProjection
                                        a4 a5 a6))) -> ([]
                                        ((,)
                                        (ProviderLifecyclePointProjection 
                                        a1 a2)
                                        ([]
                                        (ProviderLifecycleObservationProjection
                                        a3 a4 a5 a6)))) -> Prelude.Bool
decideProviderLifecycleQualification eqOperation eqInterruption eqBoundary eqObservableState eqCleanupResidue eqRetryDisposition qualifiedOperations contractBoundary allowances observations =
  andb
    (sameKeyDomainb (lifecyclePointEqualb eqOperation eqInterruption)
      allowances observations)
    (allFiniteb
      (checkProviderLifecyclePoint eqOperation eqInterruption eqBoundary
        eqObservableState eqCleanupResidue eqRetryDisposition
        qualifiedOperations contractBoundary observations)
      allowances)

