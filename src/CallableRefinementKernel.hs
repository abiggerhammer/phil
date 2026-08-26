module CallableRefinementKernel where

import qualified Prelude

type BoolVector = [] Prelude.Bool

vectorSubsetb :: BoolVector -> BoolVector -> Prelude.Bool
vectorSubsetb actual expected =
  case actual of {
   [] -> Prelude.True;
   (:) b actualTail ->
    case b of {
     Prelude.True ->
      case expected of {
       [] -> Prelude.False;
       (:) b0 expectedTail ->
        case b0 of {
         Prelude.True -> vectorSubsetb actualTail expectedTail;
         Prelude.False -> Prelude.False}};
     Prelude.False ->
      case expected of {
       [] -> vectorSubsetb actualTail [];
       (:) _ expectedTail -> vectorSubsetb actualTail expectedTail}}}

data RefinementDecision =
   RefinementAccepted
 | RefinementMachineShapeMismatch
 | RefinementAuthorityTooStrong
 | RefinementEffectsTooWide
 | RefinementFailuresTooWide
 | RefinementTransitionMismatch

data RefinementProjection =
   MkRefinementProjection Prelude.Bool BoolVector BoolVector BoolVector 
 BoolVector BoolVector BoolVector Prelude.Bool

projectionMachineShapeEqual :: RefinementProjection -> Prelude.Bool
projectionMachineShapeEqual r =
  case r of {
   MkRefinementProjection projectionMachineShapeEqual0 _ _ _ _ _ _ _ ->
    projectionMachineShapeEqual0}

projectionActualAuthority :: RefinementProjection -> BoolVector
projectionActualAuthority r =
  case r of {
   MkRefinementProjection _ projectionActualAuthority0 _ _ _ _ _ _ ->
    projectionActualAuthority0}

projectionExpectedAuthority :: RefinementProjection -> BoolVector
projectionExpectedAuthority r =
  case r of {
   MkRefinementProjection _ _ projectionExpectedAuthority0 _ _ _ _ _ ->
    projectionExpectedAuthority0}

projectionActualEffects :: RefinementProjection -> BoolVector
projectionActualEffects r =
  case r of {
   MkRefinementProjection _ _ _ projectionActualEffects0 _ _ _ _ ->
    projectionActualEffects0}

projectionExpectedEffects :: RefinementProjection -> BoolVector
projectionExpectedEffects r =
  case r of {
   MkRefinementProjection _ _ _ _ projectionExpectedEffects0 _ _ _ ->
    projectionExpectedEffects0}

projectionActualFailures :: RefinementProjection -> BoolVector
projectionActualFailures r =
  case r of {
   MkRefinementProjection _ _ _ _ _ projectionActualFailures0 _ _ ->
    projectionActualFailures0}

projectionExpectedFailures :: RefinementProjection -> BoolVector
projectionExpectedFailures r =
  case r of {
   MkRefinementProjection _ _ _ _ _ _ projectionExpectedFailures0 _ ->
    projectionExpectedFailures0}

projectionTransitionEqual :: RefinementProjection -> Prelude.Bool
projectionTransitionEqual r =
  case r of {
   MkRefinementProjection _ _ _ _ _ _ _ projectionTransitionEqual0 ->
    projectionTransitionEqual0}

decideCallableRefinement :: RefinementProjection -> RefinementDecision
decideCallableRefinement projection =
  case projectionMachineShapeEqual projection of {
   Prelude.True ->
    case vectorSubsetb (projectionActualAuthority projection)
           (projectionExpectedAuthority projection) of {
     Prelude.True ->
      case vectorSubsetb (projectionActualEffects projection)
             (projectionExpectedEffects projection) of {
       Prelude.True ->
        case vectorSubsetb (projectionActualFailures projection)
               (projectionExpectedFailures projection) of {
         Prelude.True ->
          case projectionTransitionEqual projection of {
           Prelude.True -> RefinementAccepted;
           Prelude.False -> RefinementTransitionMismatch};
         Prelude.False -> RefinementFailuresTooWide};
       Prelude.False -> RefinementEffectsTooWide};
     Prelude.False -> RefinementAuthorityTooStrong};
   Prelude.False -> RefinementMachineShapeMismatch}

incidenceVector :: ([] a1) -> (a1 -> Prelude.Bool) -> BoolVector
incidenceVector domain member =
  case domain of {
   [] -> [];
   (:) element rest -> (:) (member element) (incidenceVector rest member)}

