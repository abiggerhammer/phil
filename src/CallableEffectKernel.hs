module CallableEffectKernel where

import qualified Prelude

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

negb :: Prelude.Bool -> Prelude.Bool
negb b =
  case b of {
   Prelude.True -> Prelude.False;
   Prelude.False -> Prelude.True}

data CallableUseEffectKind =
   PossessEffectUse
 | PassEffectUse
 | StoreEffectUse
 | ReturnEffectUse
 | InvokeEffectUse

callableUseEffectKindContributesPublicBound :: CallableUseEffectKind ->
                                               Prelude.Bool
callableUseEffectKindContributesPublicBound kind =
  case kind of {
   InvokeEffectUse -> Prelude.True;
   _ -> Prelude.False}

data CallableEffectBoundDecision =
   CallableEffectBoundAccepted
 | CallableEffectBoundExceeded

decideCallableEffectBound :: Prelude.Bool -> CallableEffectBoundDecision
decideCallableEffectBound subsetFact =
  case subsetFact of {
   Prelude.True -> CallableEffectBoundAccepted;
   Prelude.False -> CallableEffectBoundExceeded}

effectDeltaBit :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
effectDeltaBit inferredPresent publicPresent =
  andb inferredPresent (negb publicPresent)
