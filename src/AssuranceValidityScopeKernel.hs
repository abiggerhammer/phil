module AssuranceValidityScopeKernel where

import qualified Prelude

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

validityScopeFactsb :: ([] Prelude.Bool) -> Prelude.Bool
validityScopeFactsb facts =
  case facts of {
   [] -> Prelude.True;
   (:) fact rest -> andb fact (validityScopeFactsb rest)}

data ValidityScopeDecision =
   ValidityScopeAccepted
 | ValidityScopeRejected

decideValidityScope :: ([] Prelude.Bool) -> ValidityScopeDecision
decideValidityScope facts =
  case validityScopeFactsb facts of {
   Prelude.True -> ValidityScopeAccepted;
   Prelude.False -> ValidityScopeRejected}

