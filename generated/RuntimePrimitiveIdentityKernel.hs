module RuntimePrimitiveIdentityKernel where

import qualified Prelude

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

decideRuntimePrimitiveIdentityByFacts :: Prelude.Bool -> Prelude.Bool ->
                                         Prelude.Bool
decideRuntimePrimitiveIdentityByFacts =
  andb

