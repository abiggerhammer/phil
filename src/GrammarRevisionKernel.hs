module GrammarRevisionKernel where

import qualified Prelude

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

decideGrammarRevisionBindingByFacts :: Prelude.Bool -> Prelude.Bool ->
                                       Prelude.Bool -> Prelude.Bool
decideGrammarRevisionBindingByFacts competentPresent exactSelectedRevision payloadIndependent =
  andb competentPresent (andb exactSelectedRevision payloadIndependent)

