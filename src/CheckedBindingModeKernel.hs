module CheckedBindingModeKernel where

import qualified Prelude

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

decideCheckedBindingModeByFacts :: Prelude.Bool -> Prelude.Bool ->
                                   Prelude.Bool -> Prelude.Bool
decideCheckedBindingModeByFacts typeMatches modeMatches contextAccepts =
  andb typeMatches (andb modeMatches contextAccepts)

