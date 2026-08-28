module CallableScopeKernel where

import qualified Prelude

data ScopeCaptureDecision =
   ScopeCaptureAccepted
 | ScopeCaptureEscapingLoan
 | ScopeCaptureOutsideLoanValidity

decideScopeCaptureByFacts :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool ->
                             ScopeCaptureDecision
decideScopeCaptureByFacts isEscaping isScopedLoan sameScope =
  case isScopedLoan of {
   Prelude.True ->
    case isEscaping of {
     Prelude.True -> ScopeCaptureEscapingLoan;
     Prelude.False ->
      case sameScope of {
       Prelude.True -> ScopeCaptureAccepted;
       Prelude.False -> ScopeCaptureOutsideLoanValidity}};
   Prelude.False -> ScopeCaptureAccepted}

data RecursiveClosureGraphDecision =
   RecursiveClosureGraphAccepted
 | RecursiveClosureDuplicateNode
 | RecursiveClosureUnknownReference
 | RecursiveClosureRestrictedCycle

decideRecursiveClosureGraphFacts :: Prelude.Bool -> Prelude.Bool ->
                                    Prelude.Bool ->
                                    RecursiveClosureGraphDecision
decideRecursiveClosureGraphFacts uniqueNodes referencesKnownFact noRestrictedCycleFact =
  case uniqueNodes of {
   Prelude.True ->
    case referencesKnownFact of {
     Prelude.True ->
      case noRestrictedCycleFact of {
       Prelude.True -> RecursiveClosureGraphAccepted;
       Prelude.False -> RecursiveClosureRestrictedCycle};
     Prelude.False -> RecursiveClosureUnknownReference};
   Prelude.False -> RecursiveClosureDuplicateNode}

