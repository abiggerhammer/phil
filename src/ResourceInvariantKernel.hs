module ResourceInvariantKernel where

import qualified Prelude

data InvariantBoundaryDecision =
   InvariantBoundaryAcceptedDecision
 | InvariantBoundaryDuplicatePredecessorDecision
 | InvariantBoundaryStructuralDecision
 | InvariantBoundaryWitnessDomainDecision
 | InvariantBoundaryEstablishmentDecision

decideInvariantBoundaryByFacts :: Prelude.Bool -> Prelude.Bool ->
                                  Prelude.Bool -> Prelude.Bool ->
                                  InvariantBoundaryDecision
decideInvariantBoundaryByFacts predecessorsDistinct structuralAccepted witnessesExact invariantEstablished =
  case predecessorsDistinct of {
   Prelude.True ->
    case structuralAccepted of {
     Prelude.True ->
      case witnessesExact of {
       Prelude.True ->
        case invariantEstablished of {
         Prelude.True -> InvariantBoundaryAcceptedDecision;
         Prelude.False -> InvariantBoundaryEstablishmentDecision};
       Prelude.False -> InvariantBoundaryWitnessDomainDecision};
     Prelude.False -> InvariantBoundaryStructuralDecision};
   Prelude.False -> InvariantBoundaryDuplicatePredecessorDecision}
