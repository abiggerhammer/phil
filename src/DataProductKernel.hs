module DataProductKernel where

import qualified Prelude

data ProductEliminationDecision =
   ProductEliminationAcceptedDecision
 | ProductEliminationArityDecision
 | ProductEliminationDuplicateSuccessorDecision

decideProductEliminationByFacts :: Prelude.Bool -> Prelude.Bool ->
                                   ProductEliminationDecision
decideProductEliminationByFacts exactArity successorsDistinct =
  case exactArity of {
   Prelude.True ->
    case successorsDistinct of {
     Prelude.True -> ProductEliminationAcceptedDecision;
     Prelude.False -> ProductEliminationDuplicateSuccessorDecision};
   Prelude.False -> ProductEliminationArityDecision}

data ProductRestorationDecision =
   ProductRestorationAcceptedDecision
 | ProductRestorationOwnerDecision
 | ProductRestorationExactnessDecision

decideProductRestorationByFacts :: Prelude.Bool -> Prelude.Bool ->
                                   ProductRestorationDecision
decideProductRestorationByFacts ownerConsumed successorsInstalledExact =
  case ownerConsumed of {
   Prelude.True ->
    case successorsInstalledExact of {
     Prelude.True -> ProductRestorationAcceptedDecision;
     Prelude.False -> ProductRestorationExactnessDecision};
   Prelude.False -> ProductRestorationOwnerDecision}

