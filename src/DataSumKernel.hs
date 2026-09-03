module DataSumKernel where

import qualified Prelude

orb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
orb b1 b2 =
  case b1 of {
   Prelude.True -> Prelude.True;
   Prelude.False -> b2}

data ConstructorSelectionDecision =
   ConstructorSelectionAcceptedDecision
 | ConstructorSelectionUnknownDecision

decideConstructorSelectionByFact :: Prelude.Bool ->
                                    ConstructorSelectionDecision
decideConstructorSelectionByFact constructorDeclared =
  case constructorDeclared of {
   Prelude.True -> ConstructorSelectionAcceptedDecision;
   Prelude.False -> ConstructorSelectionUnknownDecision}

data SelectedPayloadRestorationDecision =
   SelectedPayloadRestorationAcceptedDecision
 | SelectedPayloadAggregateDecision
 | SelectedPayloadExactnessDecision

decideSelectedPayloadRestorationByFacts :: Prelude.Bool -> Prelude.Bool ->
                                           SelectedPayloadRestorationDecision
decideSelectedPayloadRestorationByFacts aggregateConsumed payloadRestoredExact =
  case aggregateConsumed of {
   Prelude.True ->
    case payloadRestoredExact of {
     Prelude.True -> SelectedPayloadRestorationAcceptedDecision;
     Prelude.False -> SelectedPayloadExactnessDecision};
   Prelude.False -> SelectedPayloadAggregateDecision}

data ContinuingArmDecision =
   ContinuingArmAcceptedDecision
 | ContinuingArmPayloadDispositionDecision

decideContinuingArmByFact :: Prelude.Bool -> ContinuingArmDecision
decideContinuingArmByFact selectedPayloadAccounted =
  case selectedPayloadAccounted of {
   Prelude.True -> ContinuingArmAcceptedDecision;
   Prelude.False -> ContinuingArmPayloadDispositionDecision}

data BranchConvergenceDecision =
   BranchConvergenceAcceptedDecision
 | BranchConvergenceHiddenStateDecision
 | BranchConvergenceJoinDecision

decideBranchConvergenceByFacts :: Prelude.Bool -> Prelude.Bool ->
                                  Prelude.Bool -> BranchConvergenceDecision
decideBranchConvergenceByFacts rawLinearShapesCompatible explicitCommonPackage ordinaryJoinAccepted =
  case ordinaryJoinAccepted of {
   Prelude.True ->
    case orb rawLinearShapesCompatible explicitCommonPackage of {
     Prelude.True -> BranchConvergenceAcceptedDecision;
     Prelude.False -> BranchConvergenceHiddenStateDecision};
   Prelude.False -> BranchConvergenceJoinDecision}

