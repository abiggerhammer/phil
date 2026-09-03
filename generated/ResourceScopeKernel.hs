module ResourceScopeKernel where

import qualified Prelude

data ScopedBoundaryDecision =
   ScopedBoundaryAcceptedDecision
 | ScopedBoundaryResourceJoinDecision
 | ScopedBoundaryLexicalLoanDecision

decideScopedBoundaryByFacts :: Prelude.Bool -> Prelude.Bool ->
                               ScopedBoundaryDecision
decideScopedBoundaryByFacts resourceProjectionAccepted lexicalLoansClosed =
  case resourceProjectionAccepted of {
   Prelude.True ->
    case lexicalLoansClosed of {
     Prelude.True -> ScopedBoundaryAcceptedDecision;
     Prelude.False -> ScopedBoundaryLexicalLoanDecision};
   Prelude.False -> ScopedBoundaryResourceJoinDecision}

data AffineProjectionDecision =
   AffineProjectionAcceptedDecision
 | AffineProjectionExplicitCarrierDecision

decideAffineProjectionByFact :: Prelude.Bool -> AffineProjectionDecision
decideAffineProjectionByFact explicitCarrier =
  case explicitCarrier of {
   Prelude.True -> AffineProjectionAcceptedDecision;
   Prelude.False -> AffineProjectionExplicitCarrierDecision}

data BranchDispositionDecision =
   BranchDispositionAcceptedDecision
 | BranchDispositionTerminalExclusionDecision
 | BranchDispositionContinuingExactDecision

decideBranchDispositionByFacts :: Prelude.Bool -> Prelude.Bool ->
                                  BranchDispositionDecision
decideBranchDispositionByFacts terminalExcluded continuingExact =
  case terminalExcluded of {
   Prelude.True ->
    case continuingExact of {
     Prelude.True -> BranchDispositionAcceptedDecision;
     Prelude.False -> BranchDispositionContinuingExactDecision};
   Prelude.False -> BranchDispositionTerminalExclusionDecision}

