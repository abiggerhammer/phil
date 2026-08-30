module ArchitectureImportKernel where

import qualified Prelude

data ImportResolutionDecision =
   ImportResolutionDecisionAccepted
 | UnknownSelectedExportDecision
 | DuplicateResolutionNameDecision

decideImportResolutionByFacts :: Prelude.Bool -> Prelude.Bool ->
                                 ImportResolutionDecision
decideImportResolutionByFacts selectedExportPresent localNameFresh =
  case selectedExportPresent of {
   Prelude.True ->
    case localNameFresh of {
     Prelude.True -> ImportResolutionDecisionAccepted;
     Prelude.False -> DuplicateResolutionNameDecision};
   Prelude.False -> UnknownSelectedExportDecision}

data ImportedBindingPlan localName identity =
   MkImportedBindingPlan localName identity

planImportedBinding :: a1 -> a2 -> ImportedBindingPlan a1 a2
planImportedBinding name declarationIdentity =
  MkImportedBindingPlan name declarationIdentity

