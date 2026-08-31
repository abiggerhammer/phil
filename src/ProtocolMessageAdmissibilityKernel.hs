module ProtocolMessageAdmissibilityKernel where

import qualified Prelude

data BoundaryMessageContractDecision =
   BoundaryMessageContractAcceptedDecision
 | BoundaryMessageRevisionEmptyDecision
 | BoundaryMessageTypeMismatchDecision
 | BoundaryMessageSemanticsMismatchDecision
 | BoundaryMessageShapeRejectedDecision
 | BoundaryMessageHardTypeRejectedDecision

decideBoundaryMessageContractByFacts :: Prelude.Bool -> Prelude.Bool ->
                                        Prelude.Bool -> Prelude.Bool ->
                                        Prelude.Bool ->
                                        BoundaryMessageContractDecision
decideBoundaryMessageContractByFacts revisionNonempty typeMatches semanticsMatches shapeAllows hardTypeAllows =
  case revisionNonempty of {
   Prelude.True ->
    case typeMatches of {
     Prelude.True ->
      case semanticsMatches of {
       Prelude.True ->
        case shapeAllows of {
         Prelude.True ->
          case hardTypeAllows of {
           Prelude.True -> BoundaryMessageContractAcceptedDecision;
           Prelude.False -> BoundaryMessageHardTypeRejectedDecision};
         Prelude.False -> BoundaryMessageShapeRejectedDecision};
       Prelude.False -> BoundaryMessageSemanticsMismatchDecision};
     Prelude.False -> BoundaryMessageTypeMismatchDecision};
   Prelude.False -> BoundaryMessageRevisionEmptyDecision}

data IntrinsicBoundaryMessageDecision =
   IntrinsicBoundaryMessageAcceptedDecision
 | IntrinsicBoundaryMessageRequiresContractDecision

decideIntrinsicBoundaryMessageByFact :: Prelude.Bool ->
                                        IntrinsicBoundaryMessageDecision
decideIntrinsicBoundaryMessageByFact intrinsicAllows =
  case intrinsicAllows of {
   Prelude.True -> IntrinsicBoundaryMessageAcceptedDecision;
   Prelude.False -> IntrinsicBoundaryMessageRequiresContractDecision}
