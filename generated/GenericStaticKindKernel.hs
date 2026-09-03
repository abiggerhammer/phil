module GenericStaticKindKernel where

import qualified Prelude

data DirectStaticActualDecision =
   DirectStaticActualAcceptedDecision
 | DirectStaticActualKindMismatchDecision

decideDirectStaticActualByFact :: Prelude.Bool -> DirectStaticActualDecision
decideDirectStaticActualByFact kindMatches =
  case kindMatches of {
   Prelude.True -> DirectStaticActualAcceptedDecision;
   Prelude.False -> DirectStaticActualKindMismatchDecision}

data ReferencedStaticActualDecision =
   ReferencedStaticActualAcceptedDecision
 | ReferencedStaticActualUnresolvedDecision
 | ReferencedStaticActualKindMismatchDecision
 | ReferencedStaticActualAmbiguousDecision
 | ReferencedStaticActualSemanticFormMismatchDecision

decideReferencedStaticActualByFacts :: Prelude.Bool -> Prelude.Bool ->
                                       Prelude.Bool -> Prelude.Bool ->
                                       ReferencedStaticActualDecision
decideReferencedStaticActualByFacts nameExists expectedKindPresent expectedKindUnique selectedSemanticFormExact =
  case nameExists of {
   Prelude.True ->
    case expectedKindPresent of {
     Prelude.True ->
      case expectedKindUnique of {
       Prelude.True ->
        case selectedSemanticFormExact of {
         Prelude.True -> ReferencedStaticActualAcceptedDecision;
         Prelude.False -> ReferencedStaticActualSemanticFormMismatchDecision};
       Prelude.False -> ReferencedStaticActualAmbiguousDecision};
     Prelude.False -> ReferencedStaticActualKindMismatchDecision};
   Prelude.False -> ReferencedStaticActualUnresolvedDecision}

data CheckedStaticActualShapeDecision =
   CheckedStaticActualShapeAcceptedDecision
 | CheckedStaticActualParameterKeyDecision
 | CheckedStaticActualKindDecision

decideCheckedStaticActualShapeByFacts :: Prelude.Bool -> Prelude.Bool ->
                                         CheckedStaticActualShapeDecision
decideCheckedStaticActualShapeByFacts parameterKeyExact kindExact =
  case parameterKeyExact of {
   Prelude.True ->
    case kindExact of {
     Prelude.True -> CheckedStaticActualShapeAcceptedDecision;
     Prelude.False -> CheckedStaticActualKindDecision};
   Prelude.False -> CheckedStaticActualParameterKeyDecision}

