module EffectPolymorphismKernel where

import qualified Prelude

data EffectSetInstantiationDecision =
   EffectSetInstantiationAccepted
 | EffectSetInstantiationParameterKeyMismatch
 | EffectSetInstantiationKindMismatch
 | EffectSetInstantiationSemanticFormMalformed
 | EffectSetInstantiationBoundExceeded

decideEffectSetInstantiation :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
                                -> Prelude.Bool ->
                                EffectSetInstantiationDecision
decideEffectSetInstantiation parameterKeyMatches kindIsEffects semanticFormCanonical subsetOfUpper =
  case parameterKeyMatches of {
   Prelude.True ->
    case kindIsEffects of {
     Prelude.True ->
      case semanticFormCanonical of {
       Prelude.True ->
        case subsetOfUpper of {
         Prelude.True -> EffectSetInstantiationAccepted;
         Prelude.False -> EffectSetInstantiationBoundExceeded};
       Prelude.False -> EffectSetInstantiationSemanticFormMalformed};
     Prelude.False -> EffectSetInstantiationKindMismatch};
   Prelude.False -> EffectSetInstantiationParameterKeyMismatch}

