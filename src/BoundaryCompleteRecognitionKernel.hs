module BoundaryCompleteRecognitionKernel where

import qualified Prelude

data ExtentCheck =
   ExtentInvalid
 | ExtentTrailing
 | ExtentPast
 | ExtentComplete

decideCompleteExtentByFacts :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
                               -> Prelude.Bool -> ExtentCheck
decideCompleteExtentByFacts declaredNegative consumedNegative consumedBeforeDeclared declaredBeforeConsumed =
  case declaredNegative of {
   Prelude.True -> ExtentInvalid;
   Prelude.False ->
    case consumedNegative of {
     Prelude.True -> ExtentInvalid;
     Prelude.False ->
      case consumedBeforeDeclared of {
       Prelude.True -> ExtentTrailing;
       Prelude.False ->
        case declaredBeforeConsumed of {
         Prelude.True -> ExtentPast;
         Prelude.False -> ExtentComplete}}}}

