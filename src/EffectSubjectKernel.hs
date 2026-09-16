module EffectSubjectKernel where

import qualified Prelude

data EffectSubjectCorrespondenceDecision =
   EffectSubjectCorrespondenceAccepted
 | EffectSubjectCorrespondenceSourceEmpty
 | EffectSubjectCorrespondenceTargetEmpty
 | EffectSubjectCorrespondenceRevisionEmpty

decideEffectSubjectCorrespondence :: Prelude.Bool -> Prelude.Bool ->
                                     Prelude.Bool ->
                                     EffectSubjectCorrespondenceDecision
decideEffectSubjectCorrespondence sourceNonempty targetNonempty revisionNonempty =
  case sourceNonempty of {
   Prelude.True ->
    case targetNonempty of {
     Prelude.True ->
      case revisionNonempty of {
       Prelude.True -> EffectSubjectCorrespondenceAccepted;
       Prelude.False -> EffectSubjectCorrespondenceRevisionEmpty};
     Prelude.False -> EffectSubjectCorrespondenceTargetEmpty};
   Prelude.False -> EffectSubjectCorrespondenceSourceEmpty}

data EffectSubjectRetargetDecision =
   EffectSubjectRetargetAcceptedSame
 | EffectSubjectRetargetAcceptedCorrespondence
 | EffectSubjectRetargetIndexOutOfRange
 | EffectSubjectRetargetRequiresCorrespondence
 | EffectSubjectRetargetCorrespondenceSourceMismatch
 | EffectSubjectRetargetCorrespondenceTargetMismatch

decideEffectSubjectRetarget :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
                               -> Prelude.Bool -> Prelude.Bool ->
                               EffectSubjectRetargetDecision
decideEffectSubjectRetarget indexInRange sameSubject correspondencePresent correspondenceSourceMatches correspondenceTargetMatches =
  case indexInRange of {
   Prelude.True ->
    case sameSubject of {
     Prelude.True -> EffectSubjectRetargetAcceptedSame;
     Prelude.False ->
      case correspondencePresent of {
       Prelude.True ->
        case correspondenceSourceMatches of {
         Prelude.True ->
          case correspondenceTargetMatches of {
           Prelude.True -> EffectSubjectRetargetAcceptedCorrespondence;
           Prelude.False -> EffectSubjectRetargetCorrespondenceTargetMismatch};
         Prelude.False -> EffectSubjectRetargetCorrespondenceSourceMismatch};
       Prelude.False -> EffectSubjectRetargetRequiresCorrespondence}};
   Prelude.False -> EffectSubjectRetargetIndexOutOfRange}

