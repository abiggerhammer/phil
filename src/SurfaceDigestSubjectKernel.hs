module SurfaceDigestSubjectKernel where

import qualified Prelude

data SurfaceDigestSubjectDecision beginSubject stableOwner =
   SurfaceDigestSubjectAccepted beginSubject stableOwner
 | SurfaceDigestExplicitContextRejected
 | SurfaceDigestArityRejected
 | SurfaceDigestBeginNameRejected
 | SurfaceDigestBeginTypeRejected
 | SurfaceDigestPayloadBorrowRejected
 | SurfaceDigestStableOwnerRejected
 | SurfaceDigestPayloadTypeRejected

decideSurfaceDigestSubjectByFacts :: Prelude.Bool -> Prelude.Bool ->
                                     Prelude.Bool -> Prelude.Bool ->
                                     Prelude.Bool -> Prelude.Bool ->
                                     Prelude.Bool -> a1 -> a2 ->
                                     SurfaceDigestSubjectDecision a1 
                                     a2
decideSurfaceDigestSubjectByFacts noExplicitContext exactArity beginNamed beginIsBegin payloadBorrowed stableOwnerPresent payloadIsSharedBytes beginSubject stableOwner =
  case noExplicitContext of {
   Prelude.True ->
    case exactArity of {
     Prelude.True ->
      case beginNamed of {
       Prelude.True ->
        case beginIsBegin of {
         Prelude.True ->
          case payloadBorrowed of {
           Prelude.True ->
            case stableOwnerPresent of {
             Prelude.True ->
              case payloadIsSharedBytes of {
               Prelude.True -> SurfaceDigestSubjectAccepted beginSubject
                stableOwner;
               Prelude.False -> SurfaceDigestPayloadTypeRejected};
             Prelude.False -> SurfaceDigestStableOwnerRejected};
           Prelude.False -> SurfaceDigestPayloadBorrowRejected};
         Prelude.False -> SurfaceDigestBeginTypeRejected};
       Prelude.False -> SurfaceDigestBeginNameRejected};
     Prelude.False -> SurfaceDigestArityRejected};
   Prelude.False -> SurfaceDigestExplicitContextRejected}

