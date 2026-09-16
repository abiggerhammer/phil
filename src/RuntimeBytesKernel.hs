module RuntimeBytesKernel where

import qualified Prelude

data BytesCheckDecision =
   BytesCheckAcceptedForgetting
 | BytesCheckAcceptedDefinitionallyEqual
 | BytesCheckRequiresExplicitTransport
 | BytesCheckIncompatible

decideBytesCheckByFacts :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool ->
                           BytesCheckDecision
decideBytesCheckByFacts lengthForgetting definitionallyEqual sameBytesFamily =
  case lengthForgetting of {
   Prelude.True -> BytesCheckAcceptedForgetting;
   Prelude.False ->
    case definitionallyEqual of {
     Prelude.True -> BytesCheckAcceptedDefinitionallyEqual;
     Prelude.False ->
      case sameBytesFamily of {
       Prelude.True -> BytesCheckRequiresExplicitTransport;
       Prelude.False -> BytesCheckIncompatible}}}

data RuntimeBytesRefinementDecision =
   RuntimeBytesRefinementAccepted
 | RuntimeBytesRefinementSourceNotRuntime
 | RuntimeBytesRefinementTargetNotExact
 | RuntimeBytesRefinementSubjectNotVisible
 | RuntimeBytesRefinementEvidenceRequired

decideRuntimeBytesRefinementByFacts :: Prelude.Bool -> Prelude.Bool ->
                                       Prelude.Bool -> Prelude.Bool ->
                                       RuntimeBytesRefinementDecision
decideRuntimeBytesRefinementByFacts sourceIsRuntime targetIsExact subjectVisible lengthEvidenceAccepted =
  case sourceIsRuntime of {
   Prelude.True ->
    case targetIsExact of {
     Prelude.True ->
      case subjectVisible of {
       Prelude.True ->
        case lengthEvidenceAccepted of {
         Prelude.True -> RuntimeBytesRefinementAccepted;
         Prelude.False -> RuntimeBytesRefinementEvidenceRequired};
       Prelude.False -> RuntimeBytesRefinementSubjectNotVisible};
     Prelude.False -> RuntimeBytesRefinementTargetNotExact};
   Prelude.False -> RuntimeBytesRefinementSourceNotRuntime}

