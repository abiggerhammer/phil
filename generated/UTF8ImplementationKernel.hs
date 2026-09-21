module UTF8ImplementationKernel where

import qualified Prelude

data UTF8ReadDecision =
   UTF8ReadPredecessorRejected
 | UTF8ReadDecoded
 | UTF8ReadDecodeFailed
 | UTF8ReadProviderFailed

decideReadUTF8ByFacts :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool ->
                         UTF8ReadDecision
decideReadUTF8ByFacts predecessorAccepted providerSucceeded decodeSucceeded =
  case predecessorAccepted of {
   Prelude.True ->
    case providerSucceeded of {
     Prelude.True ->
      case decodeSucceeded of {
       Prelude.True -> UTF8ReadDecoded;
       Prelude.False -> UTF8ReadDecodeFailed};
     Prelude.False -> UTF8ReadProviderFailed};
   Prelude.False -> UTF8ReadPredecessorRejected}

data UTF8CompositionDecision =
   UTF8CompositionPredecessorRejected
 | UTF8CompositionAccepted

decideWriteUTF8ByFacts :: Prelude.Bool -> UTF8CompositionDecision
decideWriteUTF8ByFacts predecessorAccepted =
  case predecessorAccepted of {
   Prelude.True -> UTF8CompositionAccepted;
   Prelude.False -> UTF8CompositionPredecessorRejected}

decideWriteLineByFacts :: Prelude.Bool -> UTF8CompositionDecision
decideWriteLineByFacts predecessorAccepted =
  case predecessorAccepted of {
   Prelude.True -> UTF8CompositionAccepted;
   Prelude.False -> UTF8CompositionPredecessorRejected}

