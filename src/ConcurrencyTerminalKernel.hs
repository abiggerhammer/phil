module ConcurrencyTerminalKernel where

import qualified Prelude

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

decideCertifiedProcessTerminalByFacts :: Prelude.Bool -> Prelude.Bool ->
                                         Prelude.Bool -> Prelude.Bool ->
                                         Prelude.Bool
decideCertifiedProcessTerminalByFacts resourceClosed obligationsClosed endpointsClosed controlTerminal =
  andb resourceClosed
    (andb obligationsClosed (andb endpointsClosed controlTerminal))

decideExactFailureIsolationByFacts :: Prelude.Bool -> Prelude.Bool ->
                                      Prelude.Bool -> Prelude.Bool
decideExactFailureIsolationByFacts actorWasRunning actorBecomesFailed peersUnchanged =
  andb actorWasRunning (andb actorBecomesFailed peersUnchanged)

decideCertifiedRootTerminalByFacts :: Prelude.Bool -> Prelude.Bool ->
                                      Prelude.Bool -> Prelude.Bool ->
                                      Prelude.Bool -> Prelude.Bool ->
                                      Prelude.Bool
decideCertifiedRootTerminalByFacts rootResources rootObligations rootObservables terminalFactsComplete noInventedTerminalFacts allStaticStatusesTerminated =
  andb rootResources
    (andb rootObligations
      (andb rootObservables
        (andb terminalFactsComplete
          (andb noInventedTerminalFacts allStaticStatusesTerminated))))

decideCertifiedNetworkStuckByFacts :: Prelude.Bool -> Prelude.Bool ->
                                      Prelude.Bool -> Prelude.Bool
decideCertifiedNetworkStuckByFacts rootNotTerminal runningStaticProcess noEnabledSemanticStep =
  andb rootNotTerminal (andb runningStaticProcess noEnabledSemanticStep)

