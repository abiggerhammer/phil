From Corelib Require Extraction.
From Phil.Core Require Import ConcurrencyTerminalImplementation.

Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "ConcurrencyTerminalKernel.hs"
  decideCertifiedProcessTerminalByFacts
  decideExactFailureIsolationByFacts
  decideCertifiedRootTerminalByFacts
  decideCertifiedNetworkStuckByFacts.
