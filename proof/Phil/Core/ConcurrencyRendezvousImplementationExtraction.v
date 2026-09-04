From Corelib Require Extraction.
From Phil.Core Require Import ConcurrencyRendezvousImplementation.

Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "ConcurrencyRendezvousKernel.hs"
  decideRendezvousEndpointFactsByFacts
  decideRendezvousParticipantFactsByFacts
  decideRendezvousMessageCoarseFactsByFacts
  decideExactInternalRendezvousByFacts.
