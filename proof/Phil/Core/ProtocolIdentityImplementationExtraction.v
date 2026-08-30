From Corelib Require Extraction.
From Phil.Core Require Import ProtocolIdentityImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "ProtocolIdentityKernel"
  decideProtocolContractByFacts
  decideProtocolActionByFacts
  planProtocolContract.
