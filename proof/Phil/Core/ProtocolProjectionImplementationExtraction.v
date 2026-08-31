From Corelib Require Extraction.
From Phil.Core Require Import ProtocolProjectionImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "ProtocolProjectionKernel"
  decideDeclaredProjectionRoleByFact
  decideProjectionInstanceByFact
  decideProjectionSessionByFact
  planProtocolProjection
  planTransferredProtocolContract.
