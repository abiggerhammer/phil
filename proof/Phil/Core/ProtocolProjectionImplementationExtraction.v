From Phil.Core Require Import ProtocolProjectionImplementation.

Extraction Language Haskell.

Extraction "ProtocolProjectionKernel.hs"
  decideDeclaredProjectionRoleByFact
  decideProjectionInstanceByFact
  decideProjectionSessionByFact
  planProtocolProjection
  planTransferredProtocolContract.
