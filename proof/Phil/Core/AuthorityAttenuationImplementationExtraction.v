From Corelib Require Extraction.
From Phil.Core Require Import AuthorityAttenuationImplementation.

Extraction Language Haskell.

Extraction "AuthorityAttenuationKernel"
  decideExplicitAuthorityAttenuation
  decideAuthorityBoundary
  decideAuthorityJoin.
