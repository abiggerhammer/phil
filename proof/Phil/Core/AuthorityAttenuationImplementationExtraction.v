From Corelib Require Extraction.
From Phil.Core Require Import AuthorityAttenuationImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "AuthorityAttenuationKernel"
  decideExplicitAuthorityAttenuation
  decideAuthorityBoundary
  decideAuthorityJoin.
