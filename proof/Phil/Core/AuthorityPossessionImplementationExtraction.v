From Corelib Require Extraction.
From Phil.Core Require Import AuthorityPossessionImplementation.

Extraction Language Haskell.

Extraction "AuthorityPossessionKernel"
  AuthorityExerciseDecision
  decideAuthorityExerciseFacts
  AuthorityCopyDecision
  decideAuthorityCopy
  AuthorityDropDecision
  decideAuthorityDrop.
