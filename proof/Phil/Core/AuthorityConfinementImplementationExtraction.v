From Corelib Require Extraction.
From Phil.Core Require Import AuthorityConfinementImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "AuthorityConfinementKernel"
  ProviderAuthoritySubjectKind
  ProviderAuthorityInventoryBasisKind
  ProviderExtraAuthorityDispositionKind
  decideClosureAuthorityConfinement
  decideNegativeAuthorityClaim
  decideProviderAuthoritySubject
  decideProviderAuthorityInventoryBasis
  decideProviderExtraAuthority
  decideProviderStaticSummaries
  decideProviderExtraDisposition
  decideProviderAuthorityQualificationFacts.
