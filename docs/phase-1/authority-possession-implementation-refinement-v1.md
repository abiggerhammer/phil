# Authority possession implementation refinement v1

`PHIL-AUTH-POSSESS-IMPL-001` mechanically connects production AUTH-001/AUTH-002/AUTH-005 authority checking to the already-Certified `PHIL-AUTH-POSSESS-001` semantics.

## Extracted semantic seam

`proof/Phil/Core/AuthorityPossessionImplementation.v` defines an executable decision over the primitive facts production computes after resolving a concrete capability occurrence:

- the exercise source is actual semantic possession;
- capability contract equals the exact required contract;
- capability subject equals the exact required subject; and
- the exact required operation is permitted.

The decision preserves the Certified semantic rejection precedence: non-possession, contract mismatch, subject mismatch, operation denial, then acceptance. Its correspondence theorem proves acceptance iff Certified `authorityExerciseAllowed` accepts.

The same layer extracts copy/drop decisions directly from the Certified structural-mode predicates `capabilityCopyAllowed` and `capabilityDropAllowed`.

## Production binding

The exact Rocq-generated `AuthorityPossessionKernel.hs` is checked into `src/` byte-for-byte. `Phil.Core.Authority` routes final semantic decisions through it:

- `checkAuthorityExercise` resolves a concrete possessed occurrence natively, reflects exact contract/subject/operation facts into the kernel, and reconstructs the existing ordered diagnostic only when the returned kernel decision agrees with those native facts;
- non-possession sources are rejected through the kernel's source gate;
- `copyAuthorityCapability` leaves source lookup and target freshness native, but structural copy legality is decided by `decideAuthorityCopy` over the exact bridged `Mode`; and
- `dropAuthorityCapability` leaves source lookup and state deletion native, but structural drop legality is decided by `decideAuthorityDrop` over the exact bridged `Mode`.

Any impossible disagreement between the extracted decision and the native facts returns `AuthorityPossessionKernelBridgeMismatch`; handwritten bridge or diagnostic code cannot turn a kernel rejection into success.

## Explicit representation boundary

These remain native representation/runtime foundations:

- `CapabilityOccurrenceKey` / `Text` identity;
- `Data.Map.Strict` occurrence lookup and copy-target freshness;
- `Data.Set` operation membership;
- the total concrete `Mode` to extracted `Mode` constructor bridge;
- exact diagnostic payload reconstruction; and
- accepted concrete Map mutation.

Occurrence lookup failure remains a fail-closed gate before the Certified possessed-capability decision: a missing occurrence is never modeled as possessed authority.

## Validation

The dedicated workflow recompiles `GenericStructural.v`, Certified `AuthorityPossession.v`, and the executable correspondence under Rocq 9.2.0; fresh-extracts `AuthorityPossessionKernel.hs`; requires byte identity with the checked-in kernel; typechecks the generated kernel with only its generator-owned unused-Prelude warning suppressed; then typechecks the handwritten production/test path under full `-Wall -Werror` and reruns the unchanged AUTH-001/AUTH-002/AUTH-005 corpus.

The closeout artifact records SHA-256 identities for the checked-in kernel, bound production `Authority.hs`, and the production correspondence corpus. Once that exact-head workflow matrix is green, `PHIL-AUTH-POSSESS-IMPL-001` may be upgraded from `Active / Mechanized` to `Discharged / Implementation Refined`.
