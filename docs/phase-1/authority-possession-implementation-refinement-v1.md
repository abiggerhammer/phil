# Authority possession implementation refinement v1

This staging tranche begins `PHIL-AUTH-POSSESS-IMPL-001`, mechanically connecting the existing production AUTH-001/AUTH-002/AUTH-005 checker to the already-Certified `PHIL-AUTH-POSSESS-001` semantics without changing production behavior yet.

## Extracted semantic seam

`proof/Phil/Core/AuthorityPossessionImplementation.v` defines an executable decision over the primitive facts production already computes after resolving a concrete capability occurrence:

- the exercise source is actual semantic possession;
- capability contract equals the exact required contract;
- capability subject equals the exact required subject; and
- the exact required operation is permitted.

The decision preserves the existing semantic rejection precedence: non-possession, contract mismatch, subject mismatch, operation denial, then acceptance. A correspondence theorem proves acceptance iff Certified `authorityExerciseAllowed` accepts.

The same layer extracts copy/drop decisions directly from the Certified structural-mode predicates `capabilityCopyAllowed` and `capabilityDropAllowed`.

## Explicit representation boundary

This tranche deliberately leaves these facts native:

- `CapabilityOccurrenceKey` / `Text` identity;
- `Data.Map.Strict` lookup and freshness;
- `Data.Set` operation membership;
- the concrete native `Mode` to extracted `Mode` constructor bridge; and
- exact diagnostic payload reconstruction and accepted state mutation.

Occurrence lookup failure remains a fail-closed gate before the Certified semantic decision; a missing occurrence is not modeled as possessed authority.

## Validation

The dedicated workflow recompiles `GenericStructural.v`, Certified `AuthorityPossession.v`, and the new correspondence proof under Rocq 9.2.0, fresh-extracts `AuthorityPossessionKernel.hs`, typechecks it with GHC 9.6.7, typechecks unchanged `Phil.Core.Authority`, and reruns the unchanged AUTH-001/AUTH-002/AUTH-005 correspondence corpus.

Production is unchanged in this staging tranche. On green, harvest the exact kernel and proof artifact, record `PHIL-AUTH-POSSESS-IMPL-001` as `Active / Mechanized`, then check in the exact kernel and route production exercise/copy/drop semantic decisions through it with fail-closed native Map/Set/Mode bridges.
