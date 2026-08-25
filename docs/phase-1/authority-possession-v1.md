# Phase 1 authority possession substrate v1

This slice begins implementation of `PHIL-AUTH-POSSESS-001` and covers the initial authority conformance cases `AUTH-001`, `AUTH-002`, and `AUTH-005`.

The governing rule is simple:

> Authority exercise in pure Phil requires an actually possessed authority-bearing semantic value.

A declaration name, effect permission, runtime handle, backend symbol, ambient registry entry, pointer, file descriptor, or other realization artifact is not semantic authority.

## Exact possession

`AuthorityCapability` records one exact possessed capability occurrence with:

- a stable `CapabilityOccurrenceKey`;
- an exact `AuthorityContractKey`;
- an exact semantic `AuthoritySubjectKey`;
- ordinary Phil structural `Mode`; and
- the exact set of `AuthorityOperationKey`s that possession permits.

`AuthorityRequirement` identifies the exact contract, subject, and operation demanded by one authority-bearing action.

`checkAuthorityExercise` succeeds only when the source is `PossessedCapability occurrence`, that occurrence is currently present in `AuthorityState`, and its contract, subject, and operation match the requirement.

The check deliberately does not consume or mutate the capability. ADR-014 keeps three questions separate:

1. what authority does possession permit?;
2. may the authority-bearing value itself be copied or dropped?; and
3. does this particular operation borrow, preserve, transform, or consume the capability?

This slice implements the first two. Operation-specific resource transitions remain a later layer.

## Structural discipline

Authority-bearing values use ordinary Phil structural modes; there is no authority-specific mode.

- unrestricted capability possession may be copied or dropped;
- affine capability possession may be dropped but not copied; and
- linear capability possession may be neither copied nor silently dropped.

`copyAuthorityCapability` copies only unrestricted possession and preserves the exact contract, subject, and operation set in a fresh occurrence.

`dropAuthorityCapability` permits weakening only for unrestricted and affine capabilities.

A linear capability is not automatically one-shot authority. A non-consuming operation may use the unique capability repeatedly while the same unique owner remains available. Genuine one-shot authority requires an explicit consuming operation/resource transition rather than overloading linearity or affinity.

## Non-possession sources

`AuthorityExerciseSource` explicitly models several tempting but invalid substitutes for possession:

- `ImportedAuthorityDeclaration`;
- `EffectPermissionOnly`;
- `RuntimeAuthorityHandle`;
- `BackendAuthoritySymbol`; and
- `AmbientAuthorityRegistryEntry`.

All fail with `AuthoritySourceIsNotPossession` even if their spelling or runtime representation happens to correspond to the desired operation.

This is the executable bridge from Phase 1 import noninterference to ADR-014: import can make a declaration name available, but it cannot create runtime authority.

## Conformance coverage

The dedicated harness covers:

- `AUTH-001`: exact possessed authority succeeds;
- missing occurrence rejection;
- wrong contract rejection;
- wrong semantic subject rejection;
- undeclared operation rejection;
- `AUTH-002`: unrestricted copy, restricted-copy rejection, affine drop, and linear-drop rejection;
- `AUTH-005`: import, effect permission, runtime handle, backend symbol, and ambient registry sources all fail to grant authority; and
- runtime-identity coincidence cannot repair a semantic-subject mismatch.

## Deferred

This slice does **not** yet claim:

- explicit attenuation or non-widening (`AUTH-003` / `PHIL-AUTH-ATTEN-001`);
- closure/provider confinement or negative reachable-authority analysis (`AUTH-004`);
- foreign ambient-authority policy (`AUTH-006`);
- mint/delegation non-forgeability beyond the possession state boundary;
- operation-specific borrow/consume/successor transitions;
- provider-wide authority qualification;
- final capability syntax; or
- Rocq proof for `PHIL-AUTH-POSSESS-001`.
