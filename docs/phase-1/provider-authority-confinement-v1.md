# Phase 1 provider authority confinement v1

This slice advances `PHIL-PROV-QUAL-001` and the remaining provider-facing part of `PHIL-AUTH-CONFINE-001`, covering conformance cases `PROV-009` and `AUTH-006` from the Phase 1 matrix.

## Boundary

The previous authority slices established:

- authority exists through explicit possessed semantic capability values;
- abstraction boundaries may preserve or explicitly attenuate authority but may not widen it silently; and
- pure-Phil closures may contain broader reachable authority than their public callable surface only when checked body behavior remains confined.

The provider qualification slices then established exact provider operation correspondence, state simulation, provider-wide laws, and lifecycle/interruption checking.

This slice connects those two families at the provider boundary.

The core rule is:

> A provider implementation may possess broader internal authority than the client-visible provider surface only when every extra authority grant has an explicit confinement/assumption disposition, and the claimed internal-authority inventory itself has a competent basis.

For opaque foreign code, absence of an authority-bearing ABI parameter is never such a basis.

## Two separate questions

Provider authority qualification asks two questions separately.

### 1. Why is this internal-authority inventory complete enough?

`ProviderAuthorityInventoryBasis` records the basis for the declared implementation-internal authority set.

For a semantic pure-Phil provider the bounded Phase 1 form requires a checked pure-Phil inventory revision.

For an opaque/foreign provider, the inventory must instead be justified by one of:

- explicit external qualification/confinement evidence;
- an explicit environmental assumption; or
- an explicit TCB boundary.

`ForeignAuthorityInventoryFromAbiShape` is represented only so the checker can reject it exactly. ABI shape does not establish negative authority.

This matters even when the claimed internal-authority set is empty. Otherwise opaque code could evade `AUTH-006` simply by omitting ambient filesystem/network/device authority from the inventory before per-grant checking begins.

### 2. Why is each extra internal grant safe relative to the public provider surface?

Let:

```text
extra_authority = implementation_internal_authority - client_visible_authority
```

Every element of `extra_authority` must have exactly one `ProviderExtraAuthorityDisposition`.

Permitted bounded dispositions are:

- `ExtraAuthorityStaticallyConfined`;
- `ExtraAuthorityExternallyConfined evidence`;
- `ExtraAuthorityAssumptionDependent assumption`; or
- `ExtraAuthorityTcbBoundary boundary`.

`ExtraAuthorityAssertedAbsentFromAbi` always rejects.

No disposition may be silently invented for an undisclosed or non-extra authority grant.

## Pure Phil static confinement

`ExtraAuthorityStaticallyConfined` is available only to semantic pure-Phil implementations.

The provider qualification consumes already checked closure-confinement summaries. An extra grant is statically confined only when:

- it is actually reachable in the checked pure-Phil environment;
- it is absent from the checked closure public-mediated authority; and
- it is absent from the checked closure exercised authority.

The provider layer also checks two important consistency conditions:

- authority already known reachable from checked pure-Phil summaries may not be omitted from the declared internal-authority inventory; and
- authority already exposed by checked pure-Phil summaries may not be omitted from the declared client-visible provider authority surface.

Thus provider qualification cannot manufacture a narrow claim by underreporting facts the pure-Phil checker already knows.

## Opaque / foreign authority

Opaque foreign provider code cannot use `ExtraAuthorityStaticallyConfined`, because Phil does not have a checked semantic body establishing that relation.

Broader ambient authority may still participate in a conditional qualification when the exact extra grant is:

- covered by external confinement evidence;
- retained as an explicit assumption; or
- retained as an explicit TCB boundary.

This is the `AUTH-006` distinction:

> A foreign implementation with ambient filesystem/network/device authority does not become negatively-authority-safe merely because those capabilities do not appear in its ABI.

The evidence/assumption/TCB key is part of the inspectable qualification lineage. The truth and current admissibility of that external condition remain owned by the corresponding assurance/admission layer.

## Conditional qualification versus admission

An assumption-backed authority qualification can be *closed as a conditional qualification* without being admitted into every build.

For example:

```text
BlobProvider implementation refines BlobProvider.v1
if runtime sandbox S prevents ambient delete authority from escaping
```

or:

```text
BlobProvider implementation refines BlobProvider.v1
under assumption A that its declared ambient-authority inventory is complete
```

are complete conditional claims when every other obligation is also closed.

A strict build policy may later reject `S` or `A`. That does not rewrite the qualification claim; it rejects contextual admission.

## Provider qualification is not runtime possession

As in ADR-021, this checker does not create provider instances or capability possession.

It establishes only an authority-related qualification fact about one exact semantic implementation revision or one exact opaque provider boundary. Runtime reachability still follows the selected architecture/provider/capability flow.

## Exact identity

A semantic provider authority subject is bound to:

- exact provider `InterfaceRevision`; and
- exact implementation `DefinitionRevision`.

An opaque foreign provider authority subject is bound to:

- exact provider `InterfaceRevision`; and
- exact opaque artifact/service/runtime boundary key.

Provider replacement therefore requires a fresh applicable authority qualification for the new implementation subject. Evidence from a previous implementation is not inherited merely because the public provider contract is unchanged.

## Conformance coverage

The dedicated harness covers:

- pure-Phil narrow public authority over broader checked internal authority;
- exact static-confinement acceptance;
- rejection when statically reachable authority is omitted from the provider internal inventory;
- rejection when statically public authority is omitted from the provider public surface;
- exact disposition-domain completeness;
- rejection of a static confinement claim unsupported by the checked closure summaries;
- opaque foreign acceptance with external confinement evidence;
- opaque foreign acceptance as an explicit assumption-dependent qualification;
- opaque foreign acceptance with an explicit TCB boundary;
- rejection of an empty foreign authority inventory justified only from ABI shape;
- rejection of pretending opaque foreign code has a checked pure-Phil inventory;
- rejection of ABI absence as per-grant confinement evidence;
- rejection of static-Phil confinement for an opaque implementation;
- exact semantic provider revision binding;
- subject-sensitive authority identity; and
- canonical disposition-map ordering.

## Deferred

This slice does not yet claim:

- proof that an external sandbox/confinement mechanism actually satisfies its stated evidence key;
- policy admission of assumptions or TCB boundaries;
- evidence-producer subject competence (`PROV-010`);
- generic ProviderQualification claim/evidence/disposition closure;
- ungrounded qualification-cycle rejection;
- contextual `ProviderQualificationAdmission`;
- ArchitectureRealization provider selection;
- target/ABI/StageContract preservation of provider authority confinement;
- final provider syntax; or
- Rocq proof of the provider-authority confinement theorem family.
