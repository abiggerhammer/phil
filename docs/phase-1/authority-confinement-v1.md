# Phase 1 closure authority confinement v1

This slice advances the closure-local half of `PHIL-AUTH-CONFINE-001` and conformance case `AUTH-004` from ADR-014 and the Callable and Closure Checking Contract.

It does **not** yet close the full ledger obligation because provider/foreign confinement remains dependent on ADR-021 qualification.

## Core distinction

A closure may possess broader internal authority than its public callable interface exposes.

For example, a closure may capture a capability permitting both `read` and `delete`, while its public callable interface mediates only `read` and the checked body exercises only `read`.

That is valid confinement.

However, the same facts do **not** prove that `delete` authority is absent from the closure environment. The captured capability still makes `delete` reachable by the closure body.

The checker therefore keeps three sets distinct:

1. **reachable internal authority** — authority obtainable through captured capabilities and captured/nested callable values;
2. **public mediated authority** — authority the checked callable interface exposes through invocation; and
3. **exercised authority** — authority operations actually used by the checked implementation body.

The bounded pure-Phil relation requires:

```text
public mediated authority ⊆ reachable internal authority
exercised authority       ⊆ reachable internal authority
exercised authority       ⊆ public mediated authority
```

The first condition ensures that the concrete closure instance can realize the public authority it claims to mediate. The second is ordinary possession/reachability soundness. The third is behavioral confinement.

## Reachability

Reachability is subject-specific and operation-specific.

Each `ReachableAuthorityGrant` records:

- a source-semantic origin;
- an exact `AuthoritySurface` with authority contract, stable subject, and operation set.

The initial origins are:

- a captured capability occurrence;
- a captured callable occurrence; or
- another explicitly named source-semantic origin reserved for later extensions.

Reachability **unions** authority across the closure environment. If any captured value can exercise an operation over a subject, that authority is reachable.

This is intentionally different from authority at a control-flow join, where #175 conservatively keeps only authority available on every continuing branch.

## Negative-authority claims

A negative claim has the form:

```text
No reachable authority for operation O over subject κ
```

The checker evaluates that claim against the exact reachable internal authority of an already checked closure confinement summary.

A narrow public effect/authority interface cannot prove such a negative fact. If the closure captures `delete` authority but never exercises it, then:

- checked behavioral confinement may succeed;
- `delete` may be absent from the public interface;
- nevertheless, a claim that `delete` authority is absent from the closure environment is false.

Diagnostics retain the exact captured capability/callable origins that make the negative claim false.

Claims are subject-specific. `delete` authority over `store.secondary` does not refute a claim about `store.primary`.

## Captured callables

Captured first-class callables participate in authority reachability just like captured capabilities when their invocation interface mediates authority.

Passing a narrow function does not convey its whole provider, but the authority obtainable through that function remains reachable through the captured callable value. Negative-authority analysis must therefore include both raw captured capabilities and callable-mediated paths.

## What this slice proves mechanically

The dedicated harness covers:

- broader captured read+delete authority with read-only public behavior;
- successful confinement when the checked body uses only read;
- rejection when the body exercises reachable-but-hidden delete authority;
- rejection when the body exercises authority that is not reachable at all;
- rejection when the public mediated authority claims an operation unavailable to the closure instance;
- rejection of a false delete-absence claim despite narrow public behavior;
- acceptance of a genuinely absent write-authority claim;
- captured callable authority participating in reachability;
- subject-specific negative claims;
- duplicate-grant canonicalization; and
- grant-order noninterference.

## Deferred provider/foreign half

This slice intentionally does not claim the provider/foreign half of `PHIL-AUTH-CONFINE-001` or `AUTH-006`.

Opaque/foreign implementations may possess filesystem, network, device, process, or other ambient authority that pure Phil structure cannot enumerate. Proving confinement or absence there requires ADR-021 provider/foreign qualification, explicit sandbox/confinement evidence, or an explicit assumption/TCB boundary.

That later provider slice must preserve the rule established here: ABI/signature shape, symbol identity, successful linking, and narrow observed effects do not by themselves prove absence of stronger reachable authority.

## Deferred

Also deferred:

- provider-wide authority qualification;
- foreign ambient-authority policy (`AUTH-006`);
- Systems/StageContract authority correspondence;
- concrete OS/process sandbox evidence;
- final capability/callable surface syntax; and
- Rocq proof of the complete `PHIL-AUTH-CONFINE-001` obligation.
