# Phase 1 Structural-Mode Surface Reconciliation v1

## Status

Design/surface reconciliation for the Phase 1 canonical grammar. This pass does not introduce a fourth structural mode or change ADR-002 resource semantics. It makes the existing unrestricted/affine/linear discipline explicit at the source/type boundary and closes an ambiguity about where a runtime binding gets its mode.

The normative concrete-syntax authority remains `grammar/phase1-surface.ebnf`. Semantic acceptance remains governed by ADR-002, ADR-014, ADR-023, and the resource/data/generic checker contracts.

## The gap

Before this reconciliation, the accepted semantics already said all of the following:

- the term context has unrestricted, affine, and linear zones;
- unrestricted values admit weakening and contraction;
- affine values admit weakening but not contraction;
- linear values admit neither;
- records, sums, and closures cannot launder a restricted constituent into a weaker aggregate;
- aggregate mode is derived conservatively from owned contents;
- generic instantiation propagates structural mode from actual parameters;
- authority-bearing capabilities have a structural mode distinct from their authority contract; and
- ADR-023 permits a nominal data type to impose a mode stricter than the minimum derived from its transparent fields when its semantic contract itself carries a lifecycle/resource obligation.

What the canonical surface did not say was how those facts meet ordinary declarations. In particular, `x : T` had no explicit statement that `x` inherits the structural mode of `T`, while Grammar v1 had no way to spell ADR-023's exceptional stricter nominal mode or ADR-014's capability mode.

This pass makes that boundary explicit.

## Governing rule

> **Structural mode is a checked property of the value type/resource contract, not an independently selectable property of an ordinary local name.**

If an owning binding has type `T`, elaboration places the binding in the context zone determined by `mode(T)`:

```text
mode(T) = unrestricted  -> unrestricted context
mode(T) = affine        -> affine context
mode(T) = linear        -> linear context
```

This applies to term parameters, `let` bindings, pattern-bound owners, callable results/state slots, and other ordinary owning term occurrences after their checked type is known.

The surface therefore does **not** add forms such as:

```text
linear x : U32
affine y = value
```

Such spelling would make a local binder appear able to alter structural semantics independently of the value type. It is intentionally absent.

Scoped shared loans remain non-owning relations to an affine/linear owner, not a fourth structural mode and not a way to reclassify the owner.

## Where `mode(T)` comes from

### Intrinsic/prelude resource types

Built-in or prelude semantic types whose contracts already fix structural behavior keep that behavior. Pure immutable value types such as ordinary booleans and fixed-width unsigned values are unrestricted. Resource types such as owned bytes and session endpoints may be linear. Other resource/capability types carry the mode fixed by their checked semantic contract.

This reconciliation does not add a generic user syntax for redefining the modes of built-in types.

### Ordinary records

When no explicit mode clause appears, a transparent record derives its mode as the least upper bound of the modes of fields it **owns** under:

```text
unrestricted < affine < linear
```

For example, a record containing only unrestricted fields is unrestricted; a record owning one affine constituent is at least affine; a record owning one linear constituent is linear.

Non-owning dependencies and propositions referring to the stable identity of a restricted resource do not themselves own another occurrence and therefore do not strengthen aggregate mode.

### Ordinary sums

When no explicit mode clause appears, a sum is classified conservatively across all constructor payloads. If any constructor may own a linear constituent, the sum type is linear. Otherwise, if any constructor may own an affine constituent, it is affine. Pattern matching may recover constructor-local resource precision, but the whole sum's static mode remains conservative in Phase 1.

### Generic data

Generic aggregate mode is a checked mode expression over its actual structural parameters. Instantiation resolves the actual modes and then applies the same strongest-owned-constituent rule. Thus one generic declaration may instantiate as unrestricted, affine, or linear without acquiring undeclared copy/drop privileges.

### Closures

Closure mode remains derived from the captured owning environment. This pass does not add a closure-local mode annotation.

### Capabilities

An authority capability's structural mode cannot in general be derived from the operations it permits: authority answers what possession may do, while structural mode answers whether that possession may be copied or silently discarded.

Grammar v1 therefore requires a capability declaration to state one of the three modes explicitly:

```phil
capability BlobRead mode unrestricted {
    permits storage.Read;
}

capability Lease mode affine {
    permits storage.Use;
}

capability LifecycleToken mode linear {
    permits lifecycle.Finish;
}
```

The mode does not by itself make an operation one-shot. ADR-014 still requires a consuming operation/transition when authority exercise itself is one-shot. A linear capability instead means that the capability resource has a non-droppable lifecycle obligation.

## Explicitly stricter nominal data modes

ADR-023 already permits a nominal data type to be stricter than its transparent owned fields imply when the nominal value itself represents a semantic lifecycle/resource obligation.

Grammar v1 now exposes that case with an optional `mode` clause after generic parameters and before a `requires` block:

```phil
record FireOnceToken mode linear {
    id : U64
}

data MaybeLease mode affine =
    NoLease
  | LeaseId(U64);
```

For a record or sum with no explicit `mode`, the final mode is the ordinary derived mode.

For a record or sum with an explicit declared mode `m`, the checker computes the ordinary derived minimum `d` and requires:

```text
d <= m
```

The final checked type mode is `m`.

Thus explicit mode is a **strengthening declaration**, never a laundering annotation. This parses but must fail semantic checking:

```phil
record BadWrapper mode unrestricted {
    payload : OwnedBytes[n]
}
```

because the owned field requires a linear minimum.

A declaration that strengthens from unrestricted to affine/linear, or from affine to linear, must also have a semantic reason in its declaration/interface contract when certification cares about why the stronger lifecycle obligation exists. Grammar merely provides the spelling; it does not manufacture the obligation.

## Transparent aliases do not reclassify

A transparent type alias remains definitionally the aliased type and inherits its structural mode. Grammar v1 deliberately does not permit `mode` on `type` aliases.

If a programmer needs a new nominal resource with stronger structural semantics, that is a nominal resource/data declaration rather than a transparent alias whose mode has been changed by spelling.

## Ordinary binding rule

After elaboration establishes `e : T`, an ordinary binding receives `mode(T)` automatically:

```phil
fn forward(x : OwnedBytes[n]) -> OwnedBytes[n] satisfies Forward[n] {
    let y = x
    return y
}
```

Both `x` and `y` are linear owners because `OwnedBytes[n]` is linear. No `linear` keyword is needed or permitted on either binding.

The same rule applies when a pattern exposes a field/constructor payload: each owning pattern binding receives the structural mode of its exposed type, while the consumed aggregate occurrence is removed according to the existing resource rules.

## Grammar v1 changes

The canonical EBNF now includes:

```text
structural_mode = "unrestricted" | "affine" | "linear" ;
```

Records and sums accept an optional declaration-level mode:

```text
record Name[... ] mode linear requires { ... } { ... }
data Name[... ] mode affine requires { ... } = ... ;
```

Capabilities require a mode:

```text
capability Name[... ] mode unrestricted requires { ... } { ... }
```

Exact punctuation and optionality are governed by the EBNF itself; the examples above are explanatory renderings.

The new literals become reserved keywords under the existing lexical rule.

## Competence boundaries

Parsing is competent only to establish that a declaration contains a syntactically valid structural mode literal in a permitted declaration position.

The semantic checker remains competent for:

- intrinsic/prelude type modes;
- aggregate mode derivation from owned fields/constructors;
- generic mode instantiation;
- closure capture-mode derivation;
- checking that an explicit nominal data mode does not weaken the derived minimum;
- checking the declared capability mode as part of the capability interface;
- determining whether a stronger nominal mode is backed by the intended semantic resource/lifecycle contract;
- placing ordinary owning bindings in the correct residual context zone; and
- enforcing weakening/contraction/consumption rules after that placement.

A parser must not infer semantic validity from the spelling `mode linear`, and an elaborator must not reinterpret a local name's mode independently of its type to make a program pass.

## Conformance consequences

The eventual canonical production/parser corpus should contain positive syntax cases for:

- a record with an explicit stronger `mode linear`;
- a sum with an explicit stronger `mode affine`;
- a capability with each admitted mode spelling; and
- ordinary `x : T` / `let x = ...` bindings with no mode annotation.

Malformed syntax should cover missing/unknown mode literals and illegal binding-local mode syntax.

Semantic conformance should separately cover:

- omitted record/sum mode deriving the existing minimum;
- valid strengthening;
- attempted weakening rejection;
- conservative sum derivation;
- generic mode propagation;
- capability copy/drop behavior for unrestricted/affine/linear declarations; and
- a binding entering the context mode dictated by its checked type rather than by local spelling.

These are semantic/resource checks, not parser success criteria.

## Relationship to the earlier grammar/type-system reconciliation

The earlier `grammar-typesystem-reconciliation-v1.md` deliberately avoided unrestricted/affine/linear **binding annotations** because deterministic mode derivation already existed. That decision remains correct for ordinary binders.

The omission that remained was narrower: the surface lacked declaration syntax for the already-admitted cases where mode is itself an identity-bearing semantic fact that cannot be recovered solely from transparent contents. This pass adds that declaration-level surface without turning mode into a per-variable annotation system.

## Exit condition

This reconciliation slice is complete when:

1. Grammar v1 exposes the three structural mode literals in the declaration positions above;
2. the surface/type-system documentation states that ordinary owning bindings inherit `mode(T)`;
3. record/sum omission, strengthening, and no-weakening semantics are explicit;
4. capability declarations expose their structural mode independently of authority semantics;
5. transparent aliases and shared loans do not become alternate reclassification mechanisms;
6. the mechanically derived proof-facing grammar remains deterministic and warning-clean; and
7. no claim is made that the current Haskell parser/checker already implements the revised declaration forms until the corresponding SURF/resource implementation obligations are discharged.
