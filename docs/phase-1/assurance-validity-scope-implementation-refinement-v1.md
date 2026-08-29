# Assurance validity-scope implementation refinement v1

## Status

Production-binding closeout for `PHIL-ASSURE-VALIDITY-IMPL-001`.

## Purpose

`PHIL-ASSURE-VALIDITY-001` certifies the generic validity-scope authority used by assurance verification: every dimension bound by a `ValidityScope` must have the exact expected value in the effective verification context; unbound dimensions carry no authority.

Production represents one finite scope as `Map Text Text`. The Certified Rocq model remains representation-neutral, so concrete `Text` equality, finite `Map` enumeration, lookup, and effective-context construction remain explicit native correspondence foundations.

## Executable seam

`proof/Phil/Assurance/ValidityScopeImplementation.v` extracts the finite conjunction production needs. The kernel consumes one Boolean fact for each bound scope entry and accepts exactly when every fact is true.

The correspondence layer keeps the representation bridge explicit:

- `ScopeEntriesComplete` states that the enumerated finite entry list contains exactly every dimension/value binding carried by the Certified scope;
- `ScopeFactReflection` states that each supplied Boolean is true exactly when the effective-context lookup returns that entry's exact expected value; and
- `validity_scope_decision_accept_iff_certified_match` proves that, under those two bridge conditions, the executable decision accepts if and only if the Certified `ScopeMatches` proposition holds.

The empty-scope, single-match, and single-mismatch controls are pinned directly. `ValidityScopeImplementationExtraction.v` extracts only the Boolean list conjunction and final decision; Coq `bool` maps directly to `Prelude.Bool`, and Coq lists map directly to Haskell lists. No `Text`, `Data.Map`, validity dimension, or validity value is serialized through Rocq.

## Production binding

`Phil.Assurance.Verify.scopeMatches` now enumerates every `(dimension, expectedValue)` pair in the concrete `ValidityScope`, computes the native lookup/equality fact

`Map.lookup dimension effectiveValidity == Just expectedValue`

for each entry, and supplies the complete Boolean list to `AssuranceValidityScopeKernel.decideValidityScope`.

A successful production scope match therefore requires both:

1. the extracted kernel to return `ValidityScopeAccepted`; and
2. the native reflected facts themselves to all be true.

Kernel rejection returns `False`, and any impossible native/kernel disagreement also fails closed as `False`. The same bound function is used for evidence, assumption, and export validity scopes, so those three production acceptance paths share the Certified decision seam rather than duplicating it.

## Explicit native foundations

The following remain named representation/runtime foundations rather than being serialized through Rocq:

- concrete `Text` equality for validity dimension names and values;
- `Data.Map.Strict.toList` complete finite enumeration of the scope map;
- `Data.Map.Strict.lookup` behavior for the effective context;
- construction of the effective context from manifest validity context plus exact target and compilation profile entries; and
- callers that construct domain-specific validity scopes, including architecture interface scopes.

These native facts must reflect the Certified model exactly. Handwritten bridge code cannot turn an extracted-kernel rejection into success.

## Architecture dependency

This generic refinement is the competence-preserving dependency required by `PHIL-ARCH-ID-IMPL-001`. Architecture-specific code constructs an interface-validity dimension and exact interface revision, while the generic assurance verifier owns whether a `ValidityScope` matches an effective context. Mechanically binding that generic verifier avoids duplicating or bypassing its authority inside the architecture layer.

## Validation

The dedicated workflow:

- recompiles the Certified `ValidityScope.v` model and implementation correspondence;
- fresh-extracts `AssuranceValidityScopeKernel.hs` and requires byte-for-byte identity with the checked-in production kernel, printing a unified diff on mismatch;
- strict-typechecks the exact kernel, bound `Phil.Assurance.Verify`, Rocq validity adapter, proof-correspondence executable, and ordinary assurance corpus under `-Wall -Werror` where applicable;
- reruns the validity-scope correspondence controls, including empty, matching, and mismatching scopes;
- reruns the ordinary assurance corpus, which includes a valid reference manifest and stale validity-scope rejection through production; and
- records closeout SHA-256 identities and uploads a dedicated production-binding artifact.

An all-green exact head closes `PHIL-ASSURE-VALIDITY-IMPL-001` as `Discharged / Implementation Refined`.
