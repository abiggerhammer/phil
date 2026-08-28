# Assurance validity-scope implementation refinement v1

## Status

Staging / Mechanized target for `PHIL-ASSURE-VALIDITY-IMPL-001`.

## Purpose

`PHIL-ASSURE-VALIDITY-001` certifies the generic validity-scope authority used by assurance verification: every dimension bound by a `ValidityScope` must have the exact expected value in the effective verification context; unbound dimensions carry no authority.

Production currently implements this rule in `Phil.Assurance.Verify.scopeMatches` by enumerating the concrete `Map Text Text` scope and checking each effective-context lookup with native equality. The Certified Rocq model is representation-neutral, so the concrete `Text`/`Map` correspondence is still a reviewed boundary.

This tranche begins mechanical implementation refinement without changing production behavior.

## Executable seam

`proof/Phil/Assurance/ValidityScopeImplementation.v` extracts the finite conjunction that production needs. The kernel consumes one Boolean fact for each bound scope entry and accepts exactly when every fact is true.

The correspondence layer keeps the representation bridge explicit:

- `ScopeEntriesComplete` states that an enumerated finite entry list contains exactly every dimension/value binding carried by the Certified scope;
- `ScopeFactReflection` states that each supplied Boolean is true exactly when the effective context lookup returns that entry's exact expected value; and
- `validity_scope_decision_accept_iff_certified_match` proves that, under those two bridge conditions, the executable decision accepts if and only if the Certified `ScopeMatches` proposition holds.

The empty-scope, single-match, and single-mismatch controls are also pinned directly.

`ValidityScopeImplementationExtraction.v` extracts only the Boolean list conjunction and final decision. No `Text`, `Data.Map`, validity dimension, or validity value is serialized through Rocq.

## Production boundary retained in staging

Production is deliberately unchanged in this tranche. In particular, it does **not** yet claim mechanical correspondence for:

- concrete `Text` equality for validity dimension names and values;
- `Data.Map.Strict.toList` completeness/canonical finite enumeration;
- `Data.Map.Strict.lookup` correspondence to the normalized partial-map model;
- construction of the effective context from manifest validity context plus target and compilation profile; or
- callers that construct domain-specific validity scopes, including architecture interface scopes.

Those are the concrete bridge obligations for the production-binding closeout. As elsewhere in Phase 1, primitive native equality and canonical finite-map behavior may remain named representation foundations, but the production acceptance decision itself must be owned by the extracted kernel before this obligation can become `Implementation Refined` under `PHIL-ASSURE-IMPL-CORR-001`.

## Architecture dependency

This generic refinement is the competence-preserving dependency required by `PHIL-ARCH-ID-IMPL-001`. Architecture-specific code constructs an interface-validity dimension and exact interface revision, but the generic assurance verifier owns whether a `ValidityScope` matches an effective context. Binding that generic verifier mechanically is therefore preferable to duplicating or bypassing its authority inside the architecture layer.

## Validation

The dedicated workflow must:

- recompile the Certified `ValidityScope.v` model;
- compile the implementation correspondence proof;
- fresh-extract `AssuranceValidityScopeKernel.hs`;
- typecheck the extracted kernel under `-Wall -Werror`;
- typecheck the unchanged `Phil.Assurance.Verify` implementation;
- rerun the unchanged validity-scope correspondence corpus; and
- rerun the ordinary assurance corpus.

A green staging run earns `Active / Mechanized` evidence for this bounded generic decision seam only. Production binding is a separate closeout slice.
