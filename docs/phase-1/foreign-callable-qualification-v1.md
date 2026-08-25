# Phase 1 foreign callable qualification boundary v1

Status: implementation note for `CALL-015` / `PHIL-CALL-REFINE-001`.

## Governing rule

A foreign callable is not admitted from ABI/signature compatibility alone.

Phil must first have an explicit qualification record for one exact foreign implementation artifact. That qualification establishes the callable-facing semantic facts which the ordinary higher-order callable refinement checker may then compare with the expected Phil contract.

The relation is therefore:

```text
foreign artifact
  + explicit qualification evidence
  -> qualified callable semantic surface
  -> ordinary callable refinement
  -> admissible foreign callable
```

No successful link, symbol lookup, test run, function-pointer equality, or machine-signature match skips the qualification step.

## Artifact binding

`ForeignCallableArtifactKey` identifies the exact foreign implementation artifact to which qualification evidence applies.

A qualification for one artifact cannot be reused for another artifact merely because both expose the same machine shape or public callable contract.

The qualified semantic surface must also equal the admitted semantic facts for that artifact. Evidence for a different surface is rejected before refinement.

## Required evidence dimensions

The bounded CALL-015 checker requires explicit evidence references for:

- ABI / parameter-result correspondence;
- resource and callee lifecycle behavior;
- semantic effect confinement;
- caller-visible authority confinement; and
- modeled failure behavior.

These dimensions remain independent. ABI evidence does not prove effect confinement; effect evidence does not prove authority confinement; successful resource correspondence does not prove absence of extra fatal behavior.

The evidence payloads are stable evidence identities/references. This checker verifies that every required dimension is explicitly covered and bound to the exact artifact. It does not pretend to derive universal facts about arbitrary foreign code internally.

## Reuse of callable refinement

After qualification establishes the foreign callable's semantic surface, `checkCallableRefinement` performs the existing CALL-012 non-widening check.

Therefore a fully evidenced foreign callable still rejects when its qualified surface:

- requires stronger caller authority;
- permits wider semantic effects;
- admits extra modeled/fatal failures; or
- has an incompatible callee lifecycle.

Qualification makes foreign semantic claims explicit; it does not override the Phil contract.

## Conformance

`test/Phase1ForeignCallableQualificationMain.hs` covers:

- matching signature with no qualification;
- ABI evidence alone;
- complete explicit qualification;
- cross-artifact qualification reuse;
- qualification/admitted-surface mismatch;
- fully qualified but wider effects;
- fully qualified but stronger authority;
- fully qualified but extra fatal behavior; and
- canonical missing-evidence diagnostics.

The harness runs as a named step inside the shared Haskell `build-and-test` CI job.

## Deferred

This slice does not implement full ADR-021 provider qualification, provider-wide state/laws, concrete foreign evidence generation, runtime confinement mechanisms, target closure conversion (`CALL-016`), final foreign-callable syntax, or Rocq proof. It establishes the callable-facing qualification boundary that those later layers must feed.
