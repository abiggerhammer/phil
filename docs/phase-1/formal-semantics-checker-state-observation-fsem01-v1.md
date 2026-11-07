# FSEM-01 — resource-context to loan-observation refinement

> **Status:** non-normative, bounded resource-state observation proof and
> checked Haskell observer. This is *not* a universal proof that Haskell
> `Map`/`Set` or the surface evaluator refine Rocq `Context`, and not a
> `satisfies C` or source type-soundness discharge. Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613).

## The actual observation boundary

[Engine.hs](../../src/Phil/Surface/Check/Engine.hs) already builds
`BorrowTraceCheckpoint` records by reading the **actual** linear-binding
map and active-loan set from a `SurfaceState`'s resource context. This
slice exports `observeBorrowTraceResource`, an exact, fail-closed
one-owner observer of those **recorded maps and sets**.

The observer takes the expected owner, expected view, and expected
`Bytes[8]` type. It checks both source binder identities and
enumerates all linear-map and loan-set entries, accepting only empty
collections or exactly the expected owner (of the expected type). It
returns the recorded phase, actual linear-owner presence, and actual
shared-loan presence. Unexpected keys or types return `Nothing`.
The observer **does not infer those bits from the phase label**.

The artifact producer in
[Phase1FSEM01ObservationWireMain.hs](../../test/Phase1FSEM01ObservationWireMain.hs)
now renders the v1 checkpoint codes from this Engine observer, not
its former separate `Map.lookup` and `Set.member` implementation.
The source-derived regression test independently compares those
results with the exact original Map/Set contents and tests malformed
owner/view identities, wrong owner type, foreign owner/loan entries,
and forged phase labels. Normal/traced checker parity, source
SHA-256, Unicode UTF-8-hex identity, byte-for-byte golden artifact
comparison, and Rocq witness compilation remain required.

## What Rocq proves

[SurfaceCheckerStateObservation.v](../../proof/Phil/Surface/SurfaceCheckerStateObservation.v)
models the corresponding resource lookups over the existing
`Context.ResourceContext` model. Its central function is
`observeContext phase owner ctx`: the phase tag is preserved, and
both membership bits are computed directly from
`Context.linearBindings ctx owner` and
`Context.sharedLoans ctx owner`.

The theorems establish:

- observed owner presence is exactly the underlying linear binding
  lookup, and observed loan activity exactly the shared-loan lookup;
- an absent binding cannot be reported present, nor a present binding
  reported absent;
- the rendered checkpoint retains the phase and both actual bits,
  and the admitted before-loan state has an unloaned owner;
- successful modeled loan start and end yield exactly the admitted
  active-loan and closed-loan snapshots;
- successful terminal consumption removes the owner, while a
  `BorrowEscape` rejection snapshot retains its live owner/loan,
  without fabricating a post-rejection closure.

These proofs are over the *extensional Rocq Context model*,
using the existing [exact loan-state theorems](formal-semantics-exact-loan-transition-model-fsem01-v1.md).
The [producer-fidelity proof](formal-semantics-producer-fidelity-fsem01-v1.md)
already proved the resulting raw bits are faithfully projected to
the versioned wire. The
[conditional source-observation simulation](formal-semantics-source-simulation-fsem01-v1.md)
then connects a correctly bound, decoded artifact to terminal replay.

## Unproved boundary, explicitly retained

No theorem presently identifies all Haskell `Map` values and
`Set` values with the extensional Rocq functions for *all*
execution states. Nor does this establish the complete correctness
of the parser, runtime view-escape detection, joins/backedges,
nested/captured/affine borrows, or whole-source `satisfies C`.
The Haskell observer checks the admitted one-owner fragment
and *refuses* other shapes.

The next refinement obligation is therefore exact extraction of
the actual Haskell resource context itself, including its
state-transition operations, into a proof-carrying or independently
certified representation. This slice narrows the gap to that
cross-language state correspondence. It does not erase it.

## Formal-methods reading entry points

The repository [formal-methods reader guide](../../README.md)
and [Phase 1 review index](README.md) now link first to the
[**normative Phase 1 surface EBNF**](../../grammar/phase1-surface.ebnf),
[grammar authority and versioning](surface-grammar-v1.md),
and [syntax–semantics completeness audit](syntax-semantics-completeness-v1.md).
The typing rules reader and worked examples remain explicitly
non-normative review materials.
