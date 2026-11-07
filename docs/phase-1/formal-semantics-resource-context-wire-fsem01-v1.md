# FSEM-01 — exact bounded resource-context extraction and transition evidence

> **Status:** non-normative, checked state representation plus bounded Rocq
> transition lemmas. This is **not** a universal Haskell-to-Rocq simulation,
> a verified compiler/checker, or a global `satisfies C` result. Tracks
> [#1613](https://github.com/abiggerhammer/phil/issues/1613).

## Why another wire?

The preceding [checker-state observation slice](formal-semantics-checker-state-observation-fsem01-v1.md)
extracted owner/loan **bits** from actual source checker checkpoints. Bits
alone cannot distinguish a valid one-owner state from a malicious additional
binding or loan, and say nothing about the *other* resource collections.

This slice changes the [production Engine checkpoint](../../src/Phil/Surface/Check/Engine.hs)
to retain **all four** collections from the exact `Core.Context.ResourceContext`
at the observation point: unrestricted bindings, affine bindings, linear
bindings, and active shared loans. The previously checked observer now refuses
unexpected unrestricted and affine entries as well.

The separate **`PHIL-FSEM01-CONTEXT-V1|`** artifact contains six
length-framed ASCII fields, in order:

1. SHA-256 of exact UTF-8 source bytes;
2. lowercase UTF-8 hex of the derived declaration root;
3. lowercase UTF-8 hex of the source-resolved owner `Core.Name`;
4. lowercase UTF-8 hex of the source-resolved view `Core.Name`;
5. comma-separated source checkpoint words, each carrying
   `phase/unrestricted/affine/linear/loans`;
6. exact terminal outcome.

Map entries are listed in ascending `Name` order using exact bounded tags:
`<owner-hex>=Bytes8` for the linear owner and
`<view-hex>=SharedBytes` for the temporary unrestricted view, with set members listed in ascending order as
`<hex-encoded-name>`. Empty collections are `-`. The fragment refuses
other resource types, and the independent decoder permits only the
one-owner linear domain, a temporary unrestricted `SharedBytes` view within
the scoped body, empty affine bindings, and no foreign loan member. Unknown keys are encoded, **not silently dropped**;
their frames then fail validation.

This is intentionally a *new* artifact. The established
[OBS-V1](formal-semantics-observation-wire-fsem01-v1.md) format and its four
golden source artifacts are unchanged.

## Executable source and transition checks

[Phase1FSEM01ObservationWireMain.hs](../../test/Phase1FSEM01ObservationWireMain.hs)
produces four `.ctx` artifacts from the same actual checker runs as the
four `.obs` artifacts. Its representation is derived from `Map.toAscList`
and `Set.toAscList`, **not** canonical phase-to-bit templates.

It independently reconstructs the captured `Core.Context.ResourceContext`
for each checkpoint, then runs the **real Haskell Core.Context operations**:

- admitted success: `startSharedLoan`, unchanged safe body, `endSharedLoan`,
  and `consumeLinear`, comparing every successor context for exact equality;
- `BorrowEscape` prefix: start the actual loan, retain live owner and loan
  at both error checkpoints, and verify `consumeLinear` returns
  `OwnerBorrowed`; no invented post-rejection successor;
- tampering: fail on extra unrestricted/affine/linear entries, foreign loans,
  unexpected owner/view identities, and wrong binding types.

The separate [Python exact-bytes validator](../../scripts/fsem01_resource_context_witness.py)
rejects noncanonical framing, unknown sequences, wrong maps/loans, and
inconsistent source/declaration/binder/outcome fields when joined with the
matching OBS-V1 artifact. It generates literal **Rocq computations over the
exact emitted bytes**. Python and Haskell remain outside the proof kernel.

## Rocq scope and independent CI

[SurfaceResourceContextWire.v](../../proof/Phil/Surface/SurfaceResourceContextWire.v)
defines the length-framed decoder, the explicit join to an OBS-V1 decoded
artifact, and a one-owner extensional `Context.ResourceContext`
reconstruction parameterized by a Rocq `Ty`. It proves exact owner and loan
lookups, start/end/terminal consumption of the admitted model, and rejection
of linear consumption while the loan is active.

[The dedicated CI workflow](../../.github/workflows/fsem01-resource-context-wire.yml)
builds Haskell with `-Werror`, runs the actual source fixtures, uploads
all eight OBS/CONTEXT artifacts, independently rechecks and regenerates the
literal witness bytes, compiles Rocq 9.2 proofs without admissions, and
records hashes of both emitted source evidence and checked proof objects.

**Still unproved:** that every Haskell `ResourceContext` corresponds to the
extensional Rocq `Context`, that the entirety of runtime source evaluation
is covered, correctness of unrestricted Unicode name transformations,
general resource types and ownership modes, captures/joins/loops and
error-path simulation, or whole-program `satisfies C`. The bounded wire
decoder is a stronger *independently checked representation of observed
states*, not a general proof about the implementation.
