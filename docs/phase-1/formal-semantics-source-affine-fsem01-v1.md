# FSEM-01 — checked source nominal affine ownership and lifecycle

> **Status:** non-normative, deliberately small source-fragment bridge.
> Tracks [FSEM #1613](https://github.com/abiggerhammer/phil/issues/1613).
> A declared source mode is **not** itself permission to strengthen a
> resource mode, and no generic compiler-soundness claim is made.

## Checked source fragment

This slice accepts the closed nominal declaration
`data Permit mode affine = Permit(U64);` together with one separately
**admitted** lifecycle/resource justification, through the existing
`grammarV1CheckedClosedDataMode` nominal authority.

The intrinsic `U64` payload is Unrestricted. Therefore, without a
separately admitted lifecycle justification, the proposed Affine nominal
mode is rejected as `StrongerModeMissingJustification Unrestricted Affine`.
An `UnadmittedNominalRestriction` is rejected, too. An explicitly
`mode unrestricted` data declaration containing `Bytes[8]` is
rejected as `DeclaredModeWeakensDerived Linear Unrestricted`.
No source spelling or display name is silently treated as lifecycle proof.

[Production source bridge](../../src/Phil/Surface/GrammarV1/SourceAffineResource.hs)
resolves the type of a source function's named `Permit` parameter using
`GrammarV1ResolvedNamedTypeMode` with exact `DeclarationKey`,
`InterfaceRevision` and `GenericTypeKind` provenance. Its binder uses
the real `grammarV1FunctionParameterScope` identity. Only after
these checks does the bridge install the resulting
`CheckedTypeMode (TyOpaque "Permit") Affine` in the actual
Surface checker's `InitialBinding`; mode is **not caller-injected into
the checker**.

The bounded function has exactly one nominal affine parameter, one
lexical borrow body containing only checked `view` and `unit`
expressions, and either a return of the exact owner or `unit`.
Generic/recursive functions, arbitrary expressions, unrecognised
named types, and other function shapes remain outside competence.
`satisfies C` is **not** discharged by this bridge.

## Executable witnesses

[Haskell regression driver](../../test/Phase1FSEM01SourceAffineMain.hs)
parses the source files in
[`fsem01-source-affine-v1`](../../test/fixtures/fsem01-source-affine-v1)
and compares the actual production Surface borrow trace with native
`Core.Context` transitions:

- **consume.phil**: borrow, end the loan, return and consume the affine
  owner exactly once.
- **drop.phil**: borrow, end the loan, then `return unit`. A still-live
  affine owner at function exit is allowed by native `ensureComplete`,
  unlike a linear owner.
- **escape.phil**: minimally remove trailing `unit;` from the borrow
  body; its result contains the view, causing precisely
  `BorrowEscape: shared view escapes its lexical scope` with no invented
  post-rejection successor.
- **unjustified.phil**: affine declaration without admitted lifecycle
  evidence fails the nominal mode-strengthening authority.
- **weakened.phil**: explicit Unrestricted declaration cannot weaken a
  Linear `Bytes[8]` payload.

The driver also checks the exact Core four-zone snapshot:
`affineBindings` contains the semantic binder key, `linearBindings`
and `unrestrictedBindings` remain empty, loan start/end changes only
the owner's shared-loan bit, borrowed consumption returns
`OwnerBorrowed`, and consumed-owner reuse returns `UnknownBinding`.

These claims concern a **bounded source-driven route and actual
production checker execution**. The provenance values supplied to the
resolver and the external admission of the lifecycle text are still
trusted inputs. We do not claim the text has been independently proved.

## Rocq model relation

[SurfaceSourceAffineBridge.v](../../proof/Phil/Surface/SurfaceSourceAffineBridge.v)
models a source affine gate with an explicit external admission Boolean.
It proves that admission is necessary, and combines the previously
proved general four-zone `ForeignFrame` relation with source-conditional
insertion, borrowing, affine consumption and model disposal. Borrowed
owners cannot be consumed or disposed. The finite-context theorems
quantify over arbitrary unrelated spectators.

The model does **not** prove actual Haskell `Map`/`Set` implementation
correctness, `Text` to Rocq `String` semantics, exact native
`CheckError` correspondence, the soundness of external attestation,
or general source type preservation.

## Runway-efficient CI

The new [source affine preflight](../../.github/workflows/fsem01-source-affine-preflight.yml)
starts on pushes to this **work branch before PR creation**, and
also on the eventual PR head. Two focused jobs perform:

1. A strict production Haskell library build, the relevant SURF-008
   type/declaration corpus and previous FSEM-01 regression drivers,
   plus executable source-affine positive/rejected witnesses.
2. Rocq 9.2 compilation of `Syntax`, `Context`,
   `SurfaceFiniteContextFrame` and the new source-affine correspondence,
   excluding new `Admitted`/`Axiom`/`Parameter` declarations.

The Haskell setup uses the merged `cabal-update-retry.sh` before any
network-reliant package build. Broad PR checks are triggered only after
this focused branch preflight succeeds.

**Still open:** source-level affine constructors and general elimination,
multi-owner mixed-mode functions, arbitrary loops/joins/captures,
native-to-Rocq universal simulation, and complete executable semantics
(FSEM-05).
