# FSEM-01 — checked two-Bytes product return in one source function

> **Status:** bounded, non-normative product-elaboration correspondence, following
> [#1655](https://github.com/abiggerhammer/phil/pull/1655). Tracks
> [FSEM #1613](https://github.com/abiggerhammer/phil/issues/1613).
> This does not prove general tuple typing, source-to-Rocq refinement, or
> the source-level `satisfies C` obligation.

## What changes at the authority boundary

The prior single-source two-owner bridge checked both `Bytes[8]` result
elements but its production Surface return still contained the **opaque**
`TyOpaque "Tuple[2]"` marker. That marker described only arity; it could
not establish element type, structural mode or ordering.

The checked type/mode dispatcher now has one **closed, exact product
fragment**: a Grammar-v1 two-element `(Bytes[N], Bytes[M])` source type,
whose two children individually pass the existing production checked
`Bytes` type/mode path. It preserves both ordered `Core.Ty` values
and their certified `Linear` modes in the actual

```haskell
TyProduct
  [ ProductElementType Linear (TyBytes (RefNat n))
  , ProductElementType Linear (TyBytes (RefNat m))
  ]
```

The whole product's mode follows the existing certified
`deriveRecordMode` rule. General tuple elaboration, nesting, nominal
elements and dependent substitutions remain **outside this fragment**.
Unsupported forms return `Nothing`, not fabricated mode witnesses.

## Actual runtime verification, not a post-hoc label

The bounded [Grammar-v1 source bridge](../../src/Phil/Surface/GrammarV1/TwoOwnerBorrowResourceSurface.hs)
now consumes the **entire checked source result product**, checks
the expected first and second owner types against its exact elements,
and installs the checked element contract in
`SurfaceEnvironment.surfaceExpectedProductReturn`.

During the real production `returnPath`, after the ordinary tuple
expression has evaluated and consumed the corresponding owners, the
checker independently reconstructs each scalar element's actual
`(Mode, Ty)` (including existing decision-carrier mode discipline)
and compares the **entire ordered list** to the supplied checked
product contract. Only an exact match emits `Return (TyProduct actual)`.
Wrong width, mode or arity produces the precise `TypeMismatch`
diagnostic. Nested or unknown runtime tuple carriers remain unsupported
at this boundary.

An unconfigured Surface environment preserves its existing opaque tuple
return behavior, so ordinary unrelated tuple users do not silently gain
new source typing authority.

## Exact executable evidence

[Two-owner source tests](../../test/Phase1FSEM01TwoOwnerSourceMain.hs)
independently inspect the parsed result type with
`grammarV1CheckedTypeMode`, verify it becomes the exact
`TyProduct [Linear Bytes8, Linear Bytes8]`, and require the
**actual production checker** to return that value rather than
`TyOpaque "Tuple[2]"`. Previous accepted/BorrowEscape trace and
resource preservation checks are retained.

New wrong-product-width and unsupported-product-element source
specimens are rejected as outside the admitted fragment; reversed
returns and extra linear parameters continue to reject. An independent
low-level Surface test also supplies valid and **forged** product
contracts and checks the actual production engine: a correct exact
product returns the proper `TyProduct`, but incorrect element width,
mode or arity fails with `TypeMismatch`. The same tuple with no
product contract must still return the legacy opaque arity carrier.

The [FSEM-01 source CI workflow](../../.github/workflows/fsem01-two-owner-source.yml)
strictly builds the registered production library and Haskell tests
with `-Wall -Werror`, reruns the previous source/Core context
conformance, and records hashes of the checked source, type and
return implementations. It remains governed by PR-only supersession.

## Proof boundaries and next work

The earlier [two-owner Rocq frame lemmas](../../proof/Phil/Surface/SurfaceTwoOwnerContext.v)
remain valid and independently checked. The new type-return
correspondence is established by **actual Haskell source/engine tests**,
not a new Rocq source-to-Core preservation theorem.

General recursive `TyProduct` elaboration, runtime tuples containing
nested products or non-Bytes elements, reusable product values,
arbitrary finite Haskell resource maps, source error simulation,
captures/joins/loops and full `satisfies C` discharge remain open.
Any change to normative typing authority must follow Phil's explicit
review/ADR process.
