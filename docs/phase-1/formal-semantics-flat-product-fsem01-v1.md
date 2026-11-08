# FSEM-01 — flat source products and mixed-mode contract preservation

> Non-normative, bounded formal-semantics slice following #1658.
> Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613).
> Passing tests and a conditional Rocq model are not language-wide
> source-to-Core preservation.

## New admissible source fragment

The checked Grammar-v1 type dispatcher extends the former *exactly
two Bytes types* product case to an **ordered flat product with at least
two primitive elements**, each already accepted by the ordinary type/mode
checker. The closed admissible palette is `Unit`, `Bool`, `U<n>`, and
`Bytes[N]`. Every member is checked independently; failure at any
member refuses the whole product.

The compiler constructs `TyProduct [ProductElementType]` in exact source
order, preserving both each element's `Mode` and `Ty`. The aggregate mode
is the existing `deriveRecordMode` of the element-mode list. In particular,
`(Unit, Bool, U32)` is unrestricted, while
`(Unit, Bool, U32, Bytes[8])` and
`(Bytes[8], Bool, Bytes[9])` are linear. The earlier two-Bytes result
remains supported unchanged.

**Outside this fragment:** nested tuples, nominal types, proof-carrying
product elements, contextual substitutions and named/affine-specific
source types. These remain unsupported, not guessed. The intrinsic and
bound type routes remain unchanged: this is checked typing competence
only. An affine owner can participate when supplied as an *already checked
Core binding*; source-to-Core derivation of that affine binding is a
separate obligation.

## Real production return contracts

The source checker produces exact, ordered element contracts. The
already-merged, optional `surfaceExpectedProductReturn` path in
`returnPath` compares the **actual evaluated tuple elements** against
the full expected `Mode`/`Ty` list, refusing wrong mode, width,
arity and order. An absent contract preserves the legacy opaque
`Tuple[n]` result and gains no new typing authority.

[Strict Haskell tests](../../test/Phase1FSEM01FlatProductMain.hs) parse
real Grammar-v1 functions and call the actual production
`grammarV1CheckedTypeMode` rather than constructing an AST from
guessed type metadata. They test flat arities 2, 3, 4, mixed
unrestricted/linear element types, missing/nested/unknown members, and
actual Surface checks of positive and tampered product-return contracts.
They separately test a Core-supplied affine token mixed with
unrestricted and linear elements, plus duplicate linear owner rejection.
The [original SURF-008 type composition suite](../../test/Phase1GrammarV1IntrinsicTypeCompositionMain.hs)
is updated to recognize the new narrowly admitted checked tuple
while preserving the unsupported intrinsic/bound-route distinctions.

## Formal preservation relation

[SurfaceFlatProductCorrespondence.v](../../proof/Phil/Surface/SurfaceFlatProductCorrespondence.v)
models a finite product contract check over existing Rocq
`DataProduct.ProductElementContract` values. It proves:

- an accepted contract match preserves the **complete ordered list** of
  element types and modes, provided the supplied `Ty` equality predicate
  is sound;
- successful matching preserves arity and every indexed element;
- successful matching preserves the existing Core
  `deriveProductMode` upper-bound property for every element;
- incorrect arity cannot pass, and a reflexive equality predicate accepts
  an unchanged contract.

The proof composes existing `DataMode.v` and `DataProduct.v`
theorems, without adding axioms or admissions.

**Trust boundary:** Rocq's `Ty` remains abstract and the type equality
predicate's soundness is an explicit premise. This is a formal *model*
of the exact-element validation principle, not extraction, a proof
of Haskell `Eq Ty`, or a universal source elaborator/refinement result.
Haskell production and the Rocq relation are independently tested,
not assumed definitionally identical.

## CI and remaining obligations

The existing [FSEM-01 two-owner source workflow](../../.github/workflows/fsem01-two-owner-source.yml)
now also runs the mixed flat-product tests, the previous type-composition
test and exact source-two-owner witnesses, then compiles the new Rocq
theorems in the versioned Rocq container. The established PR-only
supersession policy remains unchanged; main and release runs remain
independent.

Open: full recursive product types, source-level affine type semantics,
verified name/type/value representation across the Haskell/Rocq boundary,
general finite resource contexts, nested borrows, joins, loops, captures,
error-path simulation and discharge of the `satisfies C` contract.
These are not claimed by this slice.
