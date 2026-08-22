# Steve checker promotion target: opaque digest proof

Status: checker-facing target, not implementation

This note fixes the smallest architecture/static environment required to promote `../rejected/02-prove-opaque-digest.phil` from a parser-valid negative witness to an executable semantic rejection.

The intended result is exactly `OpaqueProof`. The fixture must not be accepted, and it must not fail earlier because a Steve primitive, type alias, constructor, or provider interface is unknown.

## Why the witness is deliberately tiny

The fixture now uses:

```phil
component BadProveDigest(
    id : ContentId[SHA256],
    bytes : OwnedBytes[0]
) provides PutResult[SHA256] {
    let digestEvidence = prove DigestMatches(id, bytes.id)
    ...
}
```

The fixed byte count avoids needing a `Nat` architecture alias just to type the witness. The `bytes.id` projection reuses the checker’s existing `OwnedBytesShape` stable identity, so no `owned_bytes_identity` primitive is needed. The code after `prove` is intentionally irrelevant to this promotion: a correct checker stops at the opaque-proof error before reaching the result constructor.

## Required static declaration

The environment needs exactly one semantic declaration beyond an empty surface environment:

```haskell
DigestMatches(
  id     : SortOpaque "ContentId[SHA256]",
  object : SortStableId "OwnedBytes"
) : opaque claim
```

Equivalently, with the current Core API, the target construction is conceptually:

```haskell
static <- declareOpaqueClaim
  "DigestMatches"
  [ (Name "id", SortOpaque "ContentId[SHA256]")
  , (Name "object", SortStableId "OwnedBytes")
  ]
  emptyStaticContext

environment = emptySurfaceEnvironment static
```

No `surfacePrimitives`, `surfaceInitialBindings`, `surfaceTypeAliases`, select requirements, terminal allowances, or expected-provides override are required for the intended earliest rejection.

## Why those sorts are exact

`ContentId[SHA256]` currently elaborates as the ordinary opaque type `TyOpaque "ContentId[SHA256]"`; `refSortOfTy` therefore exposes it to propositions as `SortOpaque "ContentId[SHA256]"`.

`OwnedBytes[0]` resolves through the existing special `OwnedBytes` surface rule to a linear `TyBytes 0` with `OwnedBytesShape`. The surface elaboration environment already declares the projection `bytes.id` to have sort `SortStableId "OwnedBytes"`.

The claim signature therefore matches the two proposition arguments without any Steve-specific elaboration rule.

## Expected checker path

Once a general environment hook can supply the declaration above, this fixture should follow the existing generic path:

1. Source parameters initialize `id` and linear `bytes` from their explicit source types.
2. `DigestMatches(id, bytes.id)` elaborates and sort-checks against the declared opaque claim signature.
3. `focusProposition` classifies the unresolved opaque claim as `FocusNeedsExplicitMechanism`.
4. Generic `prove` rejects it as `OpaqueProof` with the existing diagnostic `opaque claim cannot be introduced by generic prove`.
5. The harness compares the resulting stable rejection class with the fixture expectation `FixtureReject OpaqueProof`.

Nothing in that path requires a Steve-specific Core rule.

## Promotion acceptance criteria

Promotion is complete only when all of the following are true:

- the fixture still parses through `phil-core -- parse`;
- a general checker harness supplies the static declaration without filename-specific logic in the checker;
- checking reaches `prove`, rather than failing on an unrelated unknown type/primitive;
- the observed rejection class is exactly `OpaqueProof`;
- the existing Phase 0 upload conformance corpus remains unchanged and green;
- no new Phil ADR is introduced merely to support this fixture.

## Explicit non-goals

This promotion does not require `DigestProvider`, `BlobProvider`, generic result variants, ownership-bearing result constructors, provider member syntax, or executable `DigestMatches` validation. Those belong to later Steve promotions.

In particular, this fixture tests only the negative rule: declaring a claim opaque does not grant source code authority to manufacture evidence for it.
