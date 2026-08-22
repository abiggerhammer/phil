# Steve checker promotion: opaque digest proof

Status: promoted to branch-local semantic CI

`../rejected/02-prove-opaque-digest.phil` is now Steve's first executable checker-level negative witness. The branch-local harness `test/SteveSurfaceSemanticMain.hs` supplies the smallest generic static environment required by the source and requires the existing surface checker to reject the program with exactly `OpaqueProof`.

No Steve-specific Core rule, filename switch, primitive, provider implementation, or result-constructor semantics were added for this promotion.

## Why the witness is deliberately tiny

The fixture uses:

```phil
component BadProveDigest(
    id : ContentId[SHA256],
    bytes : OwnedBytes[0]
) provides PutResult[SHA256] {
    let digestEvidence = prove DigestMatches(id, bytes.id)
    ...
}
```

The fixed byte count avoids needing a `Nat` architecture alias just to type the witness. The `bytes.id` projection reuses the checker's existing `OwnedBytesShape` stable identity, so no `owned_bytes_identity` primitive is needed. The code after `prove` is intentionally irrelevant: a correct checker stops at the opaque-proof error before reaching the result constructor.

## Static declaration supplied by the harness

The environment contains exactly one semantic declaration beyond an empty surface environment:

```haskell
static <- declareOpaqueClaim
  "DigestMatches"
  [ (Name "id", SortOpaque "ContentId[SHA256]")
  , (Name "object", SortStableId "OwnedBytes")
  ]
  emptyStaticContext

environment = emptySurfaceEnvironment static
```

No `surfacePrimitives`, `surfaceInitialBindings`, `surfaceTypeAliases`, select requirements, terminal allowances, or expected-provides override are supplied.

## Why those sorts are exact

`ContentId[SHA256]` elaborates as the ordinary opaque type `TyOpaque "ContentId[SHA256]"`; `refSortOfTy` therefore exposes it to propositions as `SortOpaque "ContentId[SHA256]"`.

`OwnedBytes[0]` resolves through the existing special `OwnedBytes` surface rule to a linear byte owner with `OwnedBytesShape`. The elaboration environment exposes `bytes.id` as `SortStableId "OwnedBytes"`.

The claim signature therefore matches the two proposition arguments without a Steve-specific elaboration rule.

## Checked path

The semantic test exercises the generic path:

1. Source parameters initialize `id` and linear `bytes` from their explicit source types.
2. `DigestMatches(id, bytes.id)` elaborates and sort-checks against the declared opaque claim signature.
3. `focusProposition` classifies the unresolved opaque claim as requiring an explicit mechanism.
4. Generic `prove` rejects it as `OpaqueProof` with the existing opaque-claim diagnostic.
5. The harness fails unless the observed stable rejection class is exactly `OpaqueProof`.

The ordinary branch CI still parses the entire Steve surface corpus separately, so this promotion adds semantic specificity without replacing the parser gate.

## What this promotion establishes

This witness establishes one narrow negative rule: **declaring a claim opaque does not grant source code authority to manufacture evidence for it.**

It does not establish executable `DigestMatches` validation, DigestProvider or BlobProvider semantics, generic result variants, ownership-bearing result constructors, or a complete Steve semantic environment. Those remain later promotion targets.

## Regression requirements

Keep the promotion only while all of the following remain true:

- the fixture parses;
- the harness constructs the environment through the public generic Core/surface APIs;
- checking reaches `prove` rather than failing on unrelated unknown machinery;
- the rejection class is exactly `OpaqueProof`;
- the Phase 0 upload conformance corpus remains unchanged and green;
- no Phil ADR or Steve-specific checker branch is introduced for this witness.
