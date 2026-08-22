# Steve checker promotion: opaque digest proof

Status: promoted to branch-local semantic CI

`../rejected/02-prove-opaque-digest.phil` is Steve's first executable checker-level negative witness. The branch-local harness `test/SteveSurfaceSemanticMain.hs` supplies a generic architecture environment and requires the existing surface checker to reject the program with exactly `OpaqueProof`.

No Steve-specific Core rule, filename switch, primitive, provider implementation, or result-constructor semantics are involved.

## Why the witness is deliberately tiny

The promoted fixture is:

```phil
component BadProveDigest(
    id : ContentId[SHA256],
    object
) provides Unit {
    let digestEvidence = prove DigestMatches(id, object)
    return unit
}
```

`id` uses an ordinary source type. `object` is intentionally untyped in source and supplied by the architecture environment as a stable byte-object identity. That keeps this test focused on the generic opaque-proof rule rather than depending on any Steve-specific source representation for stable identities.

An earlier draft used `bytes.id` from `OwnedBytes[0]`. CI correctly rejected that before focusing: `OwnedBytes` elaborates to a finite byte sequence, and `.id` is not currently a legal generic refinement projection on that representation. The promotion therefore makes the stable identity explicit at the architecture boundary instead of inventing a projection rule merely to make the fixture pass.

## Generic environment supplied by the harness

The static context declares one opaque claim:

```haskell
static <- declareOpaqueClaim
  "DigestMatches"
  [ (Name "id", SortOpaque "ContentId[SHA256]")
  , (Name "object", SortStableId "OwnedBytes")
  ]
  emptyStaticContext
```

The surface environment also supplies the untyped `object` parameter as an unrestricted sorted opaque value whose refinement sort is that stable identity sort:

```haskell
environment =
  (emptySurfaceEnvironment static)
    { surfaceInitialBindings = Map.singleton
        "object"
        InitialBinding
          { initialMode = Unrestricted
          , initialType = TyOpaqueSorted
              "OwnedBytesIdentity"
              (SortStableId "OwnedBytes")
          , initialShape = PlainShape
          }
    }
```

This remains generic architecture data. The checker itself knows nothing about Steve or this filename.

## Checked path

1. `id` elaborates to the opaque refinement sort `ContentId[SHA256]`.
2. The untyped `object` parameter resolves against the architecture-supplied stable-ID binding.
3. `DigestMatches(id, object)` elaborates and sort-checks against the opaque claim signature.
4. `focusProposition` classifies the unresolved opaque claim as requiring an explicit mechanism.
5. Generic `prove` rejects it as `OpaqueProof`.
6. The harness fails unless the observed stable rejection class is exactly `OpaqueProof`.

The ordinary branch CI still parses the entire Steve surface corpus separately, so this promotion adds semantic specificity without replacing the parser gate.

## What this promotion establishes

This witness establishes one narrow negative rule: **declaring a claim opaque does not grant source code authority to manufacture evidence for it.**

It does not establish executable `DigestMatches` validation, DigestProvider or BlobProvider semantics, generic result variants, ownership-bearing result constructors, or a complete Steve semantic environment. Those remain later promotion targets.

## Regression requirements

Keep the promotion only while all of the following remain true:

- the fixture parses;
- the harness constructs the environment through public generic Core/surface APIs;
- checking reaches `prove` rather than failing on unrelated unknown machinery;
- the rejection class is exactly `OpaqueProof`;
- the Phase 0 upload conformance corpus remains unchanged and green;
- no Phil ADR or Steve-specific checker branch is introduced for this witness.
