# FSEM-01 — bounded declaration identity representation bridge

> **Review status:** this file describes a bounded, **non-normative**
> source-to-model representation relation, not a global correspondence theorem.
> Tracks [issue #1613](https://github.com/abiggerhammer/phil/issues/1613).
> It builds on the [binder-name encoding proof](formal-semantics-binder-name-encoding-fsem01-v1.md).

## The identity mismatch we must not hide

Production
[Static.hs](../../src/Phil/Core/Static.hs) defines:

- `DeclarationKey` as an exact `Data.Text` root (its `Eq` and `Ord`
  are about the root, *not* the human-facing presentation).
- `DeclarationIdentity` as a triple:
  `identityDeclarationKey`, `identityInterfaceRevision`,
  `identityDefinitionRevision`.
- `deriveDeclarationIdentity` preserves the declaration key and derives
  the two revisions from canonical checked semantics. Presentation-only
  changes do not contribute to that triple.

[BinderScope.hs](../../src/Phil/Surface/GrammarV1/BinderScope.hs)
uses **only the declaration key root and the declaration-wide binder
ordinal** in its `GrammarV1BinderKey`. The revisions are not appended to
that binder key.

By contrast, [BindingSemantics.v](../../proof/Phil/Core/BindingSemantics.v)
models a local-binder declaration identity as a natural number. The
number **does not by itself represent the complete production
DeclarationIdentity triple**. #1631 proved the canonical name-encoding
shape for Rocq strings but left the root representation injection as an
assumption.

## Exact bounded relation

The
[SurfaceDeclarationIdentityBridge.v](../../proof/Phil/Surface/SurfaceDeclarationIdentityBridge.v)
model uses one **ordered finite catalog** of Rocq strings. It defines:

~~~text
representsDeclarationRoot catalog modelId concreteRoot :=
    nth_error catalog modelId = Some concreteRoot
~~~

`indexDeclarationRoot` finds a root in the catalog, returning an
`option nat`. A missing root is **not** assigned an invented model id.
`NoDup catalog` is a stated proof precondition. This catalog is a
*proof/observation environment*, **not a persistent identity service**.

| Proof | Established property |
| --- | --- |
| `catalog_index_sound` | Successful lookup points to exactly the given catalog root |
| `catalog_index_complete` / `catalog_position_roundtrip` | Under `NoDup`, every represented catalog position is found at its exact index |
| `catalog_root_roundtrip` | A successful lookup has the corresponding root at its returned index |
| `distinct_catalog_positions_have_distinct_roots` | Under `NoDup`, one concrete root cannot stand for two model indices |
| `represented_binder_encoding_preserves_exact_model_identity` | Under `NoDup` and *explicit* root and ordinal representation premises, equal canonical Core-name model strings imply equal normalized binder keys |

This discharges **root injection within one admitted, duplicate-free
catalog**, composing #1631's `encode_text_binder_key_injective` with a
reversible relation from normalized `(nat,nat)` keys to represented
`(string,nat)` keys. It does **not** construct a universal
`declarationText : nat -> string` with a proof of injection over all
natural numbers. In particular, no proof about out-of-range positions
or about *independent catalog orderings* is silently introduced.

## Executable Haskell correspondence witness

[Phase1FSEM01DeclarationBridgeMain.hs](../../test/Phase1FSEM01DeclarationBridgeMain.hs)
builds an explicit finite dictionary from actual `DeclarationKey`
values returned by production `deriveDeclarationIdentity`. A duplicate
root causes failure; an unlisted root or out-of-range model id returns
`Nothing`. The test observes the **existing production**
`grammarV1BinderCoreName` and its canonical decoder, then relates the
decoded root/ordinal to the catalog index:

- exact dictionary forward/reverse roundtrips for known keys;
- injective observations of binder Core names over roots and ordinals;
- exact distinction between revisions and declaration roots, including
  a body revision that changes the definition revision but preserves
  the root, and presentation changes that preserve identity;
- duplicate-root refusal and unknown-root refusal;
- a deliberate **catalog reorder** that changes the model number,
  while leaving production `Core.Name` unchanged;
- Unicode/delimiter-looking roots as Haskell `Text` values.

The dictionary is intentionally **test-only**, not a replacement for
Phil's persisted declaration lineage. It is an executable witness for
an admitted finite corpus, **not proof of the implementation of all
Text or Map operations**.

The dedicated
[CI workflow](../../.github/workflows/fsem01-declaration-identity-bridge.yml)
compiles the existing binder-name theorem and the new bridge with
Rocq 9.2, rejects global admissions in the new file, and strict-checks
and executes the Haskell tests using the actual library. Claims about
passing checks are valid only on the exact PR commit SHA.

## Remaining explicit proof obligations

1. **Catalog authority and stability.** A catalog must be bound to a
   specified source/program version and have verified `NoDup` roots;
   inserting, removing or reordering entries changes normalized model ids.
   Do not use catalog positions as persistent identifiers.
2. **Unicode representation.** Haskell `Text` and Rocq `String` are
   different carriers. Theorem-level correspondence still needs an
   explicit encoding (e.g. a byte-level representation) and checked
   injectivity/length relation. Unicode cases here are tests only.
3. **Declaration revision semantics.** The root-only relation is
   suitable for local binder identity, *not* complete
   `DeclarationIdentity` equality, which also includes interface and
   definition revisions.
4. **Full source-to-model simulation.** The catalog bridge does not
   certify production finite maps, the borrow runtime value tree,
   loan begin/end, `BorrowEscape`, or source-level
   `satisfies C`. #1626's traces and #1627's conditional loan model
   remain distinct until those obligations are actually discharged.

**Next bounded step:** bind the catalog to an exact source-derived
production trace and show that model owner identity and loan-membership
transitions commute across each recorded checkpoint, with a separate
negative-path correspondence theorem. Avoid reclassifying terminal
return as a continuing join.
