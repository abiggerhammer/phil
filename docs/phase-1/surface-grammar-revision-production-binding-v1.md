# Phase 1 Surface Grammar Revision production binding v1

`PHIL-SURFACE-REV-001` is target- and parser-implementation-independent at the Certified boundary: one competent grammar-revision record is present, it equals the selected concrete grammar revision, and source payload identity cannot rebind that decision.

This production slice binds those three facts to `Phil.Surface.Lineage` without replacing its parser or diagnostics.

## Native-first boundary

`Phil.Surface.GrammarRevisionCertification.certifyPortableSourceBundleGrammar` first calls the existing `decodePortableSourceBundleForGrammar` implementation. Missing, duplicate, malformed, or incompatible revision records therefore retain their existing `LineageError` diagnostics and fail before the extracted kernel is consulted.

Only native success reaches the exact `GrammarRevisionKernel` staged by #715. At that point:

1. competent revision presence is established by successful native decoding;
2. selected-revision equality is independently reflected from the returned `portableGrammarRevision`; and
3. payload independence is constructional: the kernel-facing grammar certificate path reads no program-root, source-unit, declaration-lineage, instance-lineage, or process-lineage field when deciding grammar identity.

The resulting `CertifiedGrammarRevisionBundle` constructor is opaque outside the certification module.

## Exact kernel

Fresh Rocq extraction must reproduce `GrammarRevisionKernel.hs` byte-for-byte:

- size: 510 bytes;
- SHA-256: `fdf35b8405e79f71763ea2fe342d030e0c5eac8181d9176f3c4815038f049313`;
- checked-in copies: `generated/GrammarRevisionKernel.hs` and `src/GrammarRevisionKernel.hs`.

Both trailing newline bytes are significant.

## Residual boundaries

This binding does not certify SHA-256 collision resistance, the EBNF-to-Rocq derivation script, Haskell `Text` decoding/equality, line-oriented SourceBundle parsing, parser soundness/completeness, or any cross-revision compatibility/migration relation. Those remain explicit tooling, representation, parser, or future-policy boundaries.

The exact kernel may add fail-closed rejection on correspondence disagreement; it cannot convert a native rejection into acceptance.
