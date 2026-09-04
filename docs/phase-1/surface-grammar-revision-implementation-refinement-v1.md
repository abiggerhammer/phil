# Phase 1 Surface Grammar Revision implementation refinement v1

This slice stages machine implementation refinement for `PHIL-SURFACE-REV-001`.
It does not change the portable SourceBundle format or production `Phil.Surface.Lineage` behavior.

## Certified boundary

`proof/Phil/Surface/GrammarRevision.v` already establishes exact concrete-grammar revision binding:

- the canonical Phase-1 revision is `sha256:` plus the digest carried by the deterministically derived `Grammar.v` artifact;
- one present exact selected revision is admitted;
- missing, duplicate, malformed, and incompatible revision records reject;
- an accepted bundle retains the selected revision;
- source payload identity cannot rebind the grammar revision; and
- a different revision requires a new explicit compatibility/migration policy rather than implicit admission.

## Machine-facing facts

`GrammarRevisionImplementation.v` factors the accepted binding into exactly three representation-neutral facts:

1. one competent revision record has been successfully parsed and is present;
2. its revision is exactly the selected revision; and
3. source payload identity cannot change the grammar-binding decision.

`decideGrammarRevisionBindingByFacts` is extracted to `GrammarRevisionKernel.hs` and fails closed unless all three facts hold.

The first fact deliberately absorbs native missing/duplicate/malformed parsing competence. The extracted kernel does not reproduce line parsing or diagnostic precedence. The second fact owns exact selected-revision equality. The third makes the already-proved no-payload-rebinding theorem visible at the implementation boundary and supports explicit injected-disagreement testing.

## Native staging authority

Production remains `src/Phil/Surface/Lineage.hs` during this staging slice. In particular:

- `validateGrammarRevision` owns concrete lowercase `sha256:` syntax validation;
- `decodeRecord` owns missing/duplicate grammar-record diagnostics;
- `decodePortableSourceBundleForGrammar` owns concrete `Text` equality and native error ordering;
- `canonicalGrammarRevisionV1` remains the concrete selected revision; and
- `resolveSourceBundleLineage` remains downstream of successful bundle decoding.

The existing `Phase1GrammarRevisionBindingMain.hs` recomputes SHA-256 over `grammar/phase1-surface.ebnf` and checks the concrete canonical revision. The unchanged portable-lineage corpus continues to verify that source presentation and carrier form cannot recompute semantic lineage.

## Staging controls

The direct extracted-kernel harness checks:

- exact competent payload-independent binding accepts;
- missing/duplicate/malformed competence rejects;
- incompatible selected revision rejects; and
- an injected payload-rebinding disagreement rejects.

The existing SURF-006 revision corpus and SURF-010 portable-lineage corpus are rerun unchanged.

## Residual boundaries

This staging slice does not certify SHA-256 collision resistance, Python EBNF-to-Rocq derivation correctness, concrete UTF-8/Text decoding, `Text` equality, line-oriented SourceBundle parsing, Haskell diagnostic payload identity/order, parser soundness/completeness, or any cross-revision semantic compatibility relation. Those remain explicit tooling, representation, native, or future-policy boundaries.

A later production-binding slice must fresh-extract the exact kernel and route successful production grammar admission through it before `PHIL-SURFACE-REV-001` can be promoted to **Implementation Refined**.
