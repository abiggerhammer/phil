# Phase 1 surface production corpus

This corpus is the declarative target for the canonical Phase 1 source parser.

The authority is `grammar/phase1-surface.ebnf`. These fixtures do **not** make the current Haskell parser normative and do not assert semantic acceptance. They record only whether a complete source file must parse or must fail at the syntax layer.

- `accepted/`: must parse as complete `source_file` inputs. Later elaboration/checking may still reject them.
- `rejected/`: malformed concrete syntax that must be rejected before semantic checking.
- `manifest.json`: machine-readable coverage and expectation metadata for SURF-002 and later parser/grammar correspondence work.

The corpus intentionally covers the Grammar-v1/type-system reconciliation forms independently and in composition: refinement types, explicit transport, native membership/disjointness, term-level `offer`, branch-sensitive callable outcome residues, and exact replacement-callee transitions.
