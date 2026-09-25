# Phase 1 audit remediation: numeric admission boundary

Status: implementation-side defensive audit remediation.

This slice answers the bounded production-adapter question left open by the
2026-09-25 numeric environment/result-subject audit. It does not add a new
numeric language feature and does not claim a generalized Phase-2 compiler
pipeline.

## Environment admission

`GrammarV1AdmittedNumericValues` is an explicit competent-caller boundary.
The caller supplies already admitted `NumericValue` values keyed by semantic
Core `Name`. The production adapter accepts the exact
`GrammarV1CheckedLexicalReference` occurrences produced by lexical scope
checking and uses those same occurrences for both:

1. exact source-occurrence rewriting to the resolved semantic binder name; and
2. construction of the bounded `GrammarV1NumericEnvironment`.

Display spelling is therefore not authority. Alpha renaming that preserves the
same declaration-rooted binder identity preserves admission; equal spelling in a
different declaration root or sibling lexical scope does not. A missing
semantic-name value fails closed. Forward-reference and out-of-scope decisions
remain owned by the existing lexical-reference checker.

The supplied map remains an explicit Phase-1 trust boundary: this slice does not
claim that every source compiler path now manufactures numeric values, nor does
it infer width, sign, or magnitude from names. Those values must already have
been produced by a competent contextual admission path.

## Result admission

For UInt results, `checkGrammarV1UIntNumericResult` copies the exact width and
magnitude returned by the numeric evaluator into the existing Core `VUInt`
literal path and immediately delegates to `checkValue`. The authentic Core
checker therefore creates the `TyUInt` and `RefUInt` subject used by
refinements and dependent consumers. There is no independently supplied result
term and no same-typed-variable substitution.

`evaluateAndCheckGrammarV1UIntNumericExpression` composes the checked lexical
environment adapter, the existing evaluator, and that UInt result admission in
one supported call.

Core currently has no corresponding signed-integer or floating literal
`Value` constructor, so this Phase-1 adapter rejects those result domains
rather than inventing a second representation boundary.

## Preserved boundaries

This adapter does not restore affine or linear ownership, create proof evidence,
discharge residual obligations, infer checked rebases, or turn numeric
interpretability into resource authority. Existing conversion, range,
lexical-scope, refinement, and dependent-index checks remain the competent
owners of those decisions.

No Rocq file is changed by this remediation. LLVM remains inside the Phase-1
trusted computing base and is outside this slice.

Lane: impl-audit
