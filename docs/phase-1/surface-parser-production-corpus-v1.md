# Phase 1 surface parser production corpus v1

## Purpose

This corpus fixes concrete parser expectations for the canonical Grammar-v1 surface. It is executable pressure for both:

- SURF-002 positive Grammar-v1 production coverage; and
- SURF-003 malformed, lexical, trailing-input, and explicit-non-goal rejection.

It remains example-based conformance evidence rather than a replacement for the stronger parser/grammar correspondence obligations.

## Authority and competence

`grammar/phase1-surface.ebnf` remains the sole concrete-syntax authority. The fixtures under `test/fixtures/phase1-surface/` are examples classified against that grammar.

An `accepted` fixture asserts only that the canonical parser consumes the whole file and produces a located surface structure. It does **not** assert that name resolution, elaboration, typing, resource checking, assurance, or lowering succeeds.

A `rejected` fixture is a nonmember of Grammar v1 whose rejection belongs at the lexical or syntax layer. The parser must not accept it and rely on a later semantic checker to notice the problem.

## Positive coverage

The grammar/type-system reconciliation cases cover refinement types, explicit transport, native finite membership/disjointness, term-level `offer`, branch-sensitive callable residues, exact replacement callees, and composition among those forms.

The structural-mode reconciliation covers declaration-level mode spelling for records/sums, all three explicit capability possession modes, ordinary type-derived binding mode, and syntax-negative attempts to put mode in the wrong place.

The broader syntax/semantics completeness pass adds parser pressure for static `Type` and `Session` actuals, the admitted generic-requirement categories, specialized static references, tuples, explicit callable outcome classes and residual obligations, closure mode, join invariants, typed loop state, standalone `reject`, and the bounded ADR-024 static process-network surface including explicit external protocol participation.

Parseability never establishes the semantic facts named by these forms. Semantic no-weakening, kind/sort correctness, resource projection, session duality, authority possession, process target validity, external-boundary closure, assurance validity, and related judgments remain checker obligations.

## SURF-003 negative coverage

The original nearby malformed cases remain in the corpus for repaired production families. The SURF-003 closure slice additionally makes the following whole-file boundaries executable through the same canonical Haskell parser harness:

- nontrivia trailing input after an otherwise complete Grammar-v1 source;
- an invalid string escape rejected by the Grammar-v1 lexer;
- the deliberately absent general `unsafe` and `unchecked` block spellings;
- deliberately absent term-level `spawn` and `await` block spellings;
- source assignment/mutable-local syntax;
- exception-style `try`/`catch` syntax;
- shared-memory `atomic` block syntax;
- source `malloc`/placement syntax; and
- macro and reflection syntax.

These explicit-non-goal examples are smoke tests, not a finite definition of invalid Phil. Grammar v1 plus complete-input parser correspondence remains the authority for rejecting every nonmember string.

The current manifest contains **64 fixtures: 28 accepted whole-file examples and 36 syntax-negative examples**.

## Manifest and executable harness

`manifest.json` is the machine-readable integration point for the canonical Haskell parser harness. Each row has a stable corpus ID, relative path, parse expectation, grammar/negative boundary exercised, and whether semantic checking is deferred.

`scripts/check_phase1_surface_corpus.py` validates the manifest/file bijection and emits the validated rows as a narrow TSV stream. `test/Phase1GrammarV1CorpusMain.hs` feeds every emitted row through `parseGrammarV1StructuralSource`, preserving whole-file consumption and reporting both stable corpus ID and fixture path on disagreement.

The integrity checker also requires the SURF-003 closure categories to remain represented, so deleting an audit negative together with its manifest row cannot silently weaken the gate.

## Deliberate non-goals

This corpus does not:

- define semantic acceptance;
- replace Grammar v1 with a second grammar;
- prove parser soundness, completeness, or language-wide unambiguity by testing alone;
- prescribe parser recovery or backtracking strategy; or
- expose deliberately absent implementation/runtime mechanisms merely so they can be rejected semantically later.

The semantic-to-surface classification is recorded in `syntax-semantics-completeness-v1.md`. SURF-005 retains determinate concrete interpretation, SURF-006 retains exact grammar-revision binding, and SURF-008 retains source-to-semantic elaboration correspondence.
