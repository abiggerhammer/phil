# Phase 1 surface parser production corpus v1

## Purpose

This corpus fixes concrete parser expectations for Grammar-v1 forms introduced or repaired by the Phase 1 surface reconciliations. It is a specification target for SURF-002, not evidence that the current Haskell parser already implements Grammar v1.

## Authority and competence

`grammar/phase1-surface.ebnf` remains the sole concrete-syntax authority. The fixtures under `test/fixtures/phase1-surface/` are examples classified against that grammar.

An `accepted` fixture asserts only that a conforming parser consumes the whole file and produces a surface structure. It does **not** assert that name resolution, elaboration, typing, resource checking, assurance, or lowering succeeds.

A `rejected` fixture is deliberately malformed so rejection belongs at the syntax layer. A parser must not accept it and rely on a later semantic checker to notice the problem.

## Coverage

The corpus covers the six grammar/type-system reconciliation areas independently:

1. refinement types `{x : T | P}`;
2. explicit transport `transport e to T using p`;
3. native finite membership and disjointness propositions;
4. term-level `offer`;
5. branch-sensitive callable `outcome T { ... }` residue blocks; and
6. exact `replace with ... [state ...]` callee transitions.

It also includes three positive composition cases so parser coverage is not limited to isolated productions: refinement plus transport, offer plus transport, and outcome residues carrying a refinement type.

The structural-mode reconciliation is covered separately at the declaration boundary. Positive syntax cases include an explicitly linear record, an explicitly affine sum, capabilities using each of `unrestricted`, `affine`, and `linear`, and ordinary owning bindings with no binder-local mode qualifier. Syntax-negative cases cover a missing mode literal, an unknown mode literal, an illegal binder-local mode spelling, and an illegal mode clause on a transparent type alias. These fixtures assert syntax only; strengthening/no-weakening and binding-zone behavior remain semantic checker obligations.

## Manifest

`manifest.json` is the machine-readable integration point for the future canonical Haskell parser harness. Each row has a stable corpus ID, relative path, parse expectation, grammar productions exercised, and whether semantic checking is deferred.

SURF-002 implementation should consume this manifest rather than duplicating the fixture list in Haskell. Whole-file consumption is mandatory. The harness should report the fixture ID and path on disagreement.

## Deliberate non-goals

This corpus does not:

- define semantic acceptance;
- prescribe the future surface AST shape;
- require a particular parser library or backtracking strategy;
- duplicate Grammar v1 as another grammar;
- add parser recovery behavior; or
- claim parser/grammar soundness or completeness by testing alone.

The later parser-correspondence proof/certificate remains responsible for the stronger SURF obligation. The corpus is executable pressure and regression evidence for that work.
