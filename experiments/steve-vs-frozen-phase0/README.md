# Steve against frozen Phase 0

This branch is an expected-failure baseline experiment for Phase 1.

Base: Phase 0 closure commit `911f6f73d9fd7c788f081fe616ad640b83fb882e`.

Rules for this experiment:

- do not modify Phase 0 implementation semantics to make Steve pass;
- do not add Steve-specific compiler/checker primitives merely to move the failure deeper;
- use the smallest faithful Steve source sketch that stays within syntax already represented by the frozen parser;
- record the first competent boundary that prevents Steve from travelling the Phase 0 source-to-native path.

The probe performs two steps in order:

1. parse `examples/steve/steve.phil` with the frozen Phase 0 parser;
2. ask the frozen Phase 0 surface machinery for the semantic checking environment for that source file.

The expected baseline is:

- syntax: accepted;
- semantic entry: stopped before whole-component checking because `Phil.Surface.Phase0.phase0EnvironmentFor` only supplies environments for the named Phase 0 upload fixtures and rejected witnesses.

If confirmed by CI, this is the earliest concrete Phase 1 generalization boundary: Steve is expressible in the existing concrete syntax, but the frozen semantic front end still requires program/fixture-specific environment construction. Later Phase 1 work should make architecture/static-signature declarations ordinary source-level inputs rather than adding a Steve case to `phase0EnvironmentFor`.

This result is intentionally narrower than the other known Steve pressure points. Provider interfaces, multi-operation stores, generic sum/record results carrying owned resources, architecture-declared `DigestMatches`, generic Systems lowering, and backend realization remain later boundaries to test after the semantic environment becomes generic.
