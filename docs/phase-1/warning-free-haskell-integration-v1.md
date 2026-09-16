# Phase 1 warning-free Haskell integration

INT-010 requires project-owned Phase 1 Haskell to compile under one canonical strict warning policy before freeze.

The canonical integration signal is:

```text
cabal build all --enable-tests --ghc-options=-Werror
```

The project Cabal common settings already enable `-Wall`, `-Wcompat`, `-Wincomplete-record-updates`, `-Wincomplete-uni-patterns`, and `-Wredundant-constraints`; `-Werror` makes those selected warnings fatal for the complete project-owned build.

The permanent `Phase 1 Warning-Free Haskell Integration` workflow also recompiles historically suppressed cumulative seams directly with `-Wall -Werror` and no `-Wno-*` exemptions. Focused proof and production-binding workflows have been audited so project-authored `src/`, `app/`, and `test/` code no longer inherits an extractor-only warning suppression.

When a project-authored correspondence executable imports a raw extracted kernel, the workflow keeps the warning boundary explicit: the exact kernel is compiled separately under its narrow generator-owned exception, the authored executable is compiled under plain `-Wall -Werror`, and the resulting objects are linked. This avoids GHC silently recompiling the extracted dependency under the authored warning policy while still proving that the authored code is warning-clean.

## Surviving exceptions

A Phase 1 `-Wno-*` exception is allowed only when all of the following hold:

1. the affected module is exact extractor/generated output, or a production mirror mechanically constrained to equal that output plus the documented compiler pragma;
2. the exception names only the extractor-owned warning actually required;
3. no project-authored `src/`, `app/`, or `test/` module shares the exception merely because it imports the generated module; and
4. the dedicated workflow keeps every other selected warning fatal and checks the relevant extraction or mirror identity.

The current survivors fall into two generator-owned classes.

### Unused imports from Rocq extraction

Rocq extraction can emit qualified `Prelude` imports that are unused by GHC. Dedicated proof workflows retain narrow `-Wno-unused-imports` handling only for exact extracted kernels, including the Runtime Carrier, Storage Realization, Storage Allocation Failure, Storage Cost Attribution, Storage Terminal Closure, Generic Requirement Category, Generic Static Kind, Callable Outcome, Callable Mode Strengthening, Deployment Qualification, Deployment Authority, Assurance Evidence Authority, Concurrency Activation/Rendezvous/Terminal, Systems Evidence Preservation, and Systems Revision Canonicalization kernels.

Checked-in production mirrors with a module-local unused-import exception are mechanically constrained to the exact extraction plus that pragma. Current examples are:

- `src/ArchitectureRealizationKernel.hs`;
- `src/ArchitectureRevisionConstructionKernel.hs`;
- `src/SystemsEvidencePreservationKernel.hs`;
- `src/SystemsRevisionCanonicalizationKernel.hs`.

### Name shadowing from surface-grammar extraction

Some extracted surface-grammar kernels contain nested helper names that GHC reports as shadowing. Their production mirrors or dedicated generated-kernel checks retain narrow `-Wno-name-shadowing` handling, including `src/SurfaceGrammarRecognizerKernel.hs`, `src/SurfaceGrammarAstRepresentationKernel.hs`, and the compact AST carrier kernels exercised by the surface-grammar production-binding workflows. Those exceptions are generator-owned and mechanically checked against the corresponding extraction.

## INT-010 closeout condition

Project-owned Haskell code is warning-clean under the canonical strict gate. Remaining `-Wno-*` uses are extraction/toolchain boundaries satisfying the criteria above, not project-owned warning debt. Any future suppression added to authored Phase 1 Haskell reopens INT-010-style warning debt and must be justified or removed rather than inherited transitively from a generated dependency.
