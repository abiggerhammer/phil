# Phase 1 warning-free Haskell integration

INT-010 requires project-owned Phase 1 Haskell to compile under one canonical strict warning policy before freeze.

The canonical integration signal is:

```text
cabal build all --enable-tests --ghc-options=-Werror
```

The project Cabal common settings already enable `-Wall`, `-Wcompat`, `-Wincomplete-record-updates`, `-Wincomplete-uni-patterns`, and `-Wredundant-constraints`; `-Werror` makes those selected warnings fatal for the complete project-owned build.

The permanent `Phase 1 Warning-Free Haskell Integration` workflow also recompiles the historically suppressed SYS-009/010 cumulative seams directly with `-Wall -Werror` and no `-Wno-*` exemptions. This gives INT-010 an explicit regression signal before the old focused-workflow suppressions are deleted.

## Deliberate exclusions

Rocq-generated/extracted Haskell sometimes carries generator-owned naming or import artifacts. Existing production mirrors may therefore contain narrowly scoped module-local `OPTIONS_GHC -Wno-*` pragmas where a correspondence workflow mechanically constrains the mirror to the exact extraction plus that pragma. Those are declared extraction/toolchain boundaries, not project-owned source warning debt, and this slice does not rewrite generated kernels merely to satisfy a source-style preference.

The next INT-010 cleanup slices may remove historical focused-workflow suppressions once this strict cumulative gate demonstrates that the underlying project-owned modules and tests no longer require them.
