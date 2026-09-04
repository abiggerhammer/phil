# Phase 1 surface determinacy: pattern resolver soundness v1

This slice continues `PHIL-SURFACE-DETERM-001` after the qualified-name commitment proof.

The `pattern` grammar has one structural FIRST overlap on `IDENTIFIER`: a plain `identifier` and a `record_pattern` can both begin there. The resolver distinguishes them by looking past the initial identifier. A maximal qualified name followed by `{` commits the record-pattern branch; otherwise an accepting plain-identifier continuation commits the identifier branch.

The Rocq proof establishes:

- the computed Grammar-v1 `FOLLOW(pattern)` set excludes both `.` and `{`;
- therefore an accepting continuation after a completed identifier pattern cannot begin with either token;
- exact identifier token consumption plus the scanner lemmas forces `pattern_decision` to choose branch 0 for every such ordinary derivation; and
- together with the already-proved record-pattern commitment, both sides of the structural `pattern` overlap are semantically bound to the certified resolver decision.

The remaining structural overlap families are the parenthesis comma/close decisions, brace-led static arguments, and explicit top-level relation operators in proposition atoms.
