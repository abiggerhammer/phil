# Phase 1 surface determinacy: delimiter balance v1

This tranche continues `PHIL-SURFACE-DETERM-001` after #658 established reusable scanner mechanics for the eight structural overlap sites.

The remaining structural resolvers inspect tokens at their current delimiter depth. Their grammar-soundness proof therefore needs a global fact that nested nonterminal calls cannot leak an unmatched `(`, `[`, `{`, `)`, `]`, or `}` into the caller's scanner state.

`proof/Phil/Surface/GrammarDeterminacyDelimiterBalance.v` provides that fact in two layers:

- a finite abstract interpreter checks that every generated Grammar-v1 rule body is delimiter-balanced when nonterminal references are assumed balanced; and
- a mutual induction over ordinary `Derives`, `DerivesSequence`, and `DerivesRepetition` evidence proves that checked abstract effect sound for actual token consumption.

The recursive case is justified by derivation structure rather than parser implementation: the selected nonterminal body is a smaller derivation, while the exact generated rule-table certificate supplies the body balance equation. A shift lemma shows balance is stable at arbitrary surrounding delimiter depth.

The exported corollary states that every ordinary derivation of any Grammar-v1 nonterminal consumes a prefix whose delimiter scan starts and ends at depth zero. This is the reusable fact the structural resolver proof needs when skipping nested calls at positive scanner depth.

This tranche does **not** yet discharge the eight structural resolver sites. The successor proof combines delimiter balance with #658's comma/close and relation scanner invariants to show that ordinary derivations of `pattern`, `primary_expression`, `static_argument`, and `proposition_atom` force the certified structural resolver decisions.

Baseline: #658 merged as `d9042dc7af97e71e06d05f3f132f34c83ce3c2cb`.
