# Phase 1 surface determinacy v1

## Status

Executable conformance boundary for Matrix case `SURF-005` and supporting evidence for `PHIL-SURFACE-DETERM-001`.

The normative concrete-syntax authority remains `grammar/phase1-surface.ebnf`. This note does not create a second grammar and does not claim a language-wide unambiguity theorem.

## Required property

An accepted Grammar-v1 source must have one concrete located surface structure modulo explicitly nonsemantic trivia. Parser alternative order, backtracking, or recovery policy must not choose between semantically distinct parses of the same source bytes.

That is stronger than observing that the current Haskell parser is a deterministic function.

## Executable ambiguity inventory

`scripts/check_phase1_surface_determinacy.py` imports the same typed EBNF representation used by the canonical derivation path and computes:

- nullable nonterminals;
- FIRST token sets;
- FOLLOW token sets;
- FIRST/FIRST overlap between grammar alternatives;
- FIRST/FOLLOW overlap at optional and repetition boundaries; and
- rejection of nullable repetition bodies.

The resulting local-overlap surface is checked against `grammar/phase1-surface-determinacy.json`.

An overlap is not automatically a language ambiguity. For example, two declaration forms may share an initial keyword while a later mandatory token distinguishes them. It is, however, a place where one-token dispatch alone is insufficient and where a parser implementation could accidentally make meaning depend on alternative order or backtracking. Every such overlap therefore requires an explicit reviewed disposition in the inventory.

Any Grammar-v1 revision that changes the local-overlap set fails the surface-grammar workflow until the determinacy inventory is deliberately reviewed and rebound to the new exact grammar digest.

## Exact parser-shape pressure

`test/Phase1GrammarV1DeterminacyMain.hs` exercises representative high-risk surfaces and requires distinct located AST constructors rather than mere parse success. The initial pressure includes:

- declaration forms sharing prefixes, including optional record/data mode clauses and mandatory capability mode;
- provider contract versus provider implementation versus opaque provider implementation;
- brace-led static effect-set actuals versus brace-led refinement-type actuals;
- parenthesized static values versus tuple types; and
- keyword-led session expressions versus name-shaped static session references.

Existing Grammar-v1 harnesses provide additional exact-shape pressure for relation operators, callable outcome residues, expression precedence/fallbacks, static-reference arguments, and the remaining production families.

## Competence boundary

This SURF-005 slice establishes a reproducible ambiguity-review inventory plus differential/exact-shape implementation pressure. It does **not** by itself prove that no arbitrarily long accepted token sequence has two EBNF derivations.

The stronger `PHIL-SURFACE-DETERM-001` proof obligation remains the place for a language-wide unambiguity/determinate-parse theorem over the admitted lexical/syntactic model. Concrete lexer/parser-library correspondence also remains an explicit implementation boundary until separately tightened.

This separation is intentional: the Matrix case can be executable and regression-resistant without overstating what finite tests or local FIRST/FOLLOW analysis prove.
