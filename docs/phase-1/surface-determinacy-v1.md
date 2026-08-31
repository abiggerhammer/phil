# Phase 1 surface determinacy v1

## Status

Executable audit boundary for Matrix case `SURF-005` and supporting evidence for `PHIL-SURFACE-DETERM-001`.

The normative concrete-syntax authority remains `grammar/phase1-surface.ebnf`. This note does not create a second grammar. **SURF-005 is not discharged by this audit alone.**

## Required property

An accepted Grammar-v1 source must have one concrete located surface structure modulo explicitly nonsemantic trivia. Parser alternative order, backtracking, greedy consumption, or recovery policy may not choose between semantically distinct parses of the same source bytes.

That is stronger than observing that the current Haskell parser is a deterministic function.

## Executable local-overlap inventory

`scripts/check_phase1_surface_determinacy.py` imports the same typed EBNF representation used by the canonical derivation path and computes nullable, FIRST, and FOLLOW facts plus local FIRST/FIRST and FIRST/FOLLOW overlaps.

The resulting overlap surface is checked against `grammar/phase1-surface-determinacy.json`. Every entry is bound to the exact Grammar-v1 digest and carries both a reviewed disposition and named parser-pressure files. Any grammar revision that changes the overlap surface fails the surface-grammar workflow until the inventory is reviewed again.

The current Grammar-v1 revision has **27 reviewed local overlap sites**. They fall into two materially different classes.

### Structurally resolved overlaps

Several sites share an initial token but are still unique under the ordinary EBNF because a later mandatory token or delimiter distinguishes the only complete derivation. Examples include:

- `provider` contract versus `provider implementation`;
- ordinary versus `boundary representation` generic requirements;
- tuple versus parenthesized forms;
- refinement-type versus effect-set static actuals;
- several comma-list continuation versus trailing-comma sites; and
- keyword-led session forms versus name-shaped session references.

These remain useful regression points because a parser can still get them wrong, but they do not by themselves require a syntax change.

### Residual grammar ambiguities

The audit also exposes sites where the present plain EBNF admits parser-strategy-dependent attachment. These must be repaired before SURF-005 can be called implemented.

The important families are:

- **semicolon-free statement boundaries**: an immediate argument list can attach to `f`, `break`, `continue`, or a failure target, or can begin a following parenthesized expression statement under a nondeterministic reading;
- **nested trailing `using` clauses**: an unparenthesized `using` after nested `receive_exact` or `select` can attach to the inner or outer eligible expression;
- **recursive prefix/additive/postfix attachment**: keyword-led expressions with trailing additive operands can compete with an enclosing `+`, `-`, `*`, or projection suffix; and
- **qualified name versus projection**: a dotted token sequence such as `pkg.value` can be read as a maximal qualified name or as projection from a shorter name unless the grammar itself commits one structure.

The current Haskell parser consistently chooses one side of these cases. `test/Phase1GrammarV1DeterminacyMain.hs` captures that implementation behavior so future refactors cannot change it accidentally while the grammar repair is pending. **Those tests are behavioral evidence, not authority that the alternative derivation is invalid.**

Semicolon terminators are an available and straightforward repair for the statement-boundary family. They do not solve the nested-`using` or intra-expression attachment families, which require a separate grammar/precedence repair.

## Exact parser-shape pressure

`test/Phase1GrammarV1DeterminacyMain.hs` exercises shared declaration prefixes, brace-led static categories, grouping versus tuples, session references versus keyword forms, current local call/projection/prefix attachment, and nested `using` behavior.

`test/Phase1GrammarV1DeterminacyVariantMain.hs` separately pressures record/tuple variant payload comma behavior. Existing focused Grammar-v1 harnesses remain the named pressure for the other reviewed sites.

## Competence boundary

This slice establishes a reproducible detector, an exact review inventory, and executable capture of current implementation behavior. It deliberately leaves SURF-005 **In progress** until the residual ambiguous families are removed from Grammar v1 and the audit is rerun against the repaired grammar.

The stronger `PHIL-SURFACE-DETERM-001` proof obligation remains the place for language-wide determinate-parse authority over the admitted lexical/syntactic model. Concrete lexer/parser-library correspondence also remains an explicit implementation boundary until separately tightened.
