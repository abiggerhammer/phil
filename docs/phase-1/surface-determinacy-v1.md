# Phase 1 surface determinacy v1

## Status

Executable conformance boundary for Matrix case `SURF-005` and supporting evidence for `PHIL-SURFACE-DETERM-001`.

The normative concrete-syntax authority remains `grammar/phase1-surface.ebnf`. This note does not create a second grammar and does not claim a language-wide unambiguity theorem.

## Required property

An accepted Grammar-v1 source must have one concrete located surface structure modulo explicitly nonsemantic trivia. Parser alternative order, backtracking, or recovery policy must not choose between semantically distinct parses of the same source bytes.

That is stronger than observing that the current Haskell parser is a deterministic function.

## Reviewed interpretation policy

The canonical EBNF deliberately keeps ordinary term statements semicolon-free and uses compact optional/repetition notation. The local-overlap audit therefore exposes places where a naive nondeterministic reading could otherwise assign a suffix either to an inner construct or to its enclosing context.

Grammar v1 resolves those reviewed sites with **maximal local attachment**: once a concrete production has begun, any immediately available suffix admitted by that still-open production is consumed there before control returns to its enclosing production. Parentheses and mandatory delimiters close the inner production and can therefore expose a later suffix to the outer one.

The policy has the following concrete consequences:

- reserved-keyword lexical priority is applied before syntactic alternatives, so a reserved second keyword such as `implementation` or `representation` cannot be reinterpreted as an identifier to select a different branch;
- an immediately following term-argument list belongs to the still-open local name, `break`, `continue`, or failure target rather than becoming a new parenthesized statement;
- a nested optional `using` belongs to the innermost still-open `receive_exact` or `select`; parentheses around that inner expression close it and make the suffix available to the outer expression;
- the active additive, multiplicative, postfix, and proposition production consumes its own operator repetition before returning outward, implementing the precedence already written in the EBNF;
- a `qualified_name` consumes its maximal dotted identifier chain before its containing name/static-reference expression returns. Consequently `pkg.value` is one qualified name; projection from a simple name can be made syntactically non-name, for example `(x).field`, while a call result such as `source().field` is already unambiguously projectable;
- in comma-separated forms that admit a trailing comma, comma followed by another element-start token continues the list, while comma followed by the closing delimiter is the trailing comma; and
- for shared-prefix alternatives, the first mandatory distinguishing token commits the branch rather than parser source order or recovery policy.

These rules are an interpretation of the production structure in the normative EBNF, not a second editable grammar. The reviewed overlap inventory records every current site where the rule matters and binds that review to the exact EBNF digest.

## Executable ambiguity inventory

`scripts/check_phase1_surface_determinacy.py` imports the same typed EBNF representation used by the canonical derivation path and computes:

- nullable nonterminals;
- FIRST token sets;
- FOLLOW token sets;
- FIRST/FIRST overlap between grammar alternatives;
- FIRST/FOLLOW overlap at optional and repetition boundaries; and
- rejection of nullable repetition bodies.

The resulting local-overlap surface is checked against `grammar/phase1-surface-determinacy.json`.

An overlap is not automatically a language ambiguity. For example, two declaration forms may share an initial keyword while a later mandatory token distinguishes them. It is, however, a place where one-token dispatch alone is insufficient and where a parser implementation could accidentally make meaning depend on alternative order or backtracking. Every such overlap therefore requires both an explicit reviewed disposition and named executable parser pressure in the inventory.

Any Grammar-v1 revision that changes the local-overlap set fails the surface-grammar workflow until the determinacy inventory is deliberately reviewed and rebound to the new exact grammar digest. Deleting the prose disposition or its parser-pressure references also fails the inventory check.

## Exact parser-shape pressure

`test/Phase1GrammarV1DeterminacyMain.hs` exercises high-risk surfaces and requires distinct located AST constructors rather than mere parse success. Its pressure includes:

- declaration forms sharing prefixes, including optional record/data mode clauses and mandatory capability mode;
- provider contract versus provider implementation versus opaque provider implementation;
- brace-led static effect-set actuals versus brace-led refinement-type actuals;
- parenthesized static values versus tuple types;
- keyword-led session expressions versus name-shaped static session references;
- local attachment of call arguments, qualified names, explicit projections, prefix-expression operands, and failure-target arguments; and
- inward versus parenthesized-outward attachment of nested `using` clauses.

`test/Phase1GrammarV1DeterminacyVariantMain.hs` separately pressures record/tuple variant payload comma behavior, including rejection of a tuple-style trailing comma.

Existing Grammar-v1 harnesses provide additional exact-shape pressure for provider declarations, generic requirements, patterns, relation operators, callable outcome residues, expression precedence/fallbacks, joins/loops, case/construct lists, static-reference arguments, and the remaining production families. The inventory names those concrete test files per reviewed overlap rather than relying on an ambient claim that the parser suite is comprehensive.

## Competence boundary

This SURF-005 slice establishes a reproducible ambiguity-review inventory plus differential/exact-shape implementation pressure. It does **not** by itself prove that no arbitrarily long accepted token sequence has two EBNF derivations.

The stronger `PHIL-SURFACE-DETERM-001` proof obligation remains the place for a language-wide unambiguity/determinate-parse theorem over the admitted lexical/syntactic model. Concrete lexer/parser-library correspondence also remains an explicit implementation boundary until separately tightened.

This separation is intentional: the Matrix case can be executable and regression-resistant without overstating what finite tests or local FIRST/FOLLOW analysis prove.
