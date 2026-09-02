# Phase 1 Grammar-v1 determinacy — oracle-resolved derivations

Ledger obligation: `PHIL-SURFACE-DETERM-001`

This is the second mechanized tranche toward the Grammar-v1 unique-parse theorem.
It builds on `proof/Phil/Surface/GrammarDerivation.v`, which gives the exact
mechanically derived EBNF an implementation-independent complete-derivation
semantics.

## What this tranche proves

`proof/Phil/Surface/GrammarDerivationOracle.v` introduces a `DerivationOracle`
indexed by the exact syntax path and remaining token stream.  The oracle fixes
only EBNF choice points:

- which alternative branch is selected;
- whether an optional body is present; and
- whether a repetition continues or stops.

Expression, sequence, and repetition work are represented as one typed
derivation-goal relation.  This avoids making the functionality proof depend on
mutually inductive proof automation.

The central theorem is `oracle_derivation_functional`: for one exact oracle,
grammar, derivation goal, and input token stream, any two oracle-resolved
derivations have the same exact remaining token stream and structural result.
The complete-source corollary `oracle_resolved_phase1_complete_is_unique`
therefore proves that any two complete Grammar-v1 derivations resolved by the
same oracle have the same parse tree.

The oracle relation also erases back to the ordinary nondeterministic EBNF
relation from the predecessor tranche.  It is therefore a restriction of the
language-level derivation semantics, not a new parser semantics.

## What remains

This tranche deliberately does **not** choose an oracle by Haskell parser order.
`PHIL-SURFACE-DETERM-001` remains Active.

The final tranche must derive one admissible oracle from the exact Grammar-v1
structure and the complete 15-site overlap certificate.  In particular it must
show that every ordinary complete EBNF derivation is resolved by that same
oracle.  The reusable resolver families are expected to cover:

- reserved keyword versus identifier continuation;
- mandatory delimiter commitment (tuple/grouping and refinement/effect forms);
- relation-operator commitment after a complete uniquely derived operand; and
- comma-list continuation versus admitted trailing comma.

Only after that bridge is proved may ordinary `Phase1CompleteDerivation` be
called unique.

## Checked boundary

The dedicated workflow requires the exact determinacy inventory to remain 15
reviewed sites, derives `Grammar.v` twice byte-identically from the normative
EBNF, and compiles `Grammar.v`, `GrammarDerivation.v`, and
`GrammarDerivationOracle.v` under Rocq 9.2.0.  It records hashes for the EBNF,
inventory, derivation scripts, generated grammar, both Rocq sources, and both
checked proof objects.

Lexical tokenization correctness, correctness of the EBNF derivation script,
and correspondence between Haskell lexer/parser tokens and `ConcreteToken`
remain explicit boundaries for later parser/grammar correspondence work.
