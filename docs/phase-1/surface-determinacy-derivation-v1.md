# Phase 1 surface derivation semantics

Ledger target: `PHIL-SURFACE-DETERM-001`

This is the first mechanized tranche toward the Grammar-v1 unique-parse theorem. It does **not** by itself discharge determinacy.

## Exact grammar authority

`grammar/phase1-surface.ebnf` remains normative. `scripts/derive_phase1_surface_grammar.py` deterministically emits `proof/Phil/Surface/Grammar.v`, whose typed `EbnfExpression` tree and exact source SHA-256 are the proof-facing grammar authority. The new `GrammarDerivation.v` imports that generated artifact rather than restating or hand-normalizing the grammar.

## Derivation relation

`GrammarDerivation.v` defines an implementation-independent EBNF derivation relation over concrete token streams. A token is either an exact literal token or one value from a named lexical class. Derivations return both the unconsumed suffix and a structural parse tree.

The relation covers literals, lexical classes, nonterminals through exact rule lookup, sequences, alternatives, optionals, and repetitions. Repetition steps must consume input; the existing exact-digest determinacy audit separately rejects nullable repetition bodies.

`SyntaxPath` records structural decision sites through nonterminal, sequence, alternative, optional, and repetition descent. Those paths deliberately do not encode Haskell parser call order. They are the stable handles the successor tranche will use for a deterministic choice oracle and the exact overlap certificate.

A `Phase1CompleteDerivation` is a derivation of the exact generated `source_file` nonterminal that consumes the entire token stream.

## Why this is separate from parser tests

A recursive-descent parser returning one tree is not a proof that the EBNF admits only one complete tree. This relation makes the stronger language question explicit: two distinct `Phase1CompleteDerivation` witnesses for the same token stream would be a real Grammar-v1 ambiguity even if the Haskell parser consistently preferred one of them.

## Planned successor tranches

The next proof tranche will add a path-indexed choice oracle and prove oracle-resolved derivations functional. The final tranche will derive the exact machine overlap inventory from the normative grammar, instantiate the reusable resolver families for all reviewed sites, prove that every complete derivation is oracle-resolved, and conclude uniqueness of complete Grammar-v1 derivations.

Until that final theorem lands, `PHIL-SURFACE-DETERM-001` remains Active.
