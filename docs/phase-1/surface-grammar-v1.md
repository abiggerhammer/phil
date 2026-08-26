# Phase 1 Surface Grammar v1

## Status and authority

`grammar/phase1-surface.ebnf` is the canonical concrete-syntax authority for the Phil Phase 1 surface language.

The grammar fixes what token sequences constitute Phase 1 surface syntax. It does **not** make syntactic acceptance semantic acceptance. Declaration checking, identity, authority, resource/session legality, assurance, and lowering remain governed by their checked semantic contracts.

In particular:

> **The grammar determines what can be parsed; the checker determines what it means and whether it is admissible.**

The current Haskell `Phil.Surface.Parser` began as the Phase 0 parser and is not made normative by this decision. Phase 1 parser work must establish correspondence to the canonical grammar rather than treating implementation behavior as specification.

## One source of truth

The canonical EBNF is deliberately not duplicated by a hand-maintained Rocq grammar.

Run:

```sh
python3 scripts/derive_phase1_surface_grammar.py --write
```

to derive `proof/Phil/Surface/Grammar.v`. The generated file is ignored by Git. It contains:

- a typed Rocq EBNF syntax tree;
- the exact grammar rule set;
- the start symbol `source_file`;
- the reserved keyword set derived from literal grammar terminals; and
- the SHA-256 digest of the canonical EBNF source.

CI derives the Rocq artifact from a clean checkout, derives it a second time to check determinism, and asks Rocq to compile the result. Thus the proof-facing grammar is mechanically downstream of the EBNF instead of being a second editable specification.

## Canonical lexical rules

The EBNF header owns the lexical contract. In summary:

- Unicode whitespace and `//` line comments are trivia between tokens;
- identifiers begin with a Unicode letter or `_` and continue with Unicode alphanumerics, `_`, or `'`;
- identifiers exclude the keyword literals appearing in the grammar;
- decimal integer syntax is ASCII decimal digits;
- `U` followed by decimal digits is a syntactic unsigned-width type token, while supported widths are checked semantically;
- string literals are UTF-8 double-quoted strings with the small escape set stated in the grammar; and
- parsing consumes the entire source file.

Keyword and `U<digits>` recognition take precedence over ordinary identifiers.

## Canonical structural choices

Phase 1 v1 fixes the following surface conventions:

- a source file has an optional `module`, then imports, then declarations;
- module/import and static declaration/configuration items use semicolon terminators;
- ordinary term statements retain the semicolon-free Phase 0 style;
- generic/static parameters use `[...]`; runtime parameters and arguments use `(...)`;
- generic requirements use an explicit `requires { ... }` block;
- attributes use `@name("value")`, including semantic-key annotations such as `@key(...)` and `@instance_key(...)` when admitted by the semantic checker;
- records, sums, aliases, claims, callable contracts, functions, providers, protocols, capabilities, boundary representations, architectures, components, and program roots are all ordinary top-level declaration forms;
- the Phase 1 protocol surface is explicitly binary: a protocol declaration contains exactly two role-local session declarations; distinct role names and duality remain semantic checks;
- architecture occurrence creation uses `instance`; deliberate sharing uses `ref`;
- a program root explicitly says `program ... = instantiate ...`;
- expression and proposition precedence are fixed by the grammar rather than parser implementation order; and
- Phase 0 boundary/session term forms remain syntactically available while Phase 1 adds functions/closures, records/sums, `if`, `match`, explicit join-state annotations, and loop state/invariants.

These choices freeze spelling and punctuation for Phase 1 v1. They do not freeze a formatter or whitespace layout policy.

## Semantic rejection remains competent

The grammar intentionally accepts some forms whose legality depends on semantic information. Examples include whether a named static argument denotes a type or value in the expected parameter position, whether an unsigned width is supported, whether a protocol's two roles are distinct and dual, whether a provider implementation satisfies its exact contract revision, and whether a target-independent architecture binding is valid.

Those cases belong to elaboration/checking, not to ad hoc parser rejection. Conversely, malformed concrete syntax is rejected by the parser before semantic checking begins.

## Versioning

“v1” names this Phase 1 concrete-syntax epoch. Git history and the embedded source SHA-256 identify exact grammar revisions within it.

A future incompatible concrete-syntax change must be explicit rather than silently changing parser behavior. Whether such a change becomes a new Phase 1 grammar revision or a later language-surface version is a compatibility decision, not parser discretion.

## Deliberate non-goals

This grammar does not define:

- semantic elaboration or Core meaning;
- a formatter or canonical whitespace style;
- target/backend syntax or target realization;
- multiparty/asynchronous protocol semantics;
- macro systems or arbitrary compile-time metaprogramming; or
- proof that the current Haskell parser already implements all Phase 1 productions.

Parser/grammar correspondence is an implementation and assurance obligation to discharge as the Phase 1 front end catches up with the now-canonical surface.
