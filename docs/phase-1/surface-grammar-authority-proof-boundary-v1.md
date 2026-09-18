# PHIL-SURFACE-GRAMMAR-001 proof boundary

This slice certifies the Phase-1 Grammar-v1 authority boundary.

The normative source remains `grammar/phase1-surface.ebnf`. The certification
requires one nonempty canonical source identity, exact source-revision binding in
each proof-facing derivation, deterministic repeated derivation, exact
reserved-word correspondence between identifier-shaped EBNF literals and the
production Grammar-v1 lexer, and warning-clean compilation of the generated
Rocq grammar artifact.

The dedicated gate performs the concrete correspondence checks rather than
pretending Python or Haskell representation details are part of the normalized
theorem:

- syntax-check the derivation script;
- run the exact Grammar-v1 lexer authority regression;
- derive `proof/Phil/Surface/Grammar.v`;
- derive it again and byte-compare both results;
- run the generator's `--check` mode;
- compile the generated grammar under Rocq 9.2.0 with no warnings; and
- compile the normalized GrammarAuthority semantic/correspondence proofs.

This does **not** certify that the production parser recognizes exactly the
language of Grammar v1. Parser soundness/completeness, parser-library behavior,
Unicode/tokenization implementation correspondence, and normalized-AST
correspondence remain owned by `PHIL-SURFACE-GRAMMAR-CORR-001`.
