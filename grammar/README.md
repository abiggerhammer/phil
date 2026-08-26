# Phil grammar artifacts

`phase1-surface.ebnf` is the canonical concrete-syntax authority for the Phil Phase 1 surface language.

Do not maintain a second grammar by hand. Generate the proof-facing Rocq representation with:

```sh
python3 scripts/derive_phase1_surface_grammar.py --write
```

The generated `proof/Phil/Surface/Grammar.v` is intentionally ignored by Git and is regenerated and compiled in CI.

See `docs/phase-1/surface-grammar-v1.md` for the authority, lexical, versioning, and parser-correspondence rules.
