# Phase 1 surface determinacy certificate

This tranche continues `PHIL-SURFACE-DETERM-001` after the implementation-independent derivation semantics in #552 and fixed-oracle functionality in #554.

`grammar/phase1-surface.ebnf` remains normative. `scripts/derive_phase1_surface_grammar.py` emits the proof-facing `Grammar.v`; the new `scripts/derive_phase1_surface_determinacy_certificate.py` runs the same audited nullable/FIRST/FOLLOW overlap analysis directly over that canonical EBNF and emits a typed Rocq value describing every currently machine-derived local overlap site.

The generated certificate does **not** take `grammar/phase1-surface-determinacy.json` as a proof axiom. The JSON inventory remains the human-review and parser-pressure record, and the dedicated workflow separately requires it to match the machine-derived 15-site inventory exactly. The proof-facing certificate is regenerated from the EBNF itself.

`GrammarDeterminacyCertificateCheck.v` checks two deliberately narrow facts under Rocq 9.2.0:

- the generated certificate and generated grammar carry the same exact canonical EBNF SHA-256; and
- the current generated certificate contains exactly 15 overlap sites.

The workflow derives both `Grammar.v` and `GrammarDeterminacyCertificate.v` twice and requires byte identity before compiling the certificate binding proof and recording source/proof identities.

## What this does not prove

This tranche is still preparatory and does not discharge `PHIL-SURFACE-DETERM-001`. The Python overlap analysis remains an executable review boundary rather than a mechanized completeness theorem.

Final discharge still requires a checked bridge showing that the generated certificate is complete for the exact `Grammar.v` structure, resolver lemmas for every certified site under the admitted lexical/syntactic model, one admissible path/input-indexed oracle built from those resolvers, and a theorem that every ordinary `Phase1CompleteDerivation` is resolved by that oracle. Composing that theorem with #554's `same_oracle_has_one_complete_parse` will yield language-level unique parsing.
