# Phase 1 import noninterference — first executable slice

This tranche begins logic-ledger obligation `PHIL-ARCH-IMPORT-001` and conformance case `ARCH-001`.

The governing Phase 1 rule is deliberately narrow:

> Importing or resolving a declaration changes name availability only.

The resolver therefore maps human-facing module/export/local names to already checked `DeclarationIdentity` values. Its state contains no capability authority, provider binding, requirement disposition, assumption, obligation discharge, architecture occurrence, realization choice, or runtime initialization state.

The executable corpus checks that:

- importing all or selected declarations preserves the exact resolved `DeclarationIdentity`;
- local aliases change spelling only;
- moving an unchanged declaration between module paths need not change resolved semantic identity;
- importing an architecture declaration does not instantiate a contained occurrence;
- importing a provider declaration does not satisfy a provider requirement;
- importing a capability-looking declaration does not grant capability authority;
- importing an assumption-looking declaration does not accept an assumption boundary;
- imports cannot silently shadow existing local declarations;
- unknown modules/exports and duplicate exports fail closed.

This is a resolver/elaboration boundary, not a final source-syntax decision. Phase 1 still defers the final spelling of module and import declarations, package identity/version solving, repository provenance, and broad module-system abstraction.

This slice does not close the Rocq proof for `PHIL-ARCH-IMPORT-001`. The proof artifact and the correspondence from eventual parsed module/import syntax to this checked resolver remain future work.
