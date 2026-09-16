# Portable Phase 1 generic negative corpus v1

This directory is the first INT-004 migration of Phase-1 constructor-only negative tests into an implementation-independent competent-boundary format.

The current tranche covers five concrete negative checks governed by GEN-002, GEN-003, and GEN-006. The portable input describes the generic semantic state directly; it does not name Haskell constructors, test functions, source filenames, or diagnostic strings.

`manifest.tsv` owns stable fixture identity, checker family, portable expected rejection label, earliest competent layer, exact Matrix/Certified authority references, and the semantic details that the rejection must preserve.

`parameters-v1.tsv` gives the declared abstract value-parameter domain for each fixture.

`uses-v1.tsv` gives the body-directed structural use events. The v1 vocabulary is `transfer`, `discard`, and `duplicate`. These denote ownership-preserving transfer, weakening pressure, and contraction pressure respectively.

`actuals-v1.tsv` gives concrete structural modes for `structural-actual` checks. Modes are `unrestricted`, `affine`, or `linear`.

`published-v1.tsv` gives explicitly stabilized structural permissions for `structural-interface` checks. Permissions are `weakening` and `contraction`, separated by `;` when both are present. A `structural-interface` fixture with no rows in this table deliberately supplies an explicit empty published requirement set; it does not mean “infer the public set”.

`authority-registry-v1.tsv` resolves every manifest authority reference. Matrix references resolve to the Phase-1 Conformance Matrix. Inherited Certified references resolve to checked-in Rocq proof sources. The manifest authority domain and registry domain must match exactly.

A conforming replay reconstructs the generic checker input from these tables, invokes the competent generic structural/interface relation, and checks the portable semantic rejection class and preserved parameter/permission/mode fields. It must fail closed on malformed vocabulary, undeclared parameters, duplicate rows, unknown authority, or missing Certified proof artifacts.

The initial five fixtures are:

- GEN-002: duplication/contraction rejects Affine and Linear structural actuals;
- GEN-003: discard/weakening rejects a Linear structural actual;
- GEN-006: an explicit stabilized public interface that omits a newly induced contraction or weakening requirement rejects.

The extra GEN-002 Affine contraction pressure is bound both to Matrix GEN-002 and to the inherited Certified PHIL-GEN-STRUCT-001 structural-mode theorem. This keeps the portable corpus tied to exact semantic authority rather than to legacy test labels.
