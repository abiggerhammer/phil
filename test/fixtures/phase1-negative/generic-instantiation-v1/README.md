# Portable Phase-1 generic-instantiation negatives

This INT-004 tranche carries implementation-independent competent-boundary artifacts for the Phase-1 generic-instantiation negatives governed by GEN-007, GEN-008, and GEN-012.

The corpus is normalized across four semantic tables:

- `requirements-v1.tsv` declares exact public generic requirements by stable per-fixture requirement ID. The current vocabulary is `provider-contract` and zero-argument `proposition` atoms.
- `dispositions-v1.tsv` records only the dispositions actually supplied to the instantiation boundary: exact provider, checked provider refinement, evidence, assumption, or export. Absence of a row means no disposition was supplied for that requirement.
- `policies-v1.tsv` records the explicit assumption/export policy independently from disposition data.
- `manifest.tsv` gives stable fixture identity, portable rejection class, earliest competent layer, exact Matrix/Certified authority, and semantic rejection details.

`authority-registry-v1.tsv` binds the Matrix cases to the Phase-1 Conformance Matrix and the shared Certified authority `PHIL-GEN-INST-001` to `proof/Phil/Core/GenericInstantiation.v`.

The replay adapter may translate this portable vocabulary into the implementation's generic checker API, but Haskell constructors, error enums, object identity, test names, and diagnostic strings are not conformance authority. There is no fixture-ID dispatch: each result follows from the normalized requirement/disposition/policy input.

Current fixtures cover:

- GEN-007: nominal provider superset mismatch and checked refinement targeting the wrong required interface;
- GEN-008: provider availability leaving an independent law requirement unresolved and evidence for the wrong proposition;
- GEN-012: an entirely missing requirement disposition, an assumption rejected by strict policy, and an export rejected by strict policy.

Unknown requirement/disposition kinds, malformed booleans, undeclared requirement references, duplicate requirement IDs, unknown authorities, and missing Certified proof artifacts must fail closed.
