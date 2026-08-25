# Phase 1 generic application identity v1

This tranche advances `PHIL-GEN-ID-001` through conformance cases `GEN-009` and `GEN-010`.

It establishes two distinct checked objects:

- `GenericApplicationIdentity`: the applicative semantic identity of an ordinary generic application, determined by the generic declaration lineage, exact public interface revision, and exact identity-bearing semantic actual arguments;
- `GenericDischargeLineage`: the selected checked definition revision plus the exact requirement-discharge record that justifies use of that semantic application in the current assurance context.

Consequences:

- replacing one accepted proof artifact with another for the same exact requirement may change discharge/assurance lineage without changing the semantic generic application;
- an evidence/provider/contract object explicitly passed as an identity-bearing semantic argument does affect application identity in the ordinary way;
- source ordering of semantic arguments is nonsemantic and duplicate semantic parameter keys fail closed;
- equal ordinary generic applications are canonical/applicative;
- embedding the same generic application at two distinct architecture occurrence sites does not collapse architecture generativity: the sites retain distinct `InstanceKey`s.

`GEN-011` is intentionally **not** claimed here. The Phase 1 conformance matrix assigns target-specific strengthening to the StageContract verifier under ADR-020: stronger target facts must become derived realization obligations rather than being retroactively attributed to generic assurance.

This slice does not yet claim the Rocq proof for `PHIL-GEN-ID-001`, conditional generic assurance reuse, final generic surface syntax, target strengthening, or generic Architecture/Core-to-Systems lowering.
