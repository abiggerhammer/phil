# PHIL-SYS-REV-001 — canonical Systems / StageContract revisions

This proof tranche certifies the semantic identity algebra behind Phase 1 `SystemsArtifactRevision` and `Phase1StageContractRevision`.

The production implementation in `Phil.Systems.Phase1Stage` already normalizes the concrete Systems artifact before deriving its revision. Diagnostic display labels, inspection prose, set-like enumeration order, and lowering-list ordering are normalized away; the StageContract revision is then constructed from canonical `SemanticForm` over exact identity-bearing fields.

`proof/Phil/Core/SystemsRevisionCanonicalization.v` models that boundary representation-neutrally:

- a Systems canonical revision depends exactly on source semantic content, Systems-program semantics, StageContract semantics, and lowering semantics;
- source formatting, diagnostic presentation, container order, and backend symbol spelling are excluded from the canonical semantic projection;
- a Stage canonical revision depends exactly on ArchitectureInstance identity, realization identity, Systems revision, verifier profile, source facts, dispositions, target mechanisms, and justifications;
- reconstruction from identical semantic content is deterministic;
- equality of canonical revisions reflects equality of every identity-bearing field;
- changing any identity-bearing field changes the abstract canonical revision;
- `PHIL-ARCH-ID-001` composes through the exact ArchitectureInstanceIdentity field, so presentation changes already proved nonsemantic do not rekey the StageContract;
- `PHIL-SYS-ID-001` and `PHIL-SYS-STAGE-CLOSURE-001` compose to bind the recomputed Systems/final revision to the already verified artifact and stored closure identities.

## Deliberate boundary

Rocq does **not** prove SHA-256 collision resistance or injectivity of the concrete canonical serializer. The theorem proves the semantic dependency/canonicalization algebra. Reflection of abstract revision inequality through concrete serialization and digest bytes remains the explicit ADR-019 representation/cryptographic boundary.

The correspondence job reruns the unchanged generic Systems-stage and final StageClosure regression corpora and strict-typechecks `src/Phil/Systems/Phase1Stage.hs` under `-Wall -Werror`.
