# Phase 0 source-projection CI consolidation

This CI-normalization tranche makes `.github/workflows/phase0-source-projection.yml` the single owner for the frozen source-to-Systems projection surface and its proof-bound certification.

The existing fast `phase0-source-projection` job is preserved unchanged: it builds the projection package with warnings as errors, runs the original source-to-Systems projection regression, and projects the canonical Phase 0 upload sources.

Two separately attributable proof jobs are added beside it. `rocq-phase0-source-projection` checks and stages the exact `Phase0UploadProjection.v/.vo` pair. `certify-phase0-source-projection` preserves the historical focused regression, proof/certification support typechecks, exact correspondence and drift checks, source-bound control-codec LLVM assembly and partial ABI check, and the same proof and proof-bound `PHIL-LLVM-CERT-018` certificate production.

The historical `.github/workflows/phase0-source-projection-proofs.yml` remains present with a comment-only witness edit until the consolidated three-job workflow, that historical proof workflow, ordinary CI, and Phase 0 Baseline are green together on both the bring-up tree and a clean one-commit recomposition.

No source projection behavior, theorem statement, checked proof object, correspondence logic, runtime ABI profile, test assertion, certifier source, certificate format, certificate ID, or validity scope changes in this tranche.
