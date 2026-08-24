# Phase 0 source-projection CI consolidation

This CI-normalization tranche makes `.github/workflows/phase0-source-projection.yml` the single owner for the frozen source-to-Systems projection surface and its proof-bound certification.

The existing fast `phase0-source-projection` job is preserved unchanged: it builds the projection package with warnings as errors, runs the original source-to-Systems projection regression, and projects the canonical Phase 0 upload sources.

Two separately attributable proof jobs are added beside it. `rocq-phase0-source-projection` checks and stages the exact `Phase0UploadProjection.v/.vo` pair. `certify-phase0-source-projection` preserves the historical focused regression, proof/certification support typechecks, exact correspondence and drift checks, source-bound control-codec LLVM assembly and partial ABI check, and the same proof and proof-bound `PHIL-LLVM-CERT-018` certificate production.

PR #149 established old-vs-new equivalence twice. On both its bring-up tree and clean one-commit recomposition, the consolidated three-job Phase 0 Source Projection workflow, the historical two-job proof workflow, ordinary CI, and Phase 0 Baseline were green together. The historical `.github/workflows/phase0-source-projection-proofs.yml` workflow is therefore retired from `main`; its execution history remains preserved in Git, while `.github/workflows/phase0-source-projection.yml` is now the active owner for both the fast source projection regression and proof-bound source projection certification.

No source projection behavior, theorem statement, checked proof object, correspondence logic, runtime ABI profile, test assertion, certifier source, certificate format, certificate ID, or validity scope changes in this tranche.
