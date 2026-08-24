# Phase 0 version-choice proof consolidation

This CI-normalization tranche groups the two historical version/session-choice proof authorities under one workflow while preserving their distinct evidence shapes.

The `version-session-choice` pair checks and stages the existing Systems choice theorem and LLVM boundary theorem, runs the original semantic regression and exact-candidate correspondence check, and emits the same two proof certificates.

The `version-choice-lowering` pair checks the later lowering theorem and its full historical proof prefix, stages the same complete checked proof corpus, runs the focused ABI suite and exact-final-candidate correspondence check, re-runs the LLVM 18 / partial-ABI / native / bad-provider gates, and emits the same proof certificates plus proof-bound `PHIL-LLVM-CERT-010`.

PR #147 established equivalence twice. On both its bring-up tree and clean one-commit recomposition, the consolidated four-job Phase 0 Version Choice Proofs workflow, both historical workflows, ordinary CI, and Phase 0 Baseline were green together. The historical `version-session-choice-proofs.yml` and `version-session-choice-lowering-proofs.yml` workflows are therefore retired from `main`; their execution history remains preserved in Git, while `phase0-version-choice-proofs.yml` is now the active regression surface for both authorities.

No theorem statement, checked proof object selection, semantic or ABI regression, runtime fixture, correspondence logic, certifier source, certificate format, certificate ID, predecessor relation, or validity scope changes in this tranche.
