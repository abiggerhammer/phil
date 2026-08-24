# Phase 0 response proof-chain consolidation

This CI-normalization tranche groups three cumulative proof-bound response gates under one separately attributable two-stage matrix:

- `accepted-response`, advancing `PHIL-LLVM-CERT-005` to `PHIL-LLVM-CERT-006`;
- `rejected-response`, advancing `PHIL-LLVM-CERT-006` to `PHIL-LLVM-CERT-007`;
- `final-response`, advancing `PHIL-LLVM-CERT-007` to `PHIL-LLVM-CERT-008`.

The consolidated Rocq runner preserves each historical workflow's exact cumulative compile order and checked proof-object staging. The certificate runner invokes the same `phil-certify-storage` executable with the same ordered checked-object arguments, output certificate names, predecessor certificate relationship, and certificate directory.

Profile-specific staging asymmetries are retained. In particular, Final Response still checks and stages `FinalResponseReceiveCertification.v/.vo` even though the historical certificate invocation does not consume that staged pair.

PR #145 established equivalence twice. On both its bring-up tree and clean one-commit recomposition, the consolidated six-job Response Proof Chain workflow, all three historical response workflows, ordinary CI, and Phase 0 Baseline were green together. The historical `accepted-response-proofs.yml`, `rejected-response-proofs.yml`, and `final-response-proofs.yml` workflows are therefore retired from `main`; their execution history remains preserved in Git, while `phase0-response-proof-chain.yml` and the two repo-local runners are now the active regression surface for the `CERT-005` through `CERT-008` response chain.

No theorem statement, checked proof object, certificate-producing program, certificate format, certificate ID, validity scope, or predecessor relation changes in this tranche.
