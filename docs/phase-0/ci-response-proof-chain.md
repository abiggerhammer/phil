# Phase 0 response proof-chain consolidation

This CI-normalization tranche groups three cumulative proof-bound response gates under one separately attributable two-stage matrix:

- `accepted-response`, advancing `PHIL-LLVM-CERT-005` to `PHIL-LLVM-CERT-006`;
- `rejected-response`, advancing `PHIL-LLVM-CERT-006` to `PHIL-LLVM-CERT-007`;
- `final-response`, advancing `PHIL-LLVM-CERT-007` to `PHIL-LLVM-CERT-008`.

The consolidated Rocq runner preserves each historical workflow's exact cumulative compile order and checked proof-object staging. The certificate runner invokes the same `phil-certify-storage` executable with the same ordered checked-object arguments, output certificate names, predecessor certificate relationship, and certificate directory.

Profile-specific staging asymmetries are retained. In particular, Final Response still checks and stages `FinalResponseReceiveCertification.v/.vo` even though the historical certificate invocation does not consume that staged pair.

The three historical workflows remain present with comment-only witness edits during equivalence. No theorem statement, checked proof object, certificate-producing program, certificate format, certificate ID, validity scope, or predecessor relation changes in this tranche.

The historical workflows may be retired only after the consolidated six-job workflow, all three historical witnesses, ordinary CI, and Phase 0 Baseline are green together on both the bring-up tree and a clean one-commit recomposition.
