# Phase 0 LLVM boundary proof consolidation

This CI-normalization tranche groups three adjacent proof-bound LLVM boundary gates under one separately attributable two-stage matrix:

- `client-control-send` (`PHIL-LLVM-CERT-014`);
- `server-framed-ingress` (`PHIL-LLVM-CERT-015`);
- `storage-failure-detail-lowering` (`PHIL-LLVM-CERT-016`).

The consolidated workflow preserves each historical gate's exact checked Rocq theorem, staging prefix, focused regression set, proof-support typechecking, correspondence/drift checker, LLVM 18 assembly/linking, partial runtime-ABI comparison, native smoke fixture, bad ambient/nullary provider rejection, proof certifier, and certificate directory.

Storage Failure Detail retains its wider regression set: its own ABI suite, the predecessor Server Framed Ingress ABI suite, and the current Storage Failure Detail semantic suite. Client Control Send and Server Framed Ingress retain their single focused ABI suites.

PR #143 established equivalence twice. On both its bring-up tree and clean one-commit recomposition, the consolidated six-job Phase 0 LLVM Boundary Proofs workflow, all three historical proof workflows, ordinary CI, and Phase 0 Baseline were green together. The historical `client-control-send-proofs.yml`, `server-framed-ingress-proofs.yml`, and `storage-failure-detail-lowering-proofs.yml` workflows are therefore retired from `main`; their execution history remains preserved in Git, while `phase0-llvm-boundary-proofs.yml` and the two repo-local runners are now the active regression surface for `PHIL-LLVM-CERT-014`, `PHIL-LLVM-CERT-015`, and `PHIL-LLVM-CERT-016`.

No theorem statement, checked proof object selection, test assertion, runtime fixture, correspondence logic, certifier source, certificate format, certificate ID, or validity scope changed in this tranche. `control-codec-proofs.yml` remains separate because it additionally produces runtime test evidence and a combined proof/runtime certificate chain.
