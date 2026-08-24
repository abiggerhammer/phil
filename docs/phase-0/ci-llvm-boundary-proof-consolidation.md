# Phase 0 LLVM boundary proof consolidation

This CI-normalization tranche groups three adjacent proof-bound LLVM boundary gates under one separately attributable two-stage matrix:

- `client-control-send` (`PHIL-LLVM-CERT-014`);
- `server-framed-ingress` (`PHIL-LLVM-CERT-015`);
- `storage-failure-detail-lowering` (`PHIL-LLVM-CERT-016`).

The consolidated workflow preserves each historical gate's exact checked Rocq theorem, staging prefix, focused regression set, proof-support typechecking, correspondence/drift checker, LLVM 18 assembly/linking, partial runtime-ABI comparison, native smoke fixture, bad ambient/nullary provider rejection, proof certifier, and certificate directory.

Storage Failure Detail retains its wider regression set: its own ABI suite, the predecessor Server Framed Ingress ABI suite, and the current Storage Failure Detail semantic suite. Client Control Send and Server Framed Ingress retain their single focused ABI suites.

The historical workflows remain present with comment-only witness edits during equivalence. No theorem statement, checked proof object selection, test assertion, runtime fixture, correspondence logic, certifier source, certificate format, certificate ID, or validity scope changes in this tranche.

The historical workflows may be retired only after the consolidated six-job workflow, all three historical witnesses, ordinary CI, and Phase 0 Baseline are green together on both the bring-up tree and a clean one-commit recomposition.
