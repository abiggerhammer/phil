# Phase 0 integrated-native CI consolidation

This CI-normalization tranche makes `.github/workflows/phase0-integrated-native-certification.yml` the single workflow owner for the integrated-native execution and certification surfaces while preserving them as separately attributable jobs.

The `phase0-integrated-native-upload` job reproduces the historical native execution gate, including source projection, LLVM 18 assembly/linking, complete runtime ABI checking, and native endpoint execution.

The `certify-phase0-integrated-native-upload` job remains the certification authority: it pins the frozen source-pair digest, captures exact ABI/native evidence, typechecks the certification support, and emits the existing integrated-native certificates.

The historical `.github/workflows/phase0-integrated-native-upload.yml` remains present until old-vs-new equivalence is demonstrated on both the bring-up tree and a clean one-commit recomposition.

No implementation, source digest, runtime ABI, fixture behavior, test assertion, evidence format, certificate format, certificate ID, or validity scope changes in this tranche.
