# Phase 0 test-evidence CI consolidation

This CI-normalization tranche makes `.github/workflows/test-evidence-certification.yml` the single workflow owner for Phase 0 test-evidence certification while preserving the historical evidence families as separately attributable jobs.

The existing `certify-test-evidence` job remains unchanged in substance. It captures frozen-corpus Surface conformance, exercises the reusable test-evidence certification mechanism, records recognized-record ABI evidence and runtime smoke evidence, and emits the existing `PHIL-SURFACE-CONF-001`, `PHIL-RUNTIME-ABI-001`, and `PHIL-RUNTIME-SMOKE-001` certificates.

The added `certify-remaining-runtime-test-evidence` job reproduces the historical remaining-runtime evidence gate. It builds the same digest-validation, exact-receive, storage, accepted-response, and rejected-response emitters, typechecks the same profiles and dispatcher, uses the same test-evidence certifier, runs the same fixture-certification script, and uploads the same certificate family.

Old-vs-new equivalence was demonstrated on both the bring-up tree and a clean one-commit recomposition in PR #153. The historical `.github/workflows/remaining-runtime-test-evidence.yml` is therefore retired; its history remains available in Git.

The consolidated path filter is the union of the two historical ownership surfaces. No fixture behavior, runtime ABI, evidence profile, test assertion, certifier source, certificate format, certificate ID, or validity scope changes in this tranche.
