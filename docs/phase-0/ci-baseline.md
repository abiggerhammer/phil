# Phase 0 CI baseline

Phase 0 is frozen at merge commit:

```text
911f6f73d9fd7c788f081fe616ad640b83fb882e
```

That commit contains the merged `PHIL-PHASE0-CERT-001` closure tranche for the frozen upload reference program.

## Purpose

Phase 0 was built incrementally. Its GitHub Actions directory therefore records the construction history as many per-slice semantic, runtime, proof, back-certification, and certification workflows.

That history is valuable, but it is not the desired Phase 1 regression surface.

The CI normalization is intentionally split into two tranches.

### Tranche A: equivalence

Add normalized repo-local runners and a consolidated Phase 0 baseline workflow while retaining every existing Phase 0 workflow unchanged.

The candidate baseline currently exposes two end-to-end regression gates:

- frozen source-to-Systems projection;
- frozen source-bound LLVM plus complete runtime ABI checking and integrated native execution.

The native gate requires the exact frozen source-pair digest:

```text
5339e6c7e6520e5495c1d304edcc2427e4bdbe19ce80167af3a314ab2f69e4df
```

and executes the accepted-upload, digest-rejection, and client-cancellation scenarios through the same checked-in source, emitter, runtime providers, ABI checker, LLVM/Clang 18 tool boundary, and native fixture used to close Phase 0.

No theorem statement, obligation ID, certificate format, runtime profile, test fixture, negative case, or implementation behavior is changed by this tranche.

The old and new gates must be green on the same tree before any legacy workflow is retired.

Tranche A landed in PR #124 after both an incremental bring-up tree and its clean one-commit recomposition passed ordinary CI, the consolidated Phase 0 baseline, legacy source projection, source-projection proof/certification, legacy integrated-native execution, and Phase 0 closure certification together.

### Tranche B: normalization

After equivalence is established:

1. retain ordinary build/test CI as the fast default gate;
2. normalize the active Rocq corpus and proof/correspondence checks into a coherent proof gate;
3. retain the consolidated frozen Phase 0 regression gate;
4. retain content-bound certification as a separately attributable, path-filtered gate;
5. retire redundant per-slice construction workflows from `main` while preserving them permanently in Git history at the Phase 0 freeze.

#### Semantic-suite retirement

The first Tranche B cut retires seven focused semantic workflows:

- `begin-policy-session-choice.yml`;
- `client-outbound-semantics.yml`;
- `hello-policy-validation.yml`;
- `local-runtime-choice.yml`;
- `recognition-failure-detail.yml`;
- `storage-failure-detail.yml`;
- `version-session-choice.yml`.

Each retired workflow did only two substantive things: build one named Cabal test suite and run that same suite. All seven suites remain registered in `phil-core.cabal`, and ordinary CI already executes `cabal build all --enable-tests` followed by `cabal test all --test-show-details=direct`. Their test code, test names, inputs, assertions, and failure behavior are unchanged; only duplicate GitHub Actions scheduling is removed.

Focused runtime, proof, back-certification, and content-bound certification workflows are not included in this retirement. They remain until their distinct checks are explicitly consolidated and equivalence is demonstrated.

#### Generic LLVM/runtime runner extraction

The next Tranche B cut moves the generic LLVM/runtime smoke sequence out of `.github/workflows/ci.yml` into `scripts/ci/phase0-llvm-runtime-smoke.sh`. The GitHub workflow retains the same order: build, warnings-as-errors lint build, all Cabal tests, then the LLVM/runtime smoke sequence.

The extracted runner preserves the existing Phase 0 reference LLVM assembly, recognized-record ABI/native smoke and width-drift rejection, exact-receive ABI/native smoke and ambient-provider rejection, digest-validation ABI/native smoke and nullary-provider rejection, and the runnable `return-unit`, `return-42`, and `scalar-binding-42` Phil programs. Only orchestration location changes.

The shared `resolve-llvm18.sh` helper now accepts an optional `PHIL_LLVM18_TOOLS` list so callers do not acquire new tool requirements when reusing it. Its default remains `llvm-as llvm-link llvm-dis clang`, preserving the already-landed source-bound integrated-native runner behavior.

#### Focused runtime consolidation pilot

The first focused-runtime consolidation groups four adjacent physical gates under one workflow while preserving each as a separately named matrix job:

- `storage`;
- `accepted-response`;
- `rejected-response`;
- `exact-send`.

`scripts/ci/phase0-focused-runtime.sh` reproduces the substantive commands from those four historical workflows: emitter/test builds, LLVM assembly and partial/full ABI checks as originally used, C provider compilation with warnings-as-errors, partial linking where applicable, native smoke execution, the corresponding ambient/bad-provider rejection, and Exact Send's explicit focused Cabal ABI test run.

PR #127 established equivalence twice. On both its bring-up tree and its clean one-commit recomposition, the consolidated four-profile workflow, all four historical runtime workflows, ordinary CI, and the Phase 0 baseline were green together. The historical `storage-runtime.yml`, `accepted-response-runtime.yml`, `rejected-response-runtime.yml`, and `exact-send-runtime.yml` workflows are therefore retired from `main`; their execution history remains preserved in Git, while `phase0-focused-runtime.yml` and `scripts/ci/phase0-focused-runtime.sh` are now the active regression surface for those four profiles.

#### Control-choice runtime consolidation

The next focused-runtime tranche adds four control/choice profiles to the same consolidated workflow:

- `hello-policy-validation`;
- `begin-policy-choice`;
- `version-session-choice`;
- `payload-cancel-choice`.

`scripts/ci/phase0-control-runtime.sh` reproduces their historical emitter/test builds, LLVM 18 assembly/linking, partial or full ABI comparison as originally used, C provider compilation with warnings-as-errors, native smoke execution, bad ambient/nullary provider rejection, and focused Cabal ABI test runs. `scripts/ci/phase0-focused-runtime-dispatch.sh` keeps the original four physical profiles on their already-validated runner and routes only these new control/choice profiles to the new runner.

PR #130 established equivalence twice. On both its bring-up tree and clean one-commit recomposition, the expanded eight-profile consolidated workflow, all four historical control/choice runtime workflows, ordinary CI, and Phase 0 Baseline were green together. The historical `hello-policy-validation-runtime.yml`, `begin-policy-choice-runtime.yml`, `version-session-choice-runtime.yml`, and `payload-cancel-choice-runtime.yml` workflows are therefore retired from `main`; their execution history remains preserved in Git, while `phase0-focused-runtime.yml` plus the dispatcher and repo-local runners are now the active regression surface for all eight profiles.

#### Protocol/runtime consolidation

The next focused-runtime tranche adds four adjacent protocol/runtime profiles to the consolidated workflow:

- `client-control-send`;
- `server-framed-ingress`;
- `final-response-receive`;
- `storage-failure-detail`.

`scripts/ci/phase0-protocol-runtime.sh` reproduces each historical gate without normalizing away profile-specific evidence. Client control-send and server framed-ingress retain partial ABI comparison, native smoke execution, bad ambient-provider rejection, and focused ABI tests. Final-response receive retains its full ABI comparison, linked native accepted/rejected/malformed smoke, bad ambient decoder rejection, and focused receive tests. Storage-failure detail retains its focused ABI suite plus the predecessor server-framed-ingress ABI suite and semantic storage-failure-detail suite before its partial ABI/native/bad-provider checks.

PR #132 established equivalence twice. On both its bring-up tree and clean one-commit recomposition, the twelve-profile consolidated workflow, all four historical protocol/runtime workflows, ordinary CI, and Phase 0 Baseline were green together. The historical `client-control-send-runtime.yml`, `server-framed-ingress-runtime.yml`, `final-response-receive-runtime.yml`, and `storage-failure-detail-runtime.yml` workflows are therefore retired from `main`; their execution history remains preserved in Git, while `phase0-focused-runtime.yml` plus the dispatcher and repo-local runners are now the active regression surface for all twelve profiles.

#### Control-codec runtime consolidation

The final ordinary runtime tranche adds `control-codec` as the thirteenth focused runtime profile. It stays on `scripts/ci/phase0-protocol-runtime.sh` because its evidence shape is the same LLVM/C runtime family, while preserving its own predecessor-regression set exactly: the control-codec ABI suite plus storage-failure-detail, server-framed-ingress, and client-control-send ABI suites, followed by partial ABI comparison, partial linking, and native shared-codec smoke execution.

PR #135 established equivalence twice. On both its bring-up tree and clean one-commit recomposition, the thirteen-profile consolidated workflow, the historical Control Codec Runtime workflow, ordinary CI, and Phase 0 Baseline were green together. The historical `control-codec-runtime.yml` workflow is therefore retired from `main`; its execution history remains preserved in Git, while `phase0-focused-runtime.yml` plus the dispatcher and repo-local runners are now the active ordinary runtime regression surface for all thirteen profiles.

#### Historical back-certification consolidation

The first assurance-side tranche consolidates the nine historical `ProofAssistantTheorem` back-certification workflows into one separately attributable matrix with two explicit stages per profile: Rocq checking/staging, then Haskell certificate production. The profiles are `assurance-foundations`, `core-foundations`, `core-control-assurance`, `focusing-foundations`, `llvm-foundations`, `recognition-bundle`, `recognition-gates`, `surface-foundations`, and `systems-foundations`.

`scripts/ci/phase0-back-certification-rocq.sh` preserves each historical theorem compile order and the exact proof sources/objects staged for certificate binding. `scripts/ci/phase0-back-certification-certify.sh` preserves each metadata/certifier pairing and expected certificate count. Recognition Bundle remains a special profile and still typechecks and executes its proof-bundle correspondence regression before producing four proof-part certificates.

PR #137 established equivalence twice. On both its bring-up tree and clean one-commit recomposition, the consolidated 18-job back-certification workflow, all nine historical back-certification workflows, ordinary CI, and Phase 0 Baseline were green together. The historical `assurance-foundations-back-certification.yml`, `core-foundations-back-certification.yml`, `core-control-assurance-back-certification.yml`, `focusing-foundations-back-certification.yml`, `llvm-foundations-back-certification.yml`, `recognition-bundle-back-certification.yml`, `recognition-gates-back-certification.yml`, `surface-foundations-back-certification.yml`, and `systems-foundations-back-certification.yml` workflows are therefore retired from `main`; their execution history remains preserved in Git, while `phase0-back-certification.yml` and the two repo-local runners are now the active historical back-certification regression surface.

## Rule for the refactor

This is orchestration cleanup, not assurance redesign.

Any change that alters a claim, theorem, obligation revision, certificate, validity scope, runtime ABI/profile, fixture semantics, or expected observation belongs in a separate semantic or assurance tranche and must not be smuggled into CI normalization.
