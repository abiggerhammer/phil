# Phase 0 assurance status

This is a status snapshot, not a normative design document. The checked Rocq sources, checked objects, proof certificates, assurance manifests, and exact Git history are authoritative if this file becomes stale.

Snapshot baseline: `main @ a430da8951efb18b25713920940b161ebc277e7f`.

## Historical Rocq back-certification

Phil's current proof-certificate machinery was introduced after a substantial part of the Phase 0 Rocq corpus had already been mechanized. PRs #77, #79–#85, and #90 recompiled those historical proofs under Rocq 9.2.0 and bound the exact checked proof content into `ProofAssistantTheorem` evidence without changing theorem content.

These tranches back-certified **all 46 historical mechanized Rocq obligations**:

- PR #77, merged as `7f40e84734ac7d4c9a5b59d75b7e10e5e9b0c0bd`: 6 Context/Session foundations.
- PR #79, merged as `5813876426ea67d4042d8e5d4d8112d6547d78c2`: 8 Session/Process/Discharge/Decision obligations.
- PR #80, merged as `5dc4cfff122f1923bc91c5a3406203566cda9b65`: 6 generic Assurance obligations.
- PR #81, merged as `89f594a80441781f9e1ac8cfcebdf0e233b80d75`: 6 Systems foundations.
- PR #82, merged as `0933d7aeb6f7e9d33b5039889a43598ee4e666f4`: 4 generic LLVM foundations.
- PR #83, merged as `caa37804dd44e1c355a7b2ece1e14ba2df923319`: 5 Focusing obligations.
- PR #84, merged as `5e6e528324183503b4df586dbf1453568fddf734`: 7 Surface/front-end obligations.
- PR #85, merged as `687332b2a7ae5128088b2e32656c72ecadc7c828`: 2 single-artifact Recognition obligations (`PHIL-RECOG-GATE-001` and `PHIL-RECOG-REFINE-001`).
- PR #90, merged as `a430da8951efb18b25713920940b161ebc277e7f`: 2 conjunctive Recognition obligations (`PHIL-RECOG-COMMIT-001` and `PHIL-RECOG-FAIL-001`).

The resulting evidence kind is `ProofAssistantTheorem`, **not** `KernelChecked`. Rocq kernel/toolchain correctness and each proof's reviewed Haskell/container/representation correspondence remain explicit trust boundaries unless separately discharged.

## Conjunctive Recognition authority

`PHIL-RECOG-COMMIT-001` and `PHIL-RECOG-FAIL-001` each require authority from two checked proof artifacts rather than permitting partial certification from either one alone:

- `recognition_semantics` is established by `Recognition.v/.vo`;
- `loan_exclusion` is established by `RecognitionLoan.v/.vo`;
- the obligation revision uses `AcceptAll` over both distinct `ProofAssistantTheorem` evidence roles.

The #90 correspondence regression removes each selected proof part in turn and requires `AcceptanceRuleUnsatisfied`, so neither artifact can substitute for the conjunction.

Historical `Mechanized / Rocq` certification debt is therefore **zero** at this snapshot.

## Ledger convention

The human-facing Drive logic ledger preserves each historical obligation's original implementation/proof baseline commit. Later back-certification provenance is attached to the evidence-level record rather than overwriting that history.

A historical proof may therefore have:

1. an earlier implementation/mechanization baseline;
2. a later exact-content proof-certificate baseline; and
3. explicit residual correspondence assumptions.

That distinction is intentional and follows the Phase 0 separation between revision lineage, evidence authority, and validity scope.
