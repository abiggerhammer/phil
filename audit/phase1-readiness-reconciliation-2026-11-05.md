# Phase 1 bounded readiness reconciliation — 2026-11-05

Baseline: `abiggerhammer/phil` main `57f56982271dd33819869d0a646a431e5aa738c1`.
This is a supplemental source/evidence audit, not final-candidate certification.
Sources: [independent code review index](https://drive.google.com/file/d/1M5mk_xuWPp0AFnP8r9nwLzbshZVrdT7X/view), [implementation audit ledger](https://drive.google.com/file/d/1DkP56xVvYMIPyliSF7TxbER_2Lss492l/view).

## Adopted bounded implementation repairs

R20 #1437, R17 #1564, endpoint definedness D01-D03 #1565, Steve CAS E-STEVE-CLEANUP-01 #1566, and R21 certified rendezvous/terminal output #1567 are merged and green at their documented scopes. #1567's exact head is `3b210bde6a4e498e6957fa51adc72cd679a8ba23`; squash merge `72b89b36e94250720764f6754a86a6cb17f46902`; [R21 CI](https://github.com/abiggerhammer/phil/actions/runs/42015843748) passed and 28/28 reported PR workflow runs completed without failure.

R10/R16 activation lineage has its own [merged implementation](https://github.com/abiggerhammer/phil/blob/main/docs/phase-1/review-r10-r16-restricted-successor-lineage-v1.md). R13/R14 cumulative provider authority has [separate implementation](https://github.com/abiggerhammer/phil/blob/main/docs/phase-1/review-r13-r14-cumulative-provider-closure-v1.md). Historical [borrow-scope](https://github.com/abiggerhammer/phil/blob/main/docs/phase-1/audit-borrow-local-scope-remediation-v1.md) and [recognition-grammar](https://github.com/abiggerhammer/phil/blob/main/docs/phase-1/audit-recognition-grammar-remediation-v1.md) defects have landed implementation repairs. None establishes whole-program proof or independent final review.

## Current-source exposures to address before readiness

1. **ReusableProofEvidence** in `src/Phil/Verification/ProofEvidence.hs`: constructor hidden but all three invariant-bearing record labels exported; copied prepared tokens can still be updated without passing `prepareReusableProofEvidence`. Same historical pass-7 R21 defect class, **not** part of #1567's four-type patch. Priority: private backing labels, original read getters, external-client compile rejection and cache-consumption regression.
2. **FloatValue** in `src/Phil/Core/FloatArithmetic.hs`: constructor hidden, `floatFormat`/`floatBits` still actual exported fields. Historical `430aba3/FLOAT-BOUNDARY` is a scope-limited instance of the record-update issue. Priority: getter-preserving private labels and invalid-bit conversion negatives; confirm Cabal module exposure.
3. **Runtime ABI checker** `scripts/check_runtime_abi.py`: current scalar parser drops pointer address spaces, and declaration parser considers only single-line `declare`/`define` entries. Historical `7973d01/ABI-01/02` were reproduced with fixture/provider inputs, and default calling-convention checking remains an explicit premise. Priority: tighten parsing with exact negative/positive provider controls.

These are source-level findings as of this baseline, not fresh executed exploit reproductions. Do not silently promote source inference to current Haskell/LLVM runtime proof.

## Remaining reconciliation, not yet classified as current defects

- Runtime-choice `f2ed3c1/RT-01/02`: historical reconstructed LLVM invalidity; replay current Haskell lowering and LLVM validation before calling them unfixed.
- Native transport `f2ed3c1/RT-03`: historical complete-C sanitizer finding; check current complete translation unit and generated-program reachability before disposition.
- Independent `NR-D06` StageClosure/certified-envelope caller review and final delta/integration review remain without credited current-head independent outcome.
- Published `phil-v0.1.0-phase1` release dated 2026-09-20 has eleven listed assets; historic public-byte retrieval and R18/EF04 verification were incomplete. Listing alone does not certify asset bytes.
- [Open audit-only PR #1413](https://github.com/abiggerhammer/phil/pull/1413) remains outside adopted readiness evidence.

## Verdict and next tranche

**Independent-audit freeze: NOT YET.** Implement and regression-test the reusable proof-cache token boundary first, then FloatValue and ABI checker. Reconcile historical runtime/native findings by exact current-source tests, finish independent NR-D06 and release byte verification, then pin a candidate for independent delta review. Preserve all historical audit evidence and the original 244 normative conformance cases; these are supplemental findings, not new normative rows.

## Implementation delta — 2026-11-05: reusable proof-cache field privacy

The source-confirmed `ReusableProofEvidence` record-field exposure listed in this report's initial baseline is **implemented and tested** by [PR #1568](https://github.com/abiggerhammer/phil/pull/1568), exact green head `eb73dd28aec16404c47e8d860cf9b7f73b410e06`, squash-merged at `95c0bdd5fff5f5c5c4a809e32e092c23ad4d14d6`. All **31/31** exact-head PR workflows succeeded, including the [dedicated external-client / cache-reuse workflow](https://github.com/abiggerhammer/phil/actions/runs/42020898390).

The three record labels are private; original getter names remain usable. The tests compile positive getter clients, require each external record-update attempt to fail, and replay genuine prepared cache acceptance and dependency/revision/scope/validity invalidation through VER-006. The earlier source observations above remain historical at their review pin. This closes only this protected-field mutation bypass, not all potential cache-consumption or identity errors.

**Remaining immediate implementation candidate:** `FloatValue` record-label exposure; ABI-01/02 and current RT-01/02/03 dispositions remain distinct. Independent freeze verdict remains **NOT YET**.

## Implementation delta — 2026-11-05: FloatValue record-update boundary

The historical `430aba3/FLOAT-BOUNDARY` source-import record-label exposure is **implemented and tested** by [PR #1570](https://github.com/abiggerhammer/phil/pull/1570), exact green head `45a13f9bf91287883ac862158116808610d51d7b`, squash merge `85d0b4049ad3023ea34ee0216228e3c164df1be0`.

All **21/21** reported exact-head PR workflows completed successfully, including the [dedicated FloatValue boundary run](https://github.com/abiggerhammer/phil/actions/runs/42023795612), existing numeric-semantics proof checks and warning-free Haskell integration. The two actual record labels are private, original read-only getters remain, external attempts to update either field are compile-negative, and F32 range / valid F32 and F64 / same-format numeric conversion controls pass.

**Scope:** `Phil.Core.FloatArithmetic` is an internal Cabal `other-modules` component. This closes the tested source-import mutation path, not a demonstrated public installed-package exploit, whole IEEE arithmetic refinement, or all numeric trust assumptions. Preserve the historical audit observations at their original pins.

**Remaining immediate implementation item:** runtime ABI-01/02 and the default calling-convention premise. RT-01/02/03, NR-D06, release asset verification and independent final-delta sign-off remain separate. Independent-audit freeze: **NOT YET**.

## Implementation delta — 2026-11-05: runtime ABI-01/02 and default calling convention

The historical `7973d01/ABI-01` and `ABI-02` checker gaps, plus the unguarded default-calling-convention premise, are **implemented and tested at the documented Phase 0 ABI-gate scope** by [PR #1571](https://github.com/abiggerhammer/phil/pull/1571), exact green head `7a093228a98d0623bc738a272f2b84d8d355bb70`, squash merge `610031d8b3a010622700b4ee2fc99db6b3fecf78`. All **26/26** exact-head PR workflows completed successfully.

The checker now compares opaque pointer address spaces in arguments/results, recognizes quoted and multiline required `phil_*` LLVM headers, fails closed for malformed required declarations, and enforces the documented default calling convention. Dedicated tests exhibit failures on pinned historical checker blob `51db1085eeb92b99fe11cb7c8bd7bcb2af6ef164` and success with the repaired checker. Existing `--partial` controls and the deliberately excluded linkage/attribute comparison scope are preserved. [Dedicated ABI regression workflow](https://github.com/abiggerhammer/phil/actions/workflows/phase1-audit-runtime-abi-completeness.yml) passed.

The same PR fixes LLVM 18 installation in previously red Phase 0 integrated-native certification, focused runtime, LLVM boundary proof certification, and control-codec certification jobs. All reran successfully on the exact green PR head. These were toolchain-provisioning faults, not newly discovered compiler semantic defects.

**Boundary:** no claim of a complete LLVM parser, arbitrary ABI attributes or calling conventions, all-platform linkage correctness, proof correspondence beyond existing named suites, or final public-release byte certification. Historical source/synthetic audit findings remain preserved. **Next:** reconcile historical `f2ed3c1/RT-01/02/03` against current source and supported-toolchain reproduction, then independent NR-D06, release asset-byte validation, and pinned final-delta review. Independent-audit freeze: **NOT YET**.

## Implementation delta — 2026-11-05: RT-01/02/03 current-source repairs

Historical `f2ed3c1/RT-01`, `RT-02` and `RT-03` are **implemented and tested at the bounded source/ABI/runtime boundaries** in [PR #1574](https://github.com/abiggerhammer/phil/pull/1574), exact green PR head `44029cd525983b00d9dec4e313d0969cc3114477`, squash merge `75b6226ff59883ea06b0ca4d4f87a8340b13ec67`. All **22/22** reported exact-head PR workflows completed successfully, including the [dedicated RT reproduction workflow](https://github.com/abiggerhammer/phil/actions/runs/42060839542) and [Steve release workflow](https://github.com/abiggerhammer/phil/actions/runs/42060839267).

- **RT-01:** Runtime-choice LLVM function inputs now include cleanup-only owner operands, rather than only provider-call inputs. The actual Steve runtime-choice plan is extended with a cleanup-only owner and checked for parameter inclusion.
- **RT-02:** LLVM emission rejects runtime-choice payload targets with non-producing predecessors or an unbound arm that reaches the payload load. The Steve fixture exercises both negative CFG cases, and the generated LLVM is checked under LLVM 18.
- **RT-03:** Native `control_codec_v1.c` transport append retains source offsets across `realloc`, checks alias ranges against the logical length, and rebases before copying. Sanitized regression contrasts the pinned historical complete-source translation-unit UAF against repaired whole-buffer and interior self-append cases, preserving independent append behavior.

These are **new current-head executed test results**, not retroactive credit for historical report-only reconstructions. The historical finding observations, pins and initial evidence classifications remain unchanged.

**Limit:** This does not certify arbitrary runtime-choice graph shapes, all native transport call sites, proof correspondence beyond the named gates, or final release assets. Remaining independent work: NR-D06 StageClosure/certified-envelope review, pinned final integration/delta review and release public-byte validation. **Independent-audit freeze: NOT YET.**
