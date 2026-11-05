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
