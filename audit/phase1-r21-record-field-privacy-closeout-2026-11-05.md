# R21 — certified record-field privacy: implementation closeout

**Date:** 2026-11-05  
**Lane:** implementation audit remediation  
**Finding:** R21 (existing September 29 independent-audit observations; not a new canonical defect)  
**Implementation disposition:** Implemented and tested; merged on `main`.  
**PR:** [#1567](https://github.com/abiggerhammer/phil/pull/1567)  
**Exact PR head:** `3b210bde6a4e498e6957fa51adc72cd679a8ba23`  
**Squash merge:** `72b89b36e94250720764f6754a86a6cb17f46902`  

## Previously observed boundary

The constructors of `CertifiedRendezvousProtocol`, `CertifiedRendezvousCausality`, `CertifiedRendezvousResult` and `CertifiedTerminalDisposition` were hidden, but eight exported Haskell record field selectors allowed external clients to update copies of otherwise certified values. For `CertifiedRendezvousResult`, state-only mutation retained hidden activation lineage while bypassing the certified transition's checks. Original September source observations and their pin-specific limits remain historical evidence.

## Adopted implementation repair

- The relevant record fields now use private labels, while the eight original public read-only getter names and signatures remain available to consumers.
- Constructors stay hidden; internal certification logic and Rocq models are unchanged.
- Permanent external-client regression checks compile all eight public getters successfully and require all eight attempted field updates to fail, matching the targeted label.
- The dedicated [R21 workflow run 42015843748](https://github.com/abiggerhammer/phil/actions/runs/42015843748) succeeded. All 28 exact-head PR workflows completed with no failures or pending runs before merge.

## Scope and non-credit

This closes the **external exported-record-update bypass** at the adopted implementation boundary, not the entire independent-audit acceptance process. It neither proves whole-Phase-1 semantic correspondence nor discharges independent R16, cache, LLVM, proof, release or readiness findings. Do not retroactively restate September source reviews as performed compiler-negative tests. The 244-case Phase 1 conformance matrix remains unchanged in its original cases; supplemental [November 5 audit reconciliation, row 6](https://docs.google.com/spreadsheets/d/1hpzjw7O81vJgb9V5AMRyPd2tuRMHT92EZaqtpGl3DSo/edit#gid=15562026) records the implementation repair.

**Implementation ledger publication:** This versioned closeout is a supplement to, not an overwrite of, the original Drive Markdown implementation audit ledger. An append-only entry in that original ledger remains outstanding if an in-place content editor is available.
