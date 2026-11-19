# FSEM-02: independently repairing two stale source Close operands

**Status:** bounded, non-normative source-to-production-Core conformance; separate conditional Rocq 9.2 gate theorem. Tracks #1613. Neither source spelling nor a proof-side Boolean gives authority to create protocol instances, activate processes, dispose of endpoints, select a root, or discharge assurance obligations.

## Source judgment and executable witnesses

From `test/fixtures/fsem02-restricted-source-transfer-v1/accepted.phil`, the sender and receiver each perform a typed `Bytes[8]` send/receive and `close done` on their *fresh successor*. The minimally rejected full-source witness `rejected-both-stale-close.phil` changes **only** those two operands to `close endpoint`, the already consumed predecessor. The separately existing `rejected-stale-close.phil` and `rejected-receiver-stale-close.phil` repair exactly one site each.

Conditional judgment:
```text
external P; source Γs,Γr; actual pre-state Δ
  |- restricted-rendezvous(s,r)
  ==> exact source error | checked Δ'
```
Source checking precedes authorized Core transfer. The sender's stale Close is an exact `RestrictedSourceSendError (GrammarV1ComponentSendCloseCloseMismatch successor predecessor)`; if it is repaired while the receiver remains stale, the exact result is `RestrictedSourceReceiveError (GrammarV1ComponentReceiveCloseCloseMismatch successor predecessor)`. Repairing the receiver only leaves the sender refusal unchanged. Neither source-error path emits a Core successor; correcting both source operands restores the already-authorized original state transfer with endpoint predecessor consumption, successor identity, `Bytes[8]` ownership transfer and independent affine spectator preservation.

`test/Phase1FSEM02RestrictedSourceTransferMain.hs` uses the actual Grammar-v1 parser, production `grammarV1CheckRestrictedSourceRendezvous`, declaration-rooted binders, and activated Core contexts. It validates that all four fixtures have the claimed **exact** syntactic relationship, that the two source checks prioritize the named rejection classes, and that pure replay is deterministic. The existing `acceptedReplay` checks actual Core `Map`/`Set` resource outcomes and frame preservation. The new source repair test does not itself execute an operational language interpreter or give an independent global typing theorem.

## Finite Rocq proof and trust boundary

`proof/Phil/Core/FSEM02ReceiverClosePriority.v` adds `rcpDualStaleSourceRepairDiamond`, `rcpDualSourceRepairPreservesNativeFaults` and `rcpDualSourceAndNativeRepairFramedTransfer`: finite source gate repair commutation, exact no-successor refusals, independent native resource failures and modeled transfer after full repair. These use model Booleans and explicit external authority; **not** a certified simulation from the Haskell implementation into Rocq, nor a proof of the complete `SessionStep.v` / `ConcurrencySemantics.v` correspondence. Exact endpoint/resource identities and the external protocol boundary are checked as Haskell witnesses rather than proved universally.

Reproduce on the exact work branch through the existing FSEM-02 receiver Close priority focused preflight (strict GHC 9.6.7 `-Werror` plus Rocq 9.2 no-new-admissions). Broad PR CI, fresh post-ready claim guard, protected expected-head merge and matching claim release remain separate gates. **FSEM-02 is still OPEN**; no Phase 1 normative status, global source/Core refinement, independent extracted interpreter, scheduler completeness or root/assurance discharge is claimed.
