# FSEM-02: source-close carrier projection integrity (non-normative)

Tracking: [#1613](https://github.com/abiggerhammer/phil/issues/1613).
This bounded correspondence extension builds on [exact native Core terminal-close replay](formal-semantics-terminal-close-replay-fsem02-v1.md). It does not alter normative syntax, protocol authority, the TCB, or Core transition semantics.

## Judgment and boundaries

Inputs: actual parsed Grammar-v1 sender/receiver sources and declaration-root keys; a cached already accepted restricted Core rendezvous; independently authorized process network, protocol revision, nominal roles and terminal outcomes.

The production source-close adapter first rechecks exact declaration-rooted send/receive/close plans. It then invokes both native endpoint-close transitions. If either fails, its existing precise sender/receiver Core error remains authoritative.

**New source-carrier guard:** after successful native closes but before returning a successor, require structural Haskell equality of the cached rendezvous request with a request reconstructed from the independently checked source predecessor/successor endpoint binders and the explicit process/revision/role inputs. A mismatch rejects exactly as `RestrictedSourceCloseRequestMismatch expected actual`. Also require the cached restricted transfer's sender and receiver payload binder identities to match checked source binders. Mismatch rejects exactly as `RestrictedSourceCloseTransferBinderMismatch expectedSender expectedReceiver actualSender actualReceiver`. No failure returns a partial successor.

**Executable accepted/rejected witnesses:** `test/fixtures/fsem02-restricted-source-transfer-v1/accepted.phil` is parsed and checked through the real Haskell adapter and production Core transitions. `rejected-stale-close.phil` changes just the sender close binder and rejects as `GrammarV1ComponentSendCloseCloseMismatch`. `test/Phase1FSEM02RestrictedSourceTransferMain.hs` additionally forges the request's sender process identity and each payload binder independently, asserting exact expected/actual error classes. The old ownership, head/role, source type, replay and root negatives remain active.

**Rocq:** `proof/Phil/Core/FSEM02SourceCloseCarrierIntegrity.v` proves exact equality of an abstract *three-string* projection (canonicalized request key plus two binder names) when its guard succeeds, and proves rejection for a mismatch of each field. The Haskell production request equality covers full typed records, but the representation's injective canonicalization into a Rocq string is NOT proved. No Haskell↔Rocq full-state refinement follows.

**Focused pre-PR controls:** `.github/workflows/fsem02-source-close-carrier-preflight.yml` runs warning-free strict Haskell source tests and Rocq 9.2 on pushes to the claimed work branch.

## Explicit nonclaims

Parser/source-binder fidelity, external restricted-message `BoundaryMessageContract`, nominal roles/process/activation and root admission, original pre-rendezvous Core state, restricted occurrence/mode/type, source-authorized payload disposal and obligations remain external premises. Cached carrier integrity is not full provenance authentication; native state must still be independently replayed. FSEM-02, 05, 06 and 07 remain open. No general progress, fairness, compiler correctness or normative semantic claims.

Reader navigation: [Phase 1 typing and semantics reader guide](typing-and-semantics-reader-guide-v1.md).
