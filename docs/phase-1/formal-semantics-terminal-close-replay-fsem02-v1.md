# FSEM-02: source terminal-close state replay correspondence (non-normative)

Tracking: [#1613](https://github.com/abiggerhammer/phil/issues/1613). This is a bounded **source-to-production-Core correspondence hardening** of the previously merged restricted send/receive/close/terminal gate, not a new normative rule, language construct, authorization policy, or TCB modification.

## Judgment and authority

Given independently parsed and checked Grammar-v1 sender/receiver witnesses, an already checked restricted Core rendezvous and source-close carrier, explicit activated process network, exact nominal roles/protocol revision, independently authorized message boundary, selected End outcomes, caller-provided terminal dispositions/obligations/root residues, and an activation-owned occurrence index:

1. Match exact source-close successor identities with the two rendezvous successor endpoints and check receiver payload ownership.
2. **Independently replay** Core `closeProcessEndpointState` for the sender and then receiver on the *actual post-rendezvous state* using the exact rendezvous-side process/endpoint/revision/role and externally authorized End outcomes.
3. Require **full equality** of the independently computed communication state and the source-close carrier's alleged post-close state (all process protocol/resource contexts and all occurrence owners). Reject differences with `RestrictedSourceTerminalCloseStateMismatch`; native replay failures retain separate sender/receiver `ProcessEndpointClosureError` payloads. No intermediate successor is exported on a `Left`.
4. Only then run the existing production process-disposal, owner-retirement and root-terminal checks. A successful root fact still requires explicit disposal and separate root/assurance premises.

This prevents a forged *post-close state* with correct endpoint spellings and payload owner from laundering new resources or erasing a spectator into the lifecycle gate. It **does not** authenticate the caller's source-close evidence itself or derive disposal or architecture authorization from source syntax; the prior source checker remains a necessary explicit premise.

## Exact executable evidence

`test/Phase1FSEM02RestrictedSourceTransferMain.hs` parses and executes `test/fixtures/fsem02-restricted-source-transfer-v1/accepted.phil` through the real Haskell source check, send/receive, close and terminal gate, checking deterministic accepted replay. The minimally rejected executable `rejected-stale-close.phil` differs only by `close endpoint` and must yield `GrammarV1ComponentSendCloseCloseMismatch`, not a generic parse error.

Additional negative cases reject a forged post-close affine resource snapshot (**`RestrictedSourceTerminalCloseStateMismatch`**), a missing sender occurrence in the rendezvous successor (**`RestrictedSourceTerminalCloseReplaySenderError (EndpointClosureOccurrenceUnknown ...)`**), and a missing receiver occurrence (**`RestrictedSourceTerminalCloseReplayReceiverError (EndpointClosureOccurrenceUnknown ...)`**). Existing stale session head, role, root residues, payload ownership, duplicate disposal, unconsumed linear payload and open assurance cases remain active.

`proof/Phil/Core/FSEM02TerminalCloseReplay.v` establishes **conditional owner-observation exact retirement and arbitrary spectator preservation** from an extensional replay agreement relation, plus rejection of an observed live sender and a changed independent spectator. The actual production checker tests full state equality; this Rocq model only covers the owner-index projection and does **not** prove Haskell full-map/record equality correct by extraction or universal implementation refinement.

Focused push preflight `.github/workflows/fsem02-terminal-close-replay-preflight.yml` checks strict `-Wall -Werror` Haskell and Rocq 9.2 without any new `Admitted`, `Axiom` or `Parameter`, before broad PR CI.

## Delimited nonclaims

Not a proof of source-authorized payload disposal, root/architecture population admission (FSEM-03), assurance discharge (FSEM-04), executable semantics for all admitted Phase 1 constructs (FSEM-05), Haskell↔Rocq universal refinement (FSEM-06), fairness/deadlock/termination theorems or normative graduation (FSEM-07). The source parser, independent nominal protocol authorization, activation network, boundary message certificate, and explicit environment/outcomes remain trusted inputs to this finite correspondence slice.
