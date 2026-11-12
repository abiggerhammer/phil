# FSEM-02: source Ping terminal Close nominal gates

**Bounded, non-normative follow-on to protected #1739.** Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613).

The accepted complete Grammar-v1 `test/fixtures/fsem02-protocol-progression-v1/accepted.phil` is parsed and checked independently; its Client Send and Server Receive predecessors produce exact `End Done` successors through real production Core progression. The nominal protocol instance and roles are independently supplied, never inferred from equal local session syntax.

For each source-derived successor, `test/Phase1FSEM02ProtocolProgressionMain.hs` verifies the following with the real `ProtocolCloseRequest`, keeping the complete resource context and terminal session head unchanged across adversarial metadata fixtures:

- Foreign instance: exact `ProtocolInstanceMismatch` (successor, expected, actual).
- Foreign role: exact `ProtocolRoleMismatch` (successor, expected, actual).
- Both foreign: instance mismatch takes precedence.
- Both matching: exact terminal predecessor consumed; no successor or retained linear owner.
- Stale close after success: exact `ProtocolEndpointUnknown`.

The minimally rejected parsed source `stale-close.phil` separately retains the exact `GrammarV1ComponentSendCloseCloseMismatch` rejection. The adversarial contexts are test inputs, **not** source-derived proof of instance authorization.

`proof/Phil/Core/FSEM02PingNominalTerminalClose.v` proves conditional mismatch refusal, matched local terminal consumption with unrelated linear owner and loan preservation, and wrong-outcome refusal via `FSEM02PingNominalOriginGates.v`, `FSEM02ProtocolHeadProgression.v` and `SessionStep.v`. `ConcurrencySemantics.v` remains a separate rendezvous model.

**Explicit premises/nonclaims:** protocol admission, correct role/instance projection, activation, scheduling/rendezvous, message ownership, terminal disposal authority, architecture/root and assurance. Finite production tests and conditional Rocq lemmas do not establish whole-source semantics, Haskell-to-Rocq refinement, global safety or FSEM-02 completion. No normative syntax, TCB or branch-rule modification.
