# FSEM-02: paired refused terminal Closes and deterministic retry

Status: bounded, non-normative production source/Core and conditional Rocq 9.2 evidence for issue #1613. This extends the single-refusal Ping Close trace, not authoritative syntax or the architecture root policy.

The production Phase1FSEM02ProtocolProgressionMain.hs driver parses the accepted Ping program, separately checks minimally rejected stale-close.phil with the exact GrammarV1ComponentSendCloseCloseMismatch rejection class, and performs a genuine two-process synchronous Ping rendezvous. Both post-rendezvous End successors are derived from the checked source; separately supplied instance, roles, process population, activation, scheduler and disposal grants remain premises.

The new paired-refusal cases test (a) wrong client instance plus wrong server role, and (b) wrong client outcome plus wrong server instance. Both failed local Close attempts are replayed in client-first and server-first orders from the SAME native post-rendezvous state. Every rejection must match its exact ProtocolInstanceMismatch, ProtocolRoleMismatch or ProtocolSessionError (CloseOutcomeMismatch ...) constructor, and must produce no CheckedProtocolStep. Both failure orders leave the entire two-process resource map unchanged. Subsequent admitted local terminal Closes in both orders must equal the direct final map, with the borrowed affine server spectator and shared loan preserved.

FSEM02PingDoubleRefusalRetry.v models both sequential refusal orders with explicit Boolean nominal inputs and failure/commit outcomes. Seven Rocq theorems conditionally prove full-context refusal preservation, denial under bad heads, exclusion of committed actions from the refusal category, and successful retry equivalence with both terminal Close orders. No new Admitted, Axiom or Parameter.

Nonclaims: no general Haskell-to-Rocq simulation, no rollback of committed effects, no source-derived nominal grant or root activation/disposal/assurance discharge, no fairness or deadlock freedom. FSEM-02 remains open.
