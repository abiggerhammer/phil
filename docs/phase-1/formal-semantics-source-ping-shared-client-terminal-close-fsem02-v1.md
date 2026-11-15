# FSEM-02 shared-Client contention through terminal Close (non-normative)

**Status:** finite executable source/production Haskell regression plus bounded conditional Rocq 9.2 finite-process lemmas. Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613). Not a normative semantics or architecture/assurance grant.

## Obligation beyond shared-Client first-step contention

The [one-use shared-Client test](formal-semantics-source-ping-shared-client-contention-fsem02-v1.md) establishes that competing Receive peers cannot both consume one Client Send predecessor. This slice continues either winning Send/Receive to two independently checked **typed End Closes**. The real parser checks [accepted Ping source](../../test/fixtures/fsem02-protocol-progression-v1/accepted.phil), source-derived endpoint binders, projected dual heads, and exact linear owner types. Separately the [stale-close source](../../test/fixtures/fsem02-protocol-progression-v1/stale-close.phil) rejects with the exact \`GrammarV1ComponentSendCloseCloseMismatch\` class. The extra activated Server and spectator, binary network instance/roles and terminal disposal permission are externally supplied, not inferred from source text.

For either chosen Server, production \`checkProcessCommunication\` consumes exactly the Client Send and chosen Server Receive predecessors and creates \`TyEndpoint (End Done)\` successors with the original nominal instance and roles. Real \`checkProtocolAction\` Close requests retire the winning Client and Server's exact End metadata and linear owners. The two local Close orders yield equal full process-context maps, while the **unselected Server retains its original Receive head and linear owner** and an unrelated affine spectator retains its active shared loan. Neither the process-key population nor unrelated contexts change.

After both Closes, attempting the losing Receive or replaying the winner rejects with \`RendezvousEndpointNotOwnedByProcess\` on the spent **Client Send** predecessor (sender-first validation). Repeated local Closes reject with \`ProtocolEndpointUnknown\`. A wrong terminal Close outcome rejects with \`ProtocolSessionError (CloseOutcomeMismatch ...)\` and cannot commit a replacement state. Alternate winners replay deterministically from the same immutable prestate; they do not commute with each other because they share a linear predecessor.

## Model, external premises and nonclaims

[Six conditional Rocq lemmas](../../proof/Phil/Core/FSEM02PingSharedClientTerminalCloseFrame.v) use the prior explicit shared-Client one-use model and model each successful local Close as a supplied finite-process-map replacement. They prove two local replacement orders commute, exact terminal slots, nonchosen Server/spectator framing, missing-pair refusal, and failure to rearm the consumed Client token. This does **not** prove the native Haskell Close action realizes arbitrary model replacements, or universal Haskell↔Rocq refinement.

Process-key/endpoint representation fidelity, actual activated population, nominal protocol/role grants, disposal and root selection authority, payload treatment, external environment/scheduler decisions and assurance all remain **premises**. No new grammar, TCB, normative semantics, FSEM-05 extracted executable or FSEM-07 graduation is claimed; FSEM-02 remains open.

[Focused branch preflight](../../.github/workflows/fsem02-shared-client-terminal-close-preflight.yml) runs strict warning-free GHC 9.6.7 production source tests and Rocq 9.2 compilation/no-new-admissions checks before PR creation. Broad current-head CI, fresh post-ready claim guard and protected merge/release remain mandatory.
