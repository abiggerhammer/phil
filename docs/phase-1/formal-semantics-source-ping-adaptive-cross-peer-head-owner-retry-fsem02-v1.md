# FSEM-02 — adaptive cross-peer projected-head / missing-owner precedence

**Status:** bounded, non-normative observation and conditional Rocq model. See
[tracking issue #1613](https://github.com/abiggerhammer/phil/issues/1613).
This slice extends the distinct same-peer head/resource faults in
[adaptive head/resource priority](formal-semantics-source-ping-adaptive-head-resource-priority-retry-fsem02-v1.md);
it does **not** change a normative typing or execution rule.

## Typed source and external premises

The accepted [Grammar-v1 Ping source](../../test/fixtures/fsem02-protocol-progression-v1/accepted.phil)
is parsed and checked using real production Send/Receive/Close binders, and the
[minimally rejected stale-Close source](../../test/fixtures/fsem02-protocol-progression-v1/stale-close.phil)
must still produce exactly `GrammarV1ComponentSendCloseCloseMismatch`.
The source specifies dual `send U8`/`receive U8` to `End Done`; it does
**not** authorize three copies of the architecture, a selected root,
process activation, partner bijection, endpoint disposal, or scheduling.
These remain named external inputs in the finite test.

For one of nine externally selected initial Client/Server Ping pairs, one
of four already-committed terminal Close prefixes, and one of four remaining
ordered partner suffixes, independently poison the **two still-free peers**.
The 144 prefixes have only correctly typed source-derived live Send/Receive
predecessors; the unrelated committed processes and borrowed affine frame
are unchanged.

## Exact negative transition and diagnostic ordering

The actual production
[`checkProcessCommunication`](../../src/Phil/Core/ProcessRendezvous.hs)
is applied to 288 cross-peer states: either the free Client's projected
typed head is substituted with `End Done` while the selected free Server
is missing its *linear owner*, or the dual situation. A different peer's
missing owner must **not** mask the source-projection diagnostic:
`RendezvousProjectionSessionMismatch` identifies the exact poisoned
process, expected Send/Receive head, and observed `End Done`. The
rejected `Either` value supplies **no successor map**.

Restoring only the poisoned peer's typed head (including its required
resource-map head) must expose the other peer's precise
`RendezvousProtocolError (ProtocolEndpointResourceMissing endpoint)`.
Restoring the missing owner as a separate step must recover the byte-for-byte
original process map and accepted externally selected suffix. The 144
additional states in which *both* free heads are poisoned must report Client
first; repairing only Client exposes Server; repairing Server returns the
identical valid replay. Every step also checks the active loan and committed
Close prefix are preserved. There is **no implicit repair** or opaque fallback.

## Proof boundary and executable controls

[`FSEM02PingAdaptiveCrossPeerHeadOwnerRetry.v`](../../proof/Phil/Core/FSEM02PingAdaptiveCrossPeerHeadOwnerRetry.v)
proves the conditional diagnostic precedence for each cross-peer direction,
post-head-repair missing-owner classification, two-bad-head priority, and
exact authorized half-Close suffix recovery. The model takes independent
`nat` head/resource observations and an admitted finite phase map; it is
not a proof of native Haskell `ProcessContext`/Map fidelity or an
unconditional implementation refinement theorem.

The strict source harness is
[`Phase1FSEM02ProtocolProgressionMain.hs`](../../test/Phase1FSEM02ProtocolProgressionMain.hs).
The dedicated [focused push preflight](../../.github/workflows/fsem02-adaptive-cross-peer-head-owner-retry-preflight.yml)
compiles production Haskell with `-Werror`, runs source witnesses, and
checks the Rocq 9.2 file without `Admitted`, `Axiom` or `Parameter`.
Broad PR exact-head verification and an independent post-ready claim guard
remain separate required merge gates.
