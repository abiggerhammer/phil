# FSEM-02 Ping joint uninvolved-process frame (non-normative)

**Status:** one bounded source-derived two-party Ping Send/Receive regression against an independently activated **third, uninvolved process**, plus a conditional Rocq 9.2 functional-process-map frame. This is not a normative rule or global implementation refinement. [Tracking issue #1613](https://github.com/abiggerhammer/phil/issues/1613).

## Sources and named premises

The accepted and minimally rejected executable Grammar-v1 source witnesses are [accepted.phil](../../test/fixtures/fsem02-protocol-progression-v1/accepted.phil) and [stale-close.phil](../../test/fixtures/fsem02-protocol-progression-v1/stale-close.phil). The real production parsing/Surface checks resolve Client Send and Server Receive occurrence identities and exact dual projected Ping heads. The negative source fails with the exact stale-close binder error.

The test independently supplies a **three-node instantiated architecture** with three active ProcessKeys: source-derived Client and Server process sites and an external uninvolved process. The third process is not invented as an admitted third source component. Its complete initial ProtocolContext contains an affine U8 owner and active shared loan, supplied as an **external resource-context premise**. Binary protocol revision/role grants, process activation and resource-map consistency with an initial activation owner index are not inferred from source spelling.

## Executed production transition and refusal

The regression calls the actual \`Phil.Core.ProcessRendezvous.checkProcessCommunication\` with a source-checked Ping Send/Receive request and a three-key context map. Successful rendezvous consumes both exact source predecessor endpoint names, installs their distinct End-typed successors in the corresponding two active process contexts, **preserves the third process's complete ProtocolContext byte-for-byte**, and preserves all three map keys. A second run on the same original input deterministically reconstructs the identical successor. Replaying the consumed Client predecessor against the progressed state rejects with the precise process and stale name, with the third context still unchanged.

Independent minimally malformed **Client** and **Server** session-head trials (stored End rather than the source-projected nonterminal Send/Receive head) reject with the exact \`RendezvousProjectionSessionMismatch\` process, expected head and actual head. Each failure produces no joint successor map; restoring the independent originally admitted contexts permits the successful control without changing the uninvolved affine loan. A rejected \`Either\` is not a committed transition or rollback.

## Rocq correspondence and limits

[The conditional Rocq model](../../proof/Phil/Core/FSEM02PingThreeProcessFrame.v) lifts the existing [FSEM02PingJointAtomicity](../../proof/Phil/Core/FSEM02PingJointAtomicity.v) two-resource option-valued step to a functional process map with two distinct updated keys. It checks no successor on a refused pair, exact two-target projection, and pointwise preservation of an arbitrary third key distinct from both. It connects that frame to the existing [SessionStep](../../proof/Phil/Core/SessionStep.v) and [ConcurrencySemantics](../../proof/Phil/Core/ConcurrencySemantics.v) abstractions only under named assumptions.

A finite regression on a concrete Haskell \`Map\` is **not** a proof that all Haskell ProcessKeys/Map states correspond to this Rocq \`nat -> option ResourceContext\` model; no universal Haskell-to-Rocq simulation, activation-owner-index correspondence, independent scheduler, fairness, live-state multi-step semantics, source-level third-component authority or \`satisfies C\` is established. No grammar, normative contracts, TCB or branch rules are changed; FSEM-02 remains open.

The [focused GHC/Rocq workflow](../../.github/workflows/fsem02-three-process-frame-preflight.yml) performs warning-free GHC 9.6.7 library and source regression plus Rocq 9.2 compilation without new admissions. Exact-head run outcomes must be recorded independently.
