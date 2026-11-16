# FSEM-02: partial external Ping partner selection and cross-rematch refusal

**Status:** bounded non-normative source/Core conformance and three conditional Rocq 9.2 finite-ledger lemmas; tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613). Extends [externally selected typed Ping partners](formal-semantics-source-ping-partner-selection-fsem02-v1.md), not a new source- or architecture-authority rule.

## Typed premise and transition

The actual checked [accepted Grammar-v1 Ping source](../../test/fixtures/fsem02-protocol-progression-v1/accepted.phil) determines Client Send/U8, Server Receive/U8, distinct original endpoint/End successor names, and Done terminal outcomes. The minimally rejected [stale-close witness](../../test/fixtures/fsem02-protocol-progression-v1/stale-close.phil) must fail specifically as \`GrammarV1ComponentSendCloseCloseMismatch\` (expected \`done\`, actual \`endpoint\`).

Independently supplied architecture/root population, activation, protocol instance, Client/Server roles, permissible partner selection, scheduling, terminal disposal and assurance are *premises*, never conclusions drawn from a source declaration. For any one of six externally allowed bijections of three Client/Server pairs, and any one of six rendezvous orders, the native \`checkProcessCommunication\` step atomically consumes both selected Send/Receive linear predecessors and creates the two distinct typed End successors. A partial selection leaves every **unmatched** Client and Server context byte-for-byte equal to its original pre-Ping state, including linear owners.

## Executable accepted and rejected paths

The strict [source/Core driver](../../test/Phase1FSEM02ProtocolProgressionMain.hs) now tests **36 selected matching/order paths × 4 prefix lengths = 144 partial partner prefixes**. At each prefix it checks unmatched full process contexts; for every already committed pair and each still-free partner it probes both cross-rematch directions. Exactly **288 intentionally rejected cross-partner probes** must produce \`RendezvousEndpointNotOwnedByProcess\` with the consumed Client or Server process and original source-derived endpoint, without a partial transition. It separately checks the independent affine-loan spectator and accepts the unmodified legal suffix, reaching the exact six-process End map, for each prefix.

The original **25,920** selected terminal Close schedules, **13,440** mixed Ping/Close schedules, **806,400** invalid Close probes, and **302,400** stale original-pair Ping probes remain in the same production driver, without weakening GHC warnings. This finite regression does not test an arbitrary number of processes or grant an architecture the right to choose any candidate pairing.

The new [conditional Rocq module](../../proof/Phil/Core/FSEM02PingPartialPartnerPrefix.v) proves that a disjoint unselected pair remains available, and that consumed Client/Server predecessors cannot be rematched after a separate disjoint Ping. Its participant keys are \`nat\` and the ledger is \`nat -> bool\`; representational identity, native authorization and universal native-to-model simulation remain explicit proof gaps. There are no new \`Admitted\`, \`Axiom\` or \`Parameter\` declarations.

**Nonclaims:** no general Haskell↔Rocq refinement, full source operational semantics, independently extracted interpreter, FSEM-02 closure, global progress/fairness/deadlock freedom, or normative graduation. \`SessionStep.v\` and \`ConcurrencySemantics.v\` remain separate proof abstractions rather than silently assumed equivalences.
