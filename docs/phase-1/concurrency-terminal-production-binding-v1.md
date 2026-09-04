# Phase 1 concurrency terminal production binding v1

`PHIL-CONC-TERM-001` is production-bound to the exact machine decision surface staged by #696.

## Exact kernel

`proof/Phil/Core/ConcurrencyTerminalImplementationExtraction.v` freshly extracts `ConcurrencyTerminalKernel.hs`.
The checked-in copies under `generated/` and `src/` are required to be byte-identical to that extraction:

- size: 1,800 bytes;
- SHA-256: `6cbb280fe49621f82fa8b3b3999450c82d86c0b2df658c8c3edd60534889135a`;
- two trailing newline bytes.

The four gates retain the #696 decomposition:

1. process-local terminal closure: resource/loan closure, obligation closure, endpoint closure, exact terminal control;
2. fatal-process isolation: actor was running, actor becomes failed, every peer semantic state remains unchanged;
3. root terminal closure: root resource/obligation/observable closure, complete terminal facts, no invented facts, every static status terminal;
4. stuck/nonterminal separation: root not terminal, at least one running static process, no enabled semantic step.

## Native-first production wrapper

`Phil.Core.ConcurrencyTerminalCertification` does not replace `Phil.Core.ProcessLifecycle`.
It wraps the existing lifecycle checker and preserves its diagnostics before invoking the extracted gates.

A `CertifiedTerminalRuntime` is opaque. It can only be initialized from the production-refined `CertifiedRendezvousActivation` predecessor, then advanced by certified declared/fatal terminal transitions. The wrapper independently checks exact runtime population/domain integrity after every accepted transition.

Declared terminal transitions additionally require the native result to contain the exact requested `ProcessKey` and control and to satisfy the Certified terminal-control boundary. This intentionally catches the current representation gap where native `applyDeclaredTerminalTransition` accepts `Return`: native success followed by a false `terminalControlExact` bit fails closed at the kernel boundary. `Continue` still fails earlier with the existing native diagnostic.

Fatal transitions are checked both as exact local terminal facts and as exact failure-isolation steps. Peer status, protocol/resource context, and residual-obligation state must remain byte-for-byte equal for every distinct process.

Root terminal results are reflected independently against the static `ProcessNetwork` population: terminal-fact keys must exactly cover the population, embedded `ProcessKey`s must agree, no extra facts may exist, and every static runtime status must be terminal with `Closed` or `Failed` control. Root semantic residues remain native-first errors.

Stuck classification remains explicitly nonterminal. A certified local enabled step must name a running static process. A certified rendezvous enabled step must come from a production-refined `CertifiedRendezvousResult` and match two distinct running static `ProcessKey`s.

## Retained boundary

The source checker remains responsible for supplying a **complete** set of currently enabled semantic steps. The production wrapper certifies each supplied step, but absence from that list is still the concrete source-enabledness/extraction boundary used to reflect `noEnabledSemanticStep`. This is not a fairness, scheduler, eventual-response, deadline, or deadlock-freedom claim.

Other retained implementation assumptions are the concrete `Map`/`Set` representations, `ProcessKey` encoding, Haskell equality for peer snapshots and terminal maps, Rocq extraction, GHC/runtime correctness, and physical cleanup/transport behavior outside Phil's source semantics.

## Production controls

The dedicated workflow:

- freshly compiles the Certified predecessor chain and #696 implementation theorem;
- freshly extracts the exact 1,800-byte kernel and byte-compares both checked-in copies;
- reruns #696's 20 direct extracted-kernel controls;
- strict-checks `ProcessLifecycle`, both production-refined concurrency predecessors, the terminal production wrapper, and its harness under `-Wall -Werror`;
- reruns the #687 activation production harness and #693 rendezvous production harness;
- runs 13 terminal production controls, including native-success `Return` rejection and injected disagreement for all four kernel groups;
- reruns the unchanged CONC-007/008 and external-participant fixtures.

Only after exact-head CI and artifact harvest may `PHIL-CONC-TERM-001` move from **Certified** to **Implementation Refined**.
