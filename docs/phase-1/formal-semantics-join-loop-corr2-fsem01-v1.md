# FSEM-01 CORR-2: bounded join/loop native resource-cut and failure-prefix replay

> **Provisional source/model correspondence slice, not normative Phase 1
> semantics.** This work follows protected [CORR-1 #1718](https://github.com/abiggerhammer/phil/pull/1718)
> and belongs to [FSEM issue #1613](https://github.com/abiggerhammer/phil/issues/1613).
> Successful parsing, a bounded source adapter, a native Core replay and a
> conditional Rocq model **do not** establish a universal Haskell-to-Rocq
> implementation refinement or general Source→Core compiler correctness.

## Source of authority and narrow fragment

No new resource semantics, parser rule, compiler lowering or provider/assurance
authority is introduced. The source producer remains the existing,
independently checked Grammar-v1 adapters:

- [`SourceScopedBorrowJoin`](../../src/Phil/Surface/GrammarV1/SourceScopedBorrowJoin.hs)
  for one source `if` with **two continuing** predecessors, no join-state
  telescope and a final Linear `Bytes[8]` owner return;
- [`SourceLinearLoopTransfer`](../../src/Phil/Surface/GrammarV1/SourceLinearLoopTransfer.hs)
  for one `Linear Bytes[8]` loop slot, one checked entry and static
  `continue`-backedge, optional second source owner and one optional scoped
  loan (L-2/L-3).

Both adapters already compare a source-derived production trace with the
ordinary non-tracing Surface checker. CORR-2 independently checks the recorded
resource collections against the **real native `Phil.Core.Context` operations**,
rather than accepting an event label or caller-supplied successor map as proof.
The new [strict test driver](../../test/Phase1FSEM01JoinLoopCorr2Main.hs)
re-parses source and invokes those original adapters; it does not construct a
synthetic accepted source event or alter the adapters.

## Positive cuts and precise rejection boundaries

| Fragment | Accepted native checkpoints | Failure or forgery rejection |
| --- | --- | --- |
| Continuing branch join | Both source branches return the exact unloaned Γ/A/Δ/loan context; each actual source-derived borrowed view is replayed through `Core.startSharedLoan` then `Core.endSharedLoan`; `Core.joinContinuing` preserves the original owner. | An escaping view yields only reached before/start/body/error cuts, never a closed loan, a fabricated partner branch or a joined successor. Attempting to move the borrowed owner checks the exact native `OwnerBorrowed` error. |
| One-slot Linear loop | `Core.consumeLinear` consumes the original owner, `Core.insertBinding` creates the exact fresh header, `Core.consumeLinear` consumes the continuing header, rebinding precedes `Core.joinContinuing` static reentry. | Reusing the stale source owner fails with exact `UnknownBinding`-derived `StructuralUse`; a second same-width owner cannot replace a live header (`DuplicateBinding`); an unproved invariant fails with `MissingEvidence`, before any backedge successor. |
| Closed scoped loop borrow | The checked L-3 source view creates precise loan-state cuts, then closes before the owner moves across the backedge. | The native owner cannot be consumed while borrowed, and `Core.joinContinuing` rejects an active-loan predecessor. |

The driver uses **eleven already parsed and source-checked specimens** from
`test/fixtures/fsem01-scoped-borrow-join-v1/`,
`test/fixtures/fsem01-linear-loop-transfer-v1/`, and
`test/fixtures/fsem01-scoped-linear-loop-loan-v1/`.
It independently refuses **nine altered observation cases**, including a
missing branch, forged joined or header state, fabricated loan or post-error
successor, missing move cut and foreign live-loan state. All four native
resource collections are checked, not merely owner counts. Prior accepted and
negative cases in the three predecessor drivers are rerun unchanged.

Unsupported source shapes—including general nested/dependent joins,
multi-slot loop state, arbitrary loop bodies, terminating branches and general
closures—are **outside this adapter's competence**, not normative invalid
source. Negative evidence is an exact class and payload for the stated tested
source shape, not a global guarantee about all errors.

## Rocq 9.2 correspondence boundary

The new [conditional composition model](../../proof/Phil/Surface/SurfaceSourceJoinLoopCorr2.v)
reuses the previously compiled `ContextJoin`,
`SurfaceSourceScopedBorrowJoin` and
`SurfaceSourceLinearLoopTransfer` definitions. It proves:

- A successful two-predecessor context join preserves an exact linear owner
  and requires both input loans and output loans closed.
- A checked model one-slot entry consume/rebind, continuing consume/rebind,
  distinct old/header identity and successful reentry preserve the new owner,
  do not resurrect the spent original owner, and leave no loan. An attempted
  duplicate insertion into the live header remains rejected.
- A still-active loan on the backedge prevents a valid two-predecessor
  reentry in the model.

The theorems are **conditional on the stated Rocq Core transition and join
relations**. The Haskell tests are finite native-source conformance, not an
extracted proof relating all Haskell `Map`/`Set`/`Text` operations to Rocq.
General source operational semantics and independent extracted interpreter
belong to FSEM-05; general implementation correspondence belongs to
FSEM-06. `satisfies C`/external assurance belongs to FSEM-04 and the separate
Phase 1 audit.

## Reproduction and admission gates

The dedicated
[`fsem01-corr2-join-loop-preflight.yml`](../../.github/workflows/fsem01-corr2-join-loop-preflight.yml)
checks actual GHC 9.6.7 `-Wall -Werror` source, existing predecessor cases,
strict Haskell resource replay and Rocq 9.2 compiled proof dependencies.
The proof job rejects `Admitted`/`Axiom`/`Parameter`, runs `rocq check`,
and records proof-source/compiled-object digests.

Before merge, record the **exact PR-head** tests, genuine error refusal,
complete CI/check census, active FSEM-01 claim and independent protected
claim guard. A green focused preflight alone is **not** a merge or an
independent FSEM-01/FSEM-07 closure claim.
