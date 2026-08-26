# Phase 1 Systems final revision closure v1

Status: bounded executable conformance slice for `SYS-020`.

## Governing rule

The final Phase 1 Systems boundary needs recomputable identities, not build-run identities.

The governing SYS-020 rule is:

> Semantically irrelevant ordering, diagnostic names, source formatting, traversal accidents, temporary paths, and inspection prose do not change `SystemsArtifactRevision` or the closed `StageContractRevision`. Identity-bearing logical Systems or preservation-relation changes do.

This is the final implementation slice of the Phase 1 Systems/StageContract tranche. It does not certify the still-open Rocq closure proofs; it closes the executable revision/canonicalization structure that those proofs will refer to.

## Phase 0 remains frozen

Phase 0 keeps its existing `systemsArtifactDigest` behavior unchanged.

SYS-020 changes only `Phil.Systems.Phase1Stage.deriveSystemsArtifactRevision`. Phase 1 first normalizes the logical artifact for identity, then reuses the mature legacy digest over that normalized artifact.

This avoids rewriting the frozen Phase 0 baseline while giving Phase 1 the stronger ADR-019 identity semantics required by the generic StageContract.

## Phase 1 Systems normalization

The Phase 1 identity normalization preserves executable and assurance meaning while removing representation noise that the governing contract declares nonsemantic.

Canonicalization currently does the following:

- function, value, block, invariant, and lowering-decision maps are already key-canonical through the existing digest machinery;
- executable operation order is preserved;
- diagnostic operation **presence and position** remain visible, but diagnostic display names normalize to one token;
- `DiagnosticState` display labels normalize likewise;
- set-like StageContract lists are sorted before hashing:
  - source fact transfers;
  - required edges;
  - derived obligations;
  - assumptions;
  - trace-relation declarations;
  - resource/failure relation declarations;
- set-like lists inside lowering decisions are sorted;
- lowering inspection plans are excluded from Phase 1 Systems identity because they are verifier/debugging instructions rather than executable or assurance semantics;
- normalized target-program digests are rethreaded through the StageContract and lowering ledger;
- lowering decision digests and the ledger root are recomputed from normalized content.

Source text/formatting is not an input to this canonicalizer at all. The Systems boundary receives semantic artifact identities and logical lowering decisions, not source whitespace.

## What remains identity-bearing

SYS-020 deliberately does **not** normalize away:

- function/block/value logical identity;
- executable operation order;
- runtime/provider operation identity;
- trace events and commit semantics;
- control-flow targets;
- resource/failure behavior;
- subject/evidence/authority/protocol/boundary relations;
- selected representations and lowering actions;
- target preconditions and derived obligations;
- runtime primitive/profile choices;
- realization effects;
- cost classes/shapes/charges;
- exact next-stage requirements.

Changing one of those facts must change the appropriate revision.

## Diagnostic names and the coarse SYS-001 envelope

The original SYS-001 mechanism key included the `OpDiagnostic` display name. That accidentally made a diagnostic rename change `Phase1StageContractRevision` even when no semantic relation changed.

SYS-020 fixes that boundary: a diagnostic operation is keyed as `diagnostic`, independent of its display label. Its logical occurrence and position remain visible.

## Joining the two StageContract trunks

After `SubjectStage`, the Phase 1 implementation developed two relation trunks.

The concrete correspondence trunk contains the source-to-target relations from SYS-004 onward:

```text
Subject
  -> Provider call
  -> Authority/effect
  -> Branch resource/failure
  -> Control state
  -> Protocol state          (when applicable)
  -> Boundary commit         (when applicable)
```

The assurance/realization/runtime trunk contains:

```text
Subject
  -> Evidence transfer
  -> Evidence erasure
  -> Assumption dependency
  -> Target strengthening
  -> Runtime claim binding
  -> Primitive reuse
  -> Staging effects
  -> Cost attribution
  -> Next-stage requirements
```

`Phil.Systems.StageClosure` joins these trunks at their exact common `SubjectStage` and common SYS-001 envelope.

The verifier requires exact agreement on:

- `SubjectStageRevision`;
- `InstanceRevision`;
- `RealizationRevision`;
- Phase 1 `SystemsArtifactRevision`;
- the coarse `Phase1StageContractRevision`; and
- verifier-profile revision.

It then runs the complete verifier for each terminal trunk before accepting the final closure.

## Applicability is explicit, not cosmetically symmetric

The current witnesses do not exercise identical concrete relation categories.

- Framed upload closes its concrete trunk through `BoundaryCommitStageBundle` because protocol and exact typed send/receive boundaries are part of its semantics.
- Steve closes its concrete trunk through `BranchResourceStageBundle`; its current provider-local CAS operations do not have a Phil protocol/boundary relation to invent.

`ConcreteStageClosure` therefore records whether the applicable concrete relation closes through branch/resource or boundary correspondence. That choice is itself identity-bearing in the final closed StageContract revision.

## Final closed StageContract revision

`ClosedStageContractRevision` is canonical over:

- exact instance revision;
- exact realization revision;
- recomputed Phase 1 Systems artifact revision;
- coarse Phase 1 StageContract revision;
- exact common SubjectStage revision;
- applicable concrete-trunk kind and terminal revision; and
- exact SYS-019 next-stage requirement stage revision.

The stored final Systems and StageContract revisions are checked by recomputation. Stale values reject.

## Cross-witness closure is impossible

Because both relation trunks must name the same exact common SubjectStage and SYS-001 envelope, an upload concrete trunk cannot be paired with Steve's next-stage trunk, or vice versa. Such a candidate fails before it can become a closed StageContract.

This is useful pressure on a future independent lowering producer: constructing two individually valid relation fragments is insufficient unless they describe the same exact lowering.

## Conformance corpus

The dedicated SYS-020 corpus covers:

- positive final closure for framed upload and Steve;
- exact agreement of the two relation trunks;
- recomputation of final Systems identity;
- invariance under semantically unordered StageContract-list order;
- invariance under set-like lowering-list order;
- invariance under lowering inspection-plan prose;
- diagnostic-name invariance for both Systems and coarse StageContract identity;
- revision changes under identity-bearing trace changes;
- final-closure invariance under next-stage registry reconstruction;
- final-closure revision change under an identity-bearing next-stage requirement change;
- final-closure revision change when the concrete terminal relation revision changes;
- stale stored Systems and StageContract revisions;
- cross-witness trunk substitution; and
- deterministic reconstruction of the complete closed bundle.

## Deferred proof work

SYS-020 closes executable implementation, not proof certification.

The Logic Ledger therefore remains honest:

- `PHIL-SYS-STAGE-CLOSURE-001` remains **Active / Tested** until the generalized stage-closure proof/certification is completed;
- realization and runtime-graph proof obligations remain separately tracked;
- later independent compiler/checker implementations must reproduce equivalent canonical semantics rather than byte-identical internal data structures.

## Consequence

With SYS-020 implemented, SYS-001 through SYS-020 form one executable Systems/StageContract tranche. Both required Phase 1 witnesses have deterministic logical Systems identity, deterministic cross-stage contract identity, explicit target/runtime/cost/next-stage relations, and a verifier-visible seam suitable for the upcoming source grammar/elaboration and integration work.
