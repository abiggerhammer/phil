# Phase 0 source-to-Systems projection v1

## Purpose

This slice removes the synthetic source authority previously carried by the hand-built Phase 0 Systems graph. The checked `examples/upload/client.phil` and `examples/upload/server.phil` pair now supplies the concrete source artifact identity for the Phase 0 upload pipeline.

The bridge is deliberately **template-directed**. It is not a claim that arbitrary Phil programs can already be lowered to Systems IR.

The implementation lives in the sibling `phil-phase0-projection` package and consumes only the public Phil interfaces exposed by `phil-core`.

## Projection contract

`Phil.Phase0UploadProjection.projectPhase0UploadSources`:

1. parses exactly one `UploadClient` and one `UploadServer` component;
2. checks both with the existing Phase 0 Surface environments;
3. normalizes each checked AST to a semantic operation/branch trace;
4. requires those traces to match the frozen Phase 0 upload protocol shape;
5. independently digests the exact client and server source texts, then domain-separates and digests the labeled pair;
6. rebinds the canonical Phase 0 base Systems artifact to that source-pair digest;
7. rederives every lowering-decision digest and lowering-ledger root;
8. verifies the rebound base Systems artifact and scalar dataflow;
9. verifies the already-landed semantic successor chain through `StorageFailure`;
10. source-rebinds that final semantic artifact without changing its Systems program;
11. rederives its lowering metadata and assurance manifest/context; and
12. verifies the final rebound Systems artifact again.

The resulting stage contract is:

```text
surface-to-systems/phase0-upload/v1
```

and carries the exact source-pair digest in `stageSourceArtifactDigest` and every lowering decision.

## Why template-directed is sufficient for Phase 0

The Phase 0 upload programs are frozen reference programs. The current Systems implementation was intentionally developed and verified in semantic slices before the full source bridge existed. Reimplementing all those transformations inside a second lowering path would create a new source of semantic drift.

Instead, this slice establishes a narrow authoritative projection:

```text
checked frozen source pair
    -> exact normalized upload semantic trace
    -> canonical Phase 0 Systems graph
    -> already-verified semantic successor chain
```

A source pair that parses and typechecks but has a different normalized semantic trace is rejected rather than silently mapped to the canonical graph.

Whitespace/comment-only changes may preserve the semantic trace, but they change the source-pair digest. Thus semantic identity and content identity remain distinct and explicit. The pair digest independently commits to each file before combining them, so client/server boundaries cannot be shifted by delimiter-like source text.

## Downstream continuity

The focused gate lowers the projected final Systems artifact through:

```text
phil-runtime/phase0/control-codec-v1
```

using the landed control-codec lowerer and a verification context rebound to the projected Systems artifact. This proves that the real source-bound artifact can feed the current backend without falling back to the old synthetic source digest.

## Authority boundary

This slice claims:

- the frozen checked `client.phil`/`server.phil` pair is the source authority for the Phase 0 upload Systems graph;
- the exact source texts and their file boundaries are content-bound;
- the checked AST semantic trace is constrained before template selection;
- the base and final Systems programs are unchanged by source rebinding;
- all lowering-decision digests and ledger roots are rederived after rebinding;
- Systems verification and scalar-dataflow verification pass on the rebound artifacts; and
- the final projected artifact can be lowered and translation-verified through the current control-codec LLVM target.

It does **not** claim:

- generic `.phil` -> Systems CFG/dataflow lowering;
- that every future source program can reuse the Phase 0 upload template;
- proof authority for this projection beyond the checked Haskell correspondence gate;
- operating-system I/O; or
- the final integrated native upload demonstrator.

The integrated native demonstrator and its closure certification have since landed as the final Phase 0 implementation and assurance tranches.

## CI regression entrypoint

This document remains normative for the projection boundary. The post-freeze CI normalization adds `scripts/ci/phase0-source-projection.sh` only as a repo-local orchestration entrypoint for reproducing the existing projection gate; it does not change this contract or its authority.
