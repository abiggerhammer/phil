# FSEM-01 — bounded observation producer-fidelity proof

> **Status:** non-normative, bounded proof of the *pure observation
> projection* with actual production-checker correspondence tests.
> This is NOT a general proof of the Haskell evaluator, source elaborator,
> UTF-8 runtime, or SHA-256 implementation.
> Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613).

## What changes from #1640

The previous [bounded source-observation simulation](formal-semantics-source-simulation-fsem01-v1.md)
required the proposition `SourceBindsArtifact run artifact` as an
independent **producer-fidelity premise**. That premise equated the
source-run's digest, root, owner and view names, ordinals, trace, and
outcome with all eight artifact fields, but it did not follow from a
verified producer construction.

[SurfaceObservationProducerFidelity.v](../../proof/Phil/Surface/SurfaceObservationProducerFidelity.v)
introduces the *pure projection* performed after observation:

- `ProducerInputs`: exact source SHA-256 token, root/name
  UTF-8-hex tokens, and owner/view ordinal tokens.
- `RawCheckpoint`: observed phase, linear-owner membership, and
  active-loan membership. The two bits are stored explicitly; they
  are **not inferred** from a phase label when serialized.
- `renderCheckpoint` and `renderCheckpoints`: the seven possible
  phase tags with exact membership bits and comma-separated framing.
- `produceArtifact` and `produceRun`: two views of the **same
  inputs and raw checkpoint sequence**, producing exactly the
  eight-field v1 record and the source-run model.

The new theorem
`produced_run_binds_every_artifact_field` **derives**
`SourceBindsArtifact (produceRun inputs cuts outcome)
(produceArtifact inputs cuts outcome)` by construction.
`produced_metadata_is_not_rewritten`,
`produced_trace_codes_equal_actual_snapshot_projection`, and
`produced_terminal_code_matches_source_terminal` prove that
no field, phase, membership bit, or terminal classification changes
within this pure representation step.

The theorem `rendering_one_checkpoint_is_injective` proves distinct
phase/owner/loan triples cannot share a checkpoint code. The canonical
successful and escaping-borrow snapshot sequences
are additionally proved to render to the two precise v1 trace
strings. In the escaping path, the owner remains present with an
active loan at rejection; there is no invented closure or return.

## Composition with the checked decoder and model

`exact_produced_record_simulates` takes **one remaining explicitly
stated format-validity premise**:

~~~coq
SurfaceObservationWire.validArtifact
  (produceArtifact inputs cuts terminal) = true
~~~

From that premise, #1638's proven decoder roundtrip and the
by-construction `SourceBindsArtifact` theorem discharge the premises
of #1640's source-observation simulation theorem. The result
establishes terminal model replay, owner preservation and
no post-terminal successor. The accepted and rejected specializations
are `accepted_producer_record_simulates` and
`rejected_producer_record_simulates`. The latter has a separate
`rejected_producer_record_cannot_continue` theorem.

This is a **proven producer projection**, not a theorem that the
Haskell checker necessarily creates the projected `RawCheckpoint`
values. `validArtifact` is not a source typing judgment.

## Evidence against the actual Haskell producer

The existing
[Phase1FSEM01ObservationWireMain.hs](../../test/Phase1FSEM01ObservationWireMain.hs)
continues to drive the real Grammar-v1 parser, production declaration
identity derivation, and production checker/tracer. This slice
adds `checkProducerProjection`, which independently reconstructs:

1. the exact source-text digest and declaration root;
2. the actual generated owner/view name and ordinal;
3. every actual linear-owner and active-loan membership snapshot;
4. the actual checker terminal outcome, matched to the ordinary checker.

It checks that all eight emitted fields agree with that independently
reconstructed record, and deliberately changes a source-derived
checkpoint's owner name, owner type, set of owners, shared-loan set,
and phase. Those mutations must fail the projection or the v1
format validator. The workflow still generates all four
[canonical observation specimens](../../test/fixtures/fsem01-observation-v1/expected),
checks exact file bytes and source SHA-256 with an independent Python
validator, and passes **the actual emitted files** to the Rocq
decoder and source-simulation witnesses.

The updated
[fast proof preflight](../../.github/workflows/fsem01-source-simulation-proof.yml)
compiles the new theorem independently of the Haskell build. The
[full observation workflow](../../.github/workflows/fsem01-observation-wire.yml)
compiles it again next to the actual generated wire witnesses.
Both reject global `Axiom` or `Admitted` declarations in the new
proof. Only green CI on the exact PR head is acceptance evidence.

## What remains trusted

- The connection **from the actual Haskell evaluator to the Rocq
  `RawCheckpoint` model** is tested on admitted runs, not proved
  for every input. The pure projection's fidelity theorem does not
  imply all checker-produced states are accurate.
- `Data.Text` Unicode handling, UTF-8 bytes, SHA-256, actual
  `Map`/`Set` implementations and the checker runtime value
  escape detection are not formally refined to Rocq.
- The admitted source fragment is one `Bytes[8]` linear owner,
  one borrow and one terminal return or `BorrowEscape`, including
  the test-only finite owner catalog. General source typing and
  `satisfies C` remain unproved.
- The theorem connects valid records to a **model** replay. It
  cannot substitute for a compiler or evaluator correctness theorem.

**Next defensible target:** isolate the production snapshot extractor
as a smaller, independently testable Haskell function, or verify an
extracted version of the projection, and prove preservation of
checker-state membership at each observation point. This would narrow
the remaining runtime-to-model trust boundary, instead of quietly
treating it as discharged.
