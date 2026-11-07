# FSEM-01 — bounded source-run to model simulation

> **Authority:** non-normative Phase 1 proof slice. This establishes a
> conditional, *source-observation* simulation for the precisely admitted
> single-linear-owner `Bytes[8]` borrow fragment. It does **not** establish
> universal correctness of the Haskell compiler or source typing.
> Tracks [issue #1613](https://github.com/abiggerhammer/phil/issues/1613).

## Claim and compositional boundary

The predecessor [#1638 observation-wire bridge](formal-semantics-observation-wire-fsem01-v1.md)
introduced versioned ASCII artifacts emitted from the actual Haskell
Grammar-v1 source checker and evaluated by a Rocq-proved decoder. The
[#1637 transition/error model](formal-semantics-step-error-bridge-fsem01-v1.md)
already proved that modeled borrow return and `BorrowEscape` rejection
are terminal, with no post-terminal successor. Neither result, alone,
established how a production *source run* relates to that model.

The [new theorem](../../proof/Phil/Surface/SurfaceBoundedSourceSimulation.v)
makes the **source-side trust premise a first-class proposition**.

`SourceRun` carries a source SHA-256 fingerprint, an exact
UTF-8-hex declaration root and owner/view name, canonical lexical
ordinals, observed trace codes, and a classified terminal outcome.
`SourceBindsArtifact run artifact` asserts equality of **all eight**
source-run fields with the corresponding decoded wire fields. This is
the *producer fidelity premise*. A decoder theorem cannot establish it
for arbitrary Haskell executions; that would require a verified
producer or additional refinement of the source evaluator.

`SourceOwnerCatalog catalog owner run` separately asserts:

- `NoDup catalog` for an exact, finite catalog of **hex-encoded roots**,
  rather than silently treating Unicode Haskell Text as Rocq String;
- the normalized model declaration ID points to the source-run root
  in that catalog;
- the normalized binder ordinal agrees with the exact canonical
  source ordinal.

The proof `catalog_bound_run_has_unique_model_owner` shows that one
source run cannot represent two normalized binder keys **within that
catalog**. Its positions are local observation IDs, not persistent
Phil declaration keys.

## Theorems and conclusions

`decoded_catalog_bound_source_simulates` requires the exact
`decodeArtifact wire = Some artifact` result, the
`SourceBindsArtifact` premise, and the finite catalog relation.
It concludes `BoundedSourceSimulation run owner`, meaning:

1. the run's classified outcome selects a sequence of modeled events;
2. replay from the unloaned linear owner reaches the matching
   terminal return or `BorrowEscape` state;
3. the final modeled state is classified as the same outcome;
4. **no** modeled event can follow that terminal state.

The proof composes the #1638
`decoded_wire_replays_one_terminal_model` theorem with the #1637
fail-closed step checker. `replay_preserves_exact_owner` proves
that model replay does not change binder identity;
`decoded_source_run_preserves_owner_to_terminal` applies this to the
bounded source run. Separate theorems rule out any nonempty
post-rejection or post-return replay.

This is a **bounded, conditional simulation of a trusted source
observation**, not a proof that `evalBorrowTraced` is correct for
unbounded source programs.

## Discharging the premises for real specimens

The updated
[observation CI workflow](../../.github/workflows/fsem01-observation-wire.yml)
continues to build and invoke the **actual** Haskell Grammar-v1 checker
and source fixtures, upload four source-derived artifacts, and verify
them independently against source bytes and committed goldens.

The new
[`fsem01_simulation_witness.py`](../../scripts/fsem01_simulation_witness.py)
checks the artifacts through the existing independent
[`fsem01_observation_wire.py`](../../scripts/fsem01_observation_wire.py)
validator, then recomputes the source hashes, UTF-8-hex names,
ordinals and expected control outcomes **from the fixture bytes and
known admitted fragment**. It generates a literal Rocq witness module,
with a local two-root catalog, showing for each of the four artifacts:

- the **exact wire bytes** decode to the expected record;
- the independent source-run fields match **all eight** decoded fields;
- the exact source root and ordinal map to a unique model owner;
- the conditional theorem yields `BoundedSourceSimulation`;
- the escaping traces have no modeled continuation.

The file is compiled with Rocq 9.2.0 and `vm_compute` on the exact
artifact bytes; all new proofs disallow `Admitted` and global axioms.
CI records SHA-256 digests for the artifacts, theorem source,
compiled proof objects, and generated witnesses. It does not quietly
replace real production artifacts with model-synthesized traces.

For review, a green CI result is a *specimen-specific discharge*
of the producer and catalog **observational premises**, carried by
a Python/Haskell test boundary. It is not a universal theorem that
the source producer is faithful, and a hash is not an authentication
signature.

## Remaining obligations

- General Haskell `evalBorrowTraced` semantics, including
  `containsBorrowedView`, arbitrary runtime value shapes and
  unobserved failure paths, are **not** formally simulated.
- Unicode Text↔Rocq String encoding and Haskell `Map`/`Set`
  operations have not been formally refined. The hex carrier and
  Python/Haskell source-name checks are explicitly trusted.
- The normalized catalog is **bound to these fixtures**. Its order
  or provenance cannot be promoted to a stable declaration authority.
- The theorem covers exactly source-observed successful
  `Bytes[8]` return or escaped-view rejection; no global affine,
  captured or nested borrow typing, join/backedge, effects,
  runtime certificates, or `satisfies C` is discharged.
- Future work could prove a producer refinement for the admitted
  fragment, verify an extracted source-checker observation function,
  or substantially extend model coverage with independent proof
  obligations. Avoid expanding the theorem's conclusion by merely
  changing the vocabulary of the source record.

**Bottom line:** it is now possible to inspect *which assumptions*
connect a real emitted artifact to a machine-checked model replay.
That is a useful simulation theorem with a deliberately bounded domain,
not a Phase 1 source type-soundness certificate.

## Subsequent pure producer-projection fidelity slice

[The producer-fidelity proof](formal-semantics-producer-fidelity-fsem01-v1.md) constructs both a source-run record and artifact from the same modeled raw checkpoint sequence and proves every field agrees, eliminating a separately postulated `SourceBindsArtifact` relation **for these constructed records**. It also proves each checkpoint code injectively preserves its phase and actual owner/loan bits. Real Haskell checker-state extraction, Unicode and SHA-256 remain explicitly outside the theorem.
