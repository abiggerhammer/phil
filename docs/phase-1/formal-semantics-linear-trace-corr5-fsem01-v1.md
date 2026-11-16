# FSEM-01 CORR-5: source-derived executable finite Linear traces

> **Non-normative, bounded proof and source/byte conformance slice**, [FSEM #1613](https://github.com/abiggerhammer/phil/issues/1613). Follows protected CORR-4 #1817, CORR-3 #1815 and bounded source-observation work #1638–#1641. Does **not** close FSEM-01, FSEM-05/06 or the global production-refinement proof.

## Computed traces rather than supplied transitions

The [model](../../proof/Phil/Surface/SurfaceFiniteLinearTraceCorr5.v) composes the genuine CORR-4 finite Linear consumption and insertion decisions into an executable trace replay. For **every** finite sequence and initially related extensional Core context, the theorem **corr5_arbitrary_finite_trace_refines_core_model** establishes ordered, full-domain four-zone resource-state correspondence and identical success or first-failure index/reason. **corr5_first_failure_blocks_any_later_commands** proves that appending operations after the first failed prefix cannot execute them or fabricate a successor. There are no new axioms, Parameters or Admitted proofs. Rocq's coarse missing-Linear error is expressly different from native Haskell's additional WrongStructuralMode diagnostics.

## Canonical actual-source transcript bytes

The new [source-driven Haskell producer](../../test/Phase1FSEM01Corr5ReplayMain.hs) reparses and checks six genuine Grammar-v1 loop fixtures and replays their reached Core entry/continue/rebind/error transitions before emitting **seven** actual observations. The seventh uses a genuine live-loan checkpoint from the admitted closed-loan fixture to test a borrowed-owner refusal, not an invented source-language operation.

Each ASCII artifact begins with **PHIL-FSEM01-CORR5-V1|** and has eight canonical decimal-length-framed fields: exact source SHA-256; declaration root UTF-8 hex; resolved flag, old owner and loop-header Core.Name UTF-8 hex; optional alternate source owner hex or a dash; observed bounded step profile; and exact source/result classification. Profiles are OK/DONE, ST/MISSING, DU/DUPLICATE, GA/GATED or LO/LOAN. The GA case contains valid initial resource transitions but stops at the **separate source invariant MissingEvidence** gate, which is never misrepresented as a Core resource failure. The LO case starts at an actual active-loan cut.

The [Rocq decoder](../../proof/Phil/Surface/SurfaceSourceLinearTraceWireCorr5.v) reuses the existing proved source-observation framing and rejects incompatible versions, malformed fields, trailing bytes, invalid hex, aliased identities and mismatched profile/result combinations. It derives actual finite initial states and commands from the decoded source-rooted name tokens and computes the replay; results are not accepted from caller assertions.

The independent [Python validator](../../scripts/fsem01_corr5_source_witness.py) checks the emitted ASCII bytes against original fixture source SHA-256, source-root/binder UTF-8 bytes, exact grammar-bound ordinals, finite source shape and adversarial mutations. It creates a literal-input Rocq witness that runs the decoder and replay using the **actual Haskell-emitted bytes**, with universally quantified opaque Bool and Bytes[8] Rocq type parameters. Native source typing and GHC/UTF-8/Map/Set correctness remain explicit separate boundaries; this does not prove arbitrary Haskell↔Rocq representation.

The focused CI strictly checks GHC 9.6.7 warning-free source replay and byte production, canonical source validation, Rocq 9.2 compiled proofs and actual wire replay, and source/compiled hashes. Source checker, production Core, grammar, 244 normative cases, privileged release, P8/P9 and TCB remain unchanged.

## What remains after CORR-5

This strengthens FSEM-01 rule family **R15** and bounded Linear/loop evidence in R04/R12. **All 15 R01–R15 families still have some generalization or implementation-identity gap.** The largest unfinished groups are general source binder/lifecycle/loan representation (R01–R07), nested product and aggregate sources (R08/09/14), dependent or multi-slot joins and terminal exclusions (R10/11), general loops including cross-backedge loans (R12), closure capture/callable body recursion (R13), and universal native error/state/source↔Rocq refinement (R15). FSEM-05/06 reference execution and realization are distinct later tasks; passing this bounded slice does not graduate them.

Credit only after strict exact-head full CI, fresh post-ready claim guard, protected merge and trusted release of the original unique FSEM-01 claim.
