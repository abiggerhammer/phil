# PHIL-DATA-MODE-001 — aggregate structural mode proof v1

This proof certifies the normalized semantic core of Phase 1 aggregate structural mode and owning construction over the already implemented DATA-001–003, DATA-009, and DATA-014 conformance slices.

## Certified claims

`proof/Phil/Core/DataMode.v` proves:

- structural modes form the ordered chain `Unrestricted <= Affine <= Linear`;
- record mode is the LUB/strongest mode of every owned field;
- sum mode is conservatively at least as restrictive as every owned payload of every constructor;
- normalized generic mode parameters propagate their exact actual structural mode into the aggregate LUB;
- an unbound generic mode parameter fails closed rather than receiving an inferred default;
- an accepted nominal mode declaration can never weaken the content-derived minimum;
- strict nominal strengthening requires a separately admitted semantic justification;
- an admitted aggregate construction has at most one owning position for any affine/linear occurrence identity;
- supplying the same restricted occurrence to two owning positions rejects; and
- the imported Core linear-consumption theorem makes a successfully transferred linear source one-shot.

The proof intentionally composes `PHIL-CTX-LIN-001` for concrete one-shot linear removal rather than rebuilding ResourceContext semantics inside the data theorem.

## Haskell correspondence

The dedicated workflow leaves production unchanged and reruns the existing conformance corpus:

- DATA-001 unrestricted record mode;
- DATA-002 linear record construction/transfer;
- DATA-003 duplicate restricted source rejection;
- DATA-009 generic mode propagation/fail-closed unknown parameter; and
- DATA-014 nominal mode derivation, non-weakening, and justified strengthening.

It also typechecks `src/Phil/Core/DataMode.hs`, `src/Phil/Core/NominalDataMode.hs`, and those five test programs under `-Wall -Werror`.

## Residual boundary

This is semantic certification, not implementation refinement. The following remain explicit correspondence or trust boundaries:

- the concrete Haskell `Mode`, list, product, record, and sum representations;
- source/grammar elaboration of owned field and constructor payload mode lists;
- normalization of nested Haskell `ModeExpr` trees to the proof's strongest-mode atom list;
- concrete affine consumption and the exact Haskell aggregate-constructor orchestration around Core context operations;
- generic parameter-name/text correspondence;
- constructor/field metadata ordering, which is nonsemantic here;
- truth and competence of any resource/lifecycle/authority-lifecycle contract used to justify strict nominal strengthening;
- diagnostics and Haskell implementation equivalence; and
- Rocq kernel/toolchain correctness.

The theorem does not claim that every aggregate must be linear merely because it is nominal, nor that a programmer annotation can strengthen mode without an admitted semantic contract. It certifies the Phase 1 rule: derive the minimum from owned contents; explicit declaration may only preserve or justifiably strengthen it.
