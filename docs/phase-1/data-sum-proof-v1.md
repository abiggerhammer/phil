# PHIL-DATA-SUM-001 — resource-bearing sum proof

This proof certifies the Phase 1 resource-bearing sum and branch-state semantics over the already implemented DATA-007, DATA-008, and DATA-013 conformance slices.

## Certified semantic core

`proof/Phil/Core/DataSum.v` composes three already Certified dependencies instead of duplicating them:

- `PHIL-DATA-MODE-001` supplies conservative whole-aggregate structural mode;
- `PHIL-DATA-ELIM-001` supplies exact constructor-local restricted-payload disposition; and
- `PHIL-RES-JOIN-001` supplies structural reconvergence of unrestricted, affine, and linear resource state.

The sum-specific theorem proves:

- every owned constructor payload contributes monotonically to the whole sum mode;
- pattern matching selects exactly one declared constructor payload and manufactures no payload for an unknown constructor;
- a continuing arm must account for every selected linear payload, and an unaccounted linear payload makes that arm inadmissible;
- any linear owner present after successful reconvergence was present at the same name and type in every continuing predecessor;
- successful join cannot synthesize a linear owner that was absent in a predecessor;
- two branches with mismatched raw linear ownership shapes cannot satisfy the successful join relation; and
- after each branch explicitly packages its local owner into the same linear sum/state name and type, ordinary successful join preserves that explicit owner unchanged.

This is the semantic reason Phase 1 requires explicit sum/option/state packaging or an otherwise compatible `JoinContract`: hidden compiler-synthesized optional ownership is not part of the admitted model.

## Correspondence gate

The dedicated `Phase 1 Data Sum Proofs` workflow compiles under Rocq 9.2.0, records source and `.vo` identities, typechecks the unchanged implementation/test paths under `-Wall -Werror`, and reruns the unchanged correspondence corpus:

- `Phase1ConservativeSumModeMain.hs` — 4 cases;
- `Phase1ConsumingSumMatchMain.hs` — 3 cases;
- `Phase1SumArmLinearLeakMain.hs` — 3 cases; and
- `Phase1ExplicitBranchResourceSumMain.hs` — 3 cases.

## Residual assumptions / non-claims

This is semantic certification, not implementation refinement. The following remain explicit boundaries:

- concrete Haskell `Map` representation and diagnostic ordering;
- source sum declaration, constructor-tag, and payload-field correspondence;
- source pattern-arm elaboration and exhaustiveness checking outside this obligation;
- concrete package/unpackage orchestration and exact correspondence to the normalized proof constructors;
- any future hidden optional-ownership representation (explicitly not admitted in Phase 1);
- Haskell implementation equivalence; and
- Rocq kernel/toolchain correctness.
