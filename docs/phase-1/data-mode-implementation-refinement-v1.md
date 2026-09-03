# PHIL-DATA-MODE-001 — implementation refinement staging

This staging slice extracts bounded executable decisions from the semantics already Certified by `proof/Phil/Core/DataMode.v`. Production Haskell is unchanged here.

## Exact decision surface

The staged `DataModeKernel` owns four representation-neutral decisions:

1. exact strongest/LUB mode derivation for record fields and sum-constructor payloads;
2. strongest-mode folding after generic atoms have each been resolved to an exact mode or to a missing actual;
3. nominal declaration acceptance: omission keeps the derived mode, equality needs no strengthening justification, weakening rejects, and strict strengthening requires an independently accepted justification fact; and
4. restricted aggregate formation acceptance after concrete construction establishes that each restricted occurrence has one owning position.

`decideRecordModeByCandidate` and `decideSumModeByCandidate` accept exactly when the candidate equals the Certified `deriveRecordMode` / `deriveSumMode` result. `resolvedStrongestMode` is proved equal to Certified `instantiateStrongest` after `instantiateAtom` has resolved the normalized atom list. The nominal decision is proved never to weaken the derived mode, and every strict acceptance requires the explicit justification fact; a true fact plus a Certified admitted witness constructs the existing `NominalStrengthened` relation. The formation decision is equivalent to `AggregateFormationAccepted` under an explicit reflection bridge for restricted-occurrence uniqueness.

## Concrete/native boundaries

This staging kernel does **not** make first-implementation representation choices normative:

- concrete `Phil.Core.Syntax.Mode` representation and the bridge to extracted `Mode` remain native;
- source record/sum declaration elaboration and field/constructor ordering remain native;
- nested `ModeExpr` flattening remains native; the kernel begins only after each normalized atom is resolved to `Just mode` or `Nothing`;
- generic parameter names and environment lookup remain native, while a missing resolution must still fail closed;
- exact resource/lifecycle/authority-lifecycle justification identity, nonempty detail, admission provenance, and diagnostic choice remain native; the later binding may supply the strict-justification Boolean only after those real checks succeed;
- concrete `ResourceContext` lookup/consumption, occurrence identity, affine/linear one-shot transfer, and aggregate-construction orchestration remain native; and
- exact diagnostics and their ordering remain native.

A later production-binding closeout must derive each kernel input from the actual successful production checks. Native/kernel disagreement may only reject. In particular, it may not treat structural linearity alone as nominal strengthening authority, assign a mode to an unresolved generic actual, or permit one restricted source occurrence to satisfy two owning positions.

## Staging controls

The staging workflow freshly compiles `DataMode.v` and `DataModeImplementation.v` under Rocq 9.2.0, extracts `DataModeKernel.hs`, records exact proof/kernel identities, strict-typechecks and executes sixteen direct extracted-kernel controls, then reruns the unchanged DATA-001–003, DATA-009, and DATA-014 correspondence corpus:

- `test/Phase1DataModeMain.hs`
- `test/Phase1LinearRecordConstructionMain.hs`
- `test/Phase1DuplicateRestrictedFieldMain.hs`
- `test/Phase1GenericModePropagationMain.hs`
- `test/Phase1NominalModeStrengtheningMain.hs`

A green staging merge leaves `PHIL-DATA-MODE-001` at `Discharged / Certified`. Only a separate exact-kernel production binding may promote it to `Discharged / Implementation Refined`.
