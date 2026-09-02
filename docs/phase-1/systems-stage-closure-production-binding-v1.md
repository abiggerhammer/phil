# Systems stage closure production binding v1

`PHIL-SYS-STAGE-CLOSURE-001` was Certified by PR #440 and its representation-neutral executable decision surface was staged by PR #530. This closeout binds final production StageClosure acceptance to that exact extracted kernel without moving concrete representation, enumeration, canonical revision construction, or detailed diagnostic payload recovery into Rocq.

## Exact staged kernel

The green #530 staging run fresh-extracted `SystemsStageClosureKernel.hs` under Rocq 9.2.0 with SHA-256:

`7f37e2760054fdc2ffcb30ee571ff6da9445e29f652f228ec9c53ddc1097dd4a`

The exact raw bytes are checked in at:

- `generated/SystemsStageClosureKernel.hs`
- `src/SystemsStageClosureKernel.hs`

Unlike several earlier Rocq Haskell extractions, this kernel maps Coq `bool` directly to `Prelude.Bool` and therefore uses its qualified Prelude import. The strict production mirror is byte-identical to the raw staged extraction; no local warning pragma is needed.

## Production binding

`Phil.Systems.StageClosure.verifyStageClosureBundle` continues to run the existing concrete predecessor verifiers first. Those predecessor verifiers own concrete lookup/enumeration and exact nested diagnostic payloads.

After concrete and next-stage predecessor verification succeeds, StageClosure reifies the already-established coarse source/target closure facts into the exact extracted decision surface:

- source disposition-domain coverage is recomputed from the concrete `Phase1StageBundle`;
- target justification-domain coverage is recomputed from the same bundle;
- disposition and justification validity are reflected from the already-successful native predecessor verification;
- the normalized no-empty-identity facts remain part of the already-established concrete identity/certified-predecessor bridge rather than introducing a second `Text` interpretation here.

The extracted source/target classifiers must accept. Any disagreement after native predecessor success is an impossible correspondence mismatch and fails closed.

For SYS-020 final identity closure, the extracted classifier directly owns the ordered decision over:

1. SubjectStage revision equality;
2. ArchitectureInstance revision equality;
3. realization revision equality;
4. Systems revision equality;
5. coarse StageContract revision equality;
6. verifier-profile equality;
7. recomputed Systems revision equality;
8. recomputed final StageContract revision equality;
9. stored Systems revision presence; and
10. stored final StageContract revision presence.

Each ordinary mismatch class is mapped back to the exact existing `StageClosureVerificationError` payload. The two stored-presence branches are unreachable after equality with the nonempty canonical recomputations and therefore fail closed if the concrete correspondence ever disagrees.

Finally, the extracted cumulative classifier composes the reflected Certified fact-verification and fact-projection predecessors, accepted source closure, accepted target closure, reflected Certified validity-scope predecessor, and accepted final identity closure. Successful final StageClosure verification therefore depends on exact kernel acceptance.

## Preserved correspondence boundary

This production binding does **not** claim that Rocq proves:

- Haskell `Text`, revision, `Map`, `Set`, or list representation/equality;
- extraction/enumeration of source responsibilities or target mechanisms;
- concrete fact-projection or mechanism-kind construction;
- the detailed native disposition/justification diagnostic payloads;
- `SemanticForm` serialization or canonical revision construction;
- SHA-256 collision resistance/injectivity;
- witness-specific concrete-trunk selection;
- truth of external Assurance/fact/validity evidence beyond the already-Certified predecessor interfaces;
- physical runtime/backend behavior; or
- Rocq/GHC/toolchain correctness.

`PHIL-SYS-REV-001` separately owns the machine-refined canonical revision-construction dependency structure.

## Exact-head closeout gate

The dedicated `Phase 1 Systems Stage Closure Production Binding` workflow must:

1. recompile the Certified proof and implementation-correspondence theorem under Rocq 9.2.0;
2. fresh-extract `SystemsStageClosureKernel.hs`;
3. require exact SHA-256 `7f37e2760054fdc2ffcb30ee571ff6da9445e29f652f228ec9c53ddc1097dd4a`;
4. byte-compare the fresh kernel with both checked-in raw/production copies;
5. strict-typecheck the exact kernel and the bound StageClosure path, retaining only the already-documented inherited SYS-009/010 warning exemptions;
6. execute the same 26 direct decision controls through the production kernel; and
7. rerun the unchanged 36-case coarse/final closure corpus (16 + 20).

Only a fully green exact-head closeout permits promoting `PHIL-SYS-STAGE-CLOSURE-001` from `Discharged / Certified` to `Discharged / Implementation Refined`.
