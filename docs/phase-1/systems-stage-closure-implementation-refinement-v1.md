# Systems stage closure implementation refinement v1

`PHIL-SYS-STAGE-CLOSURE-001` is already Certified by PR #440. This tranche stages only its representation-neutral executable decision surface. Production Haskell behavior is unchanged here; a separate exact-kernel production-binding closeout is required before the ledger may move to `Discharged / Implementation Refined`.

## Certified surface being extracted

The Certified theorem joins the coarse source/target StageContract closure envelope with final SYS-020 identity closure. The implementation-correspondence layer extracts four decision families.

### Source closure

`decideSourceClosureByFacts` owns the ordered semantic gates for:

1. exact coverage of every live source responsibility by one disposition;
2. rejection of the empty source-fact identity; and
3. validity of every disposition, including known target-mechanism references, nonempty export revisions, and nonempty assumption identities.

Concrete extraction/enumeration of source facts, edges, obligations, and disposition maps remains native Haskell correspondence work.

### Target closure

`decideTargetClosureByFacts` owns:

1. exact coverage of every live target mechanism by kind plus justification;
2. rejection of the empty target-mechanism identity; and
3. validity of every target justification: source refs remain live and at least one source, realization, qualification, or derived-obligation reason exists.

Concrete mechanism-kind construction, map/set domains, and detailed diagnostic payload recovery remain native.

### Final SYS-020 identity closure

`decideStageIdentityByFacts` owns the Certified ten-gate final identity relation, in theorem order:

1. concrete/next-stage SubjectStage revision equality;
2. ArchitectureInstance revision equality;
3. realization revision equality;
4. Systems revision equality;
5. coarse Phase-1 StageContract revision equality;
6. verifier-profile equality;
7. recomputed Systems revision equals stored Systems revision;
8. recomputed final closed StageContract revision equals stored final revision;
9. stored Systems revision is present/nonempty; and
10. stored final revision is present/nonempty.

The concrete `Text` revision representation and canonical `SemanticForm` encoder are not claimed by Rocq. Revision construction is separately machine-bound by `PHIL-SYS-REV-001`; this kernel owns only the closure/equality dependency structure.

### Cumulative closure

`decideSystemsStageClosureByFacts` composes, in Certified predecessor order:

1. Certified source-fact verification;
2. exact source-fact projection into the generalized closure responsibility map;
3. source closure;
4. target closure;
5. Certified validity-scope match; and
6. final identity closure.

`PHIL-SYS-FACT-001` and `PHIL-ASSURE-VALIDITY-001` therefore remain explicit Certified predecessor facts. This Stage Closure layer does not duplicate their verifiers.

## Extraction boundary

The extractor maps Coq `bool` directly to `Prelude.Bool`, so the generated kernel composes with native Haskell booleans without an extra representation bridge.

Still outside this extracted kernel are:

- concrete Haskell `Text`, revision, `Map`, `Set`, and list representation/equality;
- enumeration and derivation of live source responsibilities and target mechanisms;
- exact source-fact projection construction;
- target mechanism kind construction;
- canonical Systems and StageContract revision serialization/digest construction;
- witness-specific concrete-trunk selection;
- exact diagnostic precedence and payload construction;
- truth of Certified predecessor facts and external evidence;
- Haskell/Rocq/toolchain and runtime/backend correctness.

## Staging verification

The existing `Phase 1 Systems Stage Closure Proofs` workflow is extended to:

- recompile the Certified predecessor/proof chain plus the implementation-correspondence theorem;
- fresh-extract `SystemsStageClosureKernel.hs` under Rocq 9.2;
- strict-typecheck the raw extracted kernel;
- execute 26 direct controls covering acceptance plus every ordered failure class;
- strict/typecheck the unchanged coarse and final production implementations with only their already-documented inherited warning exemptions;
- rerun the unchanged 16-case coarse StageContract corpus plus 20-case final StageClosure corpus (36 cases total); and
- record exact proof, extraction, production, harness, test, and document identities.

A green staging matrix leaves `PHIL-SYS-STAGE-CLOSURE-001` at `Discharged / Certified`.

Baseline: `68a754e59a01e3d1e9ce80abd276c407d38c714d` (#527 merge).
