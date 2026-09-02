# Systems realization effects implementation refinement v1

`PHIL-SYS-REALIZE-001` is already Certified by PR #447. This tranche stages only its representation-neutral executable decision surface. Production behavior remains unchanged here; a separate exact-kernel production-binding closeout is required before the ledger may move to `Discharged / Implementation Refined`.

The Certified aggregate composes the now-machine-bound `PHIL-SYS-STAGE-CLOSURE-001` predecessor with SYS-014 target strengthening, SYS-017 target-inserted staging consequences, and SYS-019 explicit next-stage competence-boundary export.

## SYS-014 target strengthening

`decideTargetStrengtheningByFacts` owns the ordered semantic gates for:

1. exact coverage of live target-strengthening facts;
2. nonempty exact introducer identity;
3. source assurance, when cited, is already known at the source boundary;
4. absence of source assurance requires an explicit derived obligation;
5. nonempty derived-obligation revision;
6. exact derived-obligation introducer relation;
7. at least one semantic subject;
8. an explicit proposition/refinement statement; and
9. an explicit acceptance rule.

Concrete `DecisionId`/`RevisionId`/`Text` representation, lowering-ledger and StageContract registry construction, `Map`/`Set` domain derivation, and exact diagnostic payloads remain native correspondence work.

## SYS-017 target-inserted staging

`decideStagingEffectByFacts` owns:

1. exact coverage of live staging requirements by events;
2. nonempty staging-requirement identity;
3. explicit realization effect;
4. explicit authority account;
5. explicit valid failure account, including explicit infallibility as distinct from omission;
6. explicit semantic-subject transfer revision;
7. explicit target-required cost identity;
8. bytes-copied accounting; and
9. frequency accounting.

Concrete source-site/profile/subject lookup, event/map keys, authority-use representation, target-subject equality, cost-class/shape representation, cost-identity separation, and detailed errors remain native. Those concrete checks are stronger representation-level checks around the normalized Certified semantic relation, not extra Rocq claims.

## SYS-019 next-stage export

`decideNextStageExportByFacts` owns:

1. exact coverage of every live target/runtime basis;
2. nonempty requirement revision;
3. nonempty exact Systems provenance;
4. nonempty required fact/contract identity;
5. rejection of folklore-only requirements;
6. an explicit acceptance rule; and
7. a nonempty validity scope.

Concrete canonical revision calculation, collision detection, exact basis/revision map construction, source-reference representation, and final exact expected-entry comparison remain native.

## Cumulative composition

`decideSystemsRealizationEffectsByFacts` composes, in Certified theorem order:

1. accepted `PHIL-SYS-STAGE-CLOSURE-001` identity closure;
2. accepted SYS-014 target-strengthening closure;
3. accepted SYS-017 staging-effect closure; and
4. accepted SYS-019 next-stage requirement closure.

Stage Closure is no longer merely an assumed design seam: its exact production-bound kernel was closed by #530/#534. The later production-binding tranche for this obligation may therefore consume an actual mechanically bound predecessor result rather than duplicating Stage Closure logic.

## Staging verification

The existing `Phase 1 Systems Realization Effects Proofs` workflow is extended to:

- compile the Certified theorem plus implementation-correspondence theorem;
- fresh-extract `SystemsRealizationEffectsKernel.hs` under Rocq 9.2;
- map Coq `bool` directly to `Prelude.Bool`;
- strict-typecheck the extracted kernel;
- execute 33 direct controls covering acceptance plus every ordered failure class;
- strict-typecheck the unchanged production SYS-014/017/019 surfaces with only the already-documented inherited RuntimeClaimBinding warning exemption;
- rerun the unchanged 68-case correspondence corpus (14 + 29 + 25); and
- record exact proof, kernel, production, test, harness, and staging-document identities.

## Residual boundary

This refinement does not claim concrete Haskell `Text`, key, revision, `Map`, `Set`, list, runtime-site, profile, subject, cost-shape, or canonical `SemanticForm` semantics. It does not prove target/profile-specific ABI/layout/aliasing/machine facts, external evidence truth, backend correctness, physical runtime behavior, or Rocq/GHC/toolchain correctness. Those remain explicit selected-evidence, finite-correspondence, or TCB boundaries.

A green staging matrix leaves `PHIL-SYS-REALIZE-001` at `Discharged / Certified` until a separate exact-kernel production-binding closeout lands.
