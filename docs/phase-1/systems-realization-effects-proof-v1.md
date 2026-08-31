# Phase 1 Systems realization-effects proof v1

`PHIL-SYS-REALIZE-001` certifies the target-strengthening, target-inserted staging, and next-stage export obligations already implemented by SYS-014, SYS-017, and SYS-019.

## Certified boundary

The Rocq model composes the already Certified `PHIL-SYS-STAGE-CLOSURE-001` final StageContract identity closure with three normalized relations.

### Target strengthening

A target fact stronger than available source assurance cannot be silently attributed to the source. If no exact source assurance is available, the strengthening must name an explicit derived realization obligation. That obligation has a nonempty revision, an exact introducer relation, at least one semantic subject, a proposition/refinement statement, and an acceptance rule.

The model also proves that a claimed source-assurance citation cannot close the strengthening when that citation is not known at the exact source boundary.

### Target-inserted staging

Every live staging requirement has exactly one staging event. A valid event exposes all semantic consequences that the implementation checks separately: realization effect, authority account, explicit failure account (including explicit infallibility as distinct from omission), semantic-subject transfer, target-required cost identity, bytes-copied accounting, and frequency accounting.

This proves the normalized obligation that target-only copying/staging cannot disappear into backend housekeeping.

### Next-stage competence-boundary export

Every live next-stage basis has exactly one exported requirement. Every requirement has exact Systems provenance, a nonempty required fact/contract identity, a non-folklore marker, an acceptance rule, and a validity scope. A folklore-only requirement cannot close.

The concrete implementation additionally derives this domain mechanically from target preconditions and reusable runtime primitive profiles, so omission and invention remain executable correspondence checks rather than assumptions of the Rocq model.

## Correspondence corpus

The dedicated certification workflow reruns the existing implementation corpus unchanged:

- `test/Phase1TargetStrengtheningMain.hs` — 14 SYS-014 cases;
- `test/Phase1StagingEffectMain.hs` — 29 SYS-017 cases;
- `test/Phase1NextStageRequirementMain.hs` — 25 SYS-019 cases.

Total: **68 unchanged cases**.

No production Haskell behavior changes are part of this proof slice.

## Residual correspondence boundary

Concrete Haskell `Text`/`Map`/`Set` enumeration, canonical `SemanticForm` rendering, target/profile-specific ABI/layout/runtime facts, concrete authority/effect/failure/cost schemas, and the Haskell-to-normalized-model correspondence remain explicit implementation/assurance boundaries. The proof does not treat ambient platform convention, compiler defaults, or symbol coincidence as evidence.

Baseline at branch cut: `6e11c80440f05b5a5708ff8694e778b81435f51c` (#440 merge).
