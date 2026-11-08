# FSEM-01 resource and local typing: exit-evidence matrix (v1)

> **Review finding: FSEM-01 remains OPEN.** This is a non-normative
> coverage/acceptance audit, not a new language rule, a proof of the general
> Haskell implementation, or an FSEM-01 completion claim.
>
> **Evidence cutoff:** 2026-11-08, Phil main at
> b057e30dde1854be2bbd2b696ec660cc98d9054a (merged PR #1670).
> Track [FSEM #1613](https://github.com/abiggerhammer/phil/issues/1613);
> source syntax authority is
> [Phase 1 Grammar v1](../../grammar/phase1-surface.ebnf), with its
> [status document](surface-grammar-v1.md). The [FSEM-00 inventory](formal-semantics-judgment-inventory-v0.md)
> names J01/J02/J03 and proposed resource-rule obligations.
>
> **Do not tick the FSEM-01 checkbox yet.** The table below separates
> checked bounded source paths from independently proved Rocq models,
> native Core/Systems obligations, and constructs still lacking FSEM-01
> source-to-resource correspondence. Other project tranches may have
> verified their own narrower contracts without satisfying this review gate.

## Method and evidence classifications

In this matrix **S** means a specific Grammar-v1 source witness parsed and
checked through its stated production checker fragment, with a paired accepted
and rejected execution where cited. **N** means native Core/Systems resource
behavior tested or separately production-bound, without necessarily being
reached from the same source witness. **R** means a kernel-checked Rocq theorem
about the *stated model*, often with explicit premises. **L** means source
lexical/structural identity scope only, not end-to-end resource typing.
**G** means a required FSEM-01 bridge or coverage decision is missing.
The combinations S+N+R or L+R must **not** be read as a universal refinement
proof. All classifications below are limited by the cited slice's exact
competence domain.

The proposed local resource context is R = (unrestricted Γ, affine A,
linear Δ, active shared loans). A checked judgment must name the source
expression or control form, exact type and structural mode, required
identity/provenance, context before/after, admissible return or error, and
any remaining assurance obligation. This is the provisional
[reader-guide vocabulary](typing-and-semantics-reader-guide-v1.md),
**not** a newly adopted normative inference rule.

The following is a **rule-family matrix**, not a pass percentage. The
scoped source-level positives/negatives below were tested on the cited
merged PR heads, not inferred merely from fixture filenames. A
non-competent bounded adapter returning Nothing is **not** proof that the
underlying Phase 1 program is source-invalid.

## A. Local/resource rule-family matrix

| Key | Resource/local typing rule or premise | Checked source, rejection and implementation evidence | Rocq / other existing model evidence | Audit verdict and exit gap |
| --- | --- | --- | --- | --- |
| R01 | Fresh lexical binder identity, source root, occurrence and scope; reject collision/out-of-scope use | **L+S (bounded).** [BinderScope](../../src/Phil/Surface/GrammarV1/BinderScope.hs), [PatternBinderScope](../../src/Phil/Surface/GrammarV1/PatternBinderScope.hs), [Phase1FSEM01BinderNameMain](../../test/Phase1FSEM01BinderNameMain.hs), [source product elimination](../../test/Phase1FSEM01SourceProductEliminationMain.hs). The product let allocates distinct successor keys; duplicate source names reject in the binder layer, consumed-owner reuse rejects by production StructuralUse. | [SurfaceBinderNameEncoding.v](../../proof/Phil/Surface/SurfaceBinderNameEncoding.v), [SurfaceDeclarationIdentityBridge.v](../../proof/Phil/Surface/SurfaceDeclarationIdentityBridge.v). | **Bounded bridge.** ASCII/string encoded-name and finite declaration catalogs are proved/tested; full Unicode Text/String and persisted declaration/revision identity simulation remain open. |
| R02 | Independently checked intrinsic linear mode and externally justified nominal affine mode; reject unjustified strengthening or weakening | **S.** [CheckedType](../../src/Phil/Surface/GrammarV1/CheckedType.hs), [SourceAffineResource](../../src/Phil/Surface/GrammarV1/SourceAffineResource.hs), [Phase1FSEM01SourceAffineMain](../../test/Phase1FSEM01SourceAffineMain.hs): Bytes[N] is intrinsically Linear; Permit mode affine requires an admitted external lifecycle justification. Source negatives isolate StrongerModeMissingJustification, unadmitted justification and DeclaredModeWeakensDerived. | [SurfaceSourceAffineBridge.v](../../proof/Phil/Surface/SurfaceSourceAffineBridge.v), [DataMode.v](../../proof/Phil/Core/DataMode.v). | **Bounded and premise-dependent.** Source spelling never establishes lifecycle authority. Independent validity of the caller-supplied attestation, root and interface revision is not proved by these tests. |
| R03 | Correct Γ/A/Δ/loans representation, lookup and framing of other owners | **S+N.** [Phase1FSEM01ObservationWireMain](../../test/Phase1FSEM01ObservationWireMain.hs), [Phase1FSEM01FiniteContextMain](../../test/Phase1FSEM01FiniteContextMain.hs) and [Surface Check Engine](../../src/Phil/Surface/Check/Engine.hs) inspect actual production map/set snapshots. Bounded decoder/wire evidence and 3/7/15-owner native tests detect forged or dropped foreign entries. | [SurfaceResourceContextWire.v](../../proof/Phil/Surface/SurfaceResourceContextWire.v) and [SurfaceFiniteContextFrame.v](../../proof/Phil/Surface/SurfaceFiniteContextFrame.v). | **Finite conformance + R**, not a proof of all Haskell Map/Set operations, arbitrary source execution or Text-to-String equivalence. |
| R04 | One-shot linear owner move and no silent unconsumed linear owner at terminal return | **S+N.** [SourceProductElimination](../../src/Phil/Surface/GrammarV1/SourceProductElimination.hs), [Phase1FSEM01SourceProductEliminationMain](../../test/Phase1FSEM01SourceProductEliminationMain.hs) and [Phase1FSEM01MixedAffineLinearMain](../../test/Phase1FSEM01MixedAffineLinearMain.hs). Negative sources reject reuse as StructuralUse and retained linear debt as LinearCompletion; real Core consumed-owner lookup is UnknownBinding. | [Context.v](../../proof/Phil/Core/Context.v), [DataProduct.v](../../proof/Phil/Core/DataProduct.v), [SurfaceSourceProductEliminationBridge.v](../../proof/Phil/Surface/SurfaceSourceProductEliminationBridge.v). | **Bounded single-path production checks.** Join/backedge/capture-wide linear use is not certified by these specimens. |
| R05 | Shared borrow start, view scope, loan closure and forbidden escape | **S+N+R (bounded).** [BorrowResourceSurface](../../src/Phil/Surface/GrammarV1/BorrowResourceSurface.hs), [Engine](../../src/Phil/Surface/Check/Engine.hs), [Phase1FSEM01BorrowResourceTraceMain](../../test/Phase1FSEM01BorrowResourceTraceMain.hs) and [Phase1FSEM01SourceAffineMain](../../test/Phase1FSEM01SourceAffineMain.hs) pair legal scoped use with minimally changed view escape, requiring precise BorrowEscape and no post-rejection successor. | [SurfaceBorrowStepErrorBridge.v](../../proof/Phil/Surface/SurfaceBorrowStepErrorBridge.v), [SurfaceSourceAffineBridge.v](../../proof/Phil/Surface/SurfaceSourceAffineBridge.v), [ResourceScope.v](../../proof/Phil/Core/ResourceScope.v). | **Bounded loan transition and modeled error prefix.** No source-wide nested borrowing/joins/captures/loops, general lifetime inference or runtime-to-Rocq checker-state simulation. |
| R06 | Affine owner optional disposition versus linear completion obligation; borrowed owner must not be consumed | **S+N.** [Phase1FSEM01SourceAffineMain](../../test/Phase1FSEM01SourceAffineMain.hs) accepts returning Unit while leaving a live affine Permit; [Phase1FSEM01MixedAffineLinearMain](../../test/Phase1FSEM01MixedAffineLinearMain.hs) rejects the identical terminal omission with outstanding linear Bytes. The native Context rejects consuming a borrowed owner as OwnerBorrowed. | [SurfaceMixedAffineLinearBridge.v](../../proof/Phil/Surface/SurfaceMixedAffineLinearBridge.v), [SurfaceSourceAffineBridge.v](../../proof/Phil/Surface/SurfaceSourceAffineBridge.v). | **Bounded.** Optional affine absence is a resource property; it does not prove any external release/disposal effect or independent lifecycle attestation. |
| R07 | Multiple real source-local affine and linear owners; spectator/loan preservation | **S+N.** [Phase1FSEM01TwoOwnerSourceMain](../../test/Phase1FSEM01TwoOwnerSourceMain.hs) checks two linear owners in one source function; [Phase1FSEM01MixedAffineLinearMain](../../test/Phase1FSEM01MixedAffineLinearMain.hs) checks one Affine Permit plus one Linear Bytes in one source function, with exact four-zone checkpoints and BorrowEscape/LinearCompletion failures. | [SurfaceTwoOwnerContext.v](../../proof/Phil/Surface/SurfaceTwoOwnerContext.v), [SurfaceFiniteContextFrame.v](../../proof/Phil/Surface/SurfaceFiniteContextFrame.v), [SurfaceMixedAffineLinearBridge.v](../../proof/Phil/Surface/SurfaceMixedAffineLinearBridge.v). | **Bounded multi-owner source runs.** General simultaneous source ownership, arbitrary spectator maps and exact failure refinement are still distinct obligations. |
| R08 | Flat product formation and checked ordered return: per-element type, mode and one-shot source | **S+N+R.** [CheckedType](../../src/Phil/Surface/GrammarV1/CheckedType.hs), [Phase1FSEM01FlatProductMain](../../test/Phase1FSEM01FlatProductMain.hs) cover flat Unit/Bool/U<n>/Bytes[N] products; [Phase1FSEM01NominalAffineProductMain](../../test/Phase1FSEM01NominalAffineProductMain.hs) covers admitted Permit + Bytes. Reversed members, wrong widths/modes and repeated owners reject with exact production TypeMismatch or StructuralUse. | [SurfaceFlatProductCorrespondence.v](../../proof/Phil/Surface/SurfaceFlatProductCorrespondence.v), [SurfaceNominalAffineProductBridge.v](../../proof/Phil/Surface/SurfaceNominalAffineProductBridge.v). | **Bounded flat palette.** Sound Rocq Ty equality is a premise; nested/recursive products and general source-to-Core product preservation are not established. |
| R09 | Product elimination: consume whole Linear product and restore positional Affine/Linear successors with fresh identities | **S+N+R.** [SourceProductElimination](../../src/Phil/Surface/GrammarV1/SourceProductElimination.hs) uses the real [Core.DataMode.eliminateProductBinding](../../src/Phil/Core/DataMode.hs) under an exact opt-in product contract. [Phase1FSEM01SourceProductEliminationMain](../../test/Phase1FSEM01SourceProductEliminationMain.hs) verifies accepted Bytes-only return and both-member return, exact states and negatives: linear debt, stale product reuse, 2-to-3 arity TypeMismatch, duplicate successor, return mismatch. | [DataProduct.v](../../proof/Phil/Core/DataProduct.v), [SurfaceSourceProductEliminationBridge.v](../../proof/Phil/Surface/SurfaceSourceProductEliminationBridge.v). | **Bounded single-source flat tuple let, merged #1670.** No general tuple destructuring/refinement proof, recursive aggregates, or arbitrary non-opted-in runtime product elimination. |
| R10 | Continuing branch join: exact linear ownership across predecessors; conditional affine asymmetry and no escaping loan | **N+R, source FSEM bridge G.** [Core.Context](../../src/Phil/Core/Context.hs) has joinContinuing; [Resource scope proof note](resource-scope-proof-v1.md) cites [Phase1BranchLocalLinearLeakMain](../../test/Phase1BranchLocalLinearLeakMain.hs), [Phase1AffineBranchAsymmetryMain](../../test/Phase1AffineBranchAsymmetryMain.hs), [Phase1ScopedLoanBoundaryMain](../../test/Phase1ScopedLoanBoundaryMain.hs) and [Phase1TerminalArmExclusionMain](../../test/Phase1TerminalArmExclusionMain.hs). [JoinStateScope](../../src/Phil/Surface/GrammarV1/JoinStateScope.hs) and [Phase1GrammarV1JoinLoopMain](../../test/Phase1GrammarV1JoinLoopMain.hs) cover lexical join slots, not the full source resource judgment. | [ContextJoin.v](../../proof/Phil/Core/ContextJoin.v), [ResourceJoin.v](../../proof/Phil/Core/ResourceJoin.v), [ResourceScope.v](../../proof/Phil/Core/ResourceScope.v), [SurfaceJoinStateScope.v](../../proof/Phil/Surface/SurfaceJoinStateScope.v). | **BLOCKER J-1.** Need one end-to-end parsed-source branch/join positive and minimally rejected negative with exact resource context and error, showing how source identities flow into native join and the normalized model. Do not mark source join proved from N+R. |
| R11 | Branch-local scope exit and terminal-arm exclusion from ordinary joins | **N+L+R, FSEM source G.** Source lexical join scopes and normalized RES-005–008 controls exist, including branch-local linear leak and terminal exclusion. These tests/model predicates are not yet a general source-derived FSEM-01 resource-state trace for a full branch. | [ResourceScope.v](../../proof/Phil/Core/ResourceScope.v), [SurfaceJoinStateScope.v](../../proof/Phil/Surface/SurfaceJoinStateScope.v). | **BLOCKER J-2.** Check complete-source continuing vs terminal predecessor separation, branch-local resource closure and exact rejection precedence. Keep affine absent as an explicit result, not hidden maybe-possession. |
| R12 | Loop initial/header/body/continue scopes, resource state slots, invariants and backedges | **L+N+R, FSEM source G.** [LoopStateScope](../../src/Phil/Surface/GrammarV1/LoopStateScope.hs) and [Phase1GrammarV1JoinLoopMain](../../test/Phase1GrammarV1JoinLoopMain.hs) cover lexical phases and visibility; [resource loop production binding](resource-loop-production-binding-v1.md) documents separate Systems/CFG resource checks. Neither alone establishes the combined FSEM source-step judgment. | [SurfaceLoopStateScope.v](../../proof/Phil/Surface/SurfaceLoopStateScope.v), [ResourceLoop.v](../../proof/Phil/Core/ResourceLoop.v). | **BLOCKER L-1.** Connect parsed loop entry, invariant, continue actuals and backedge resource context to real checker and model; isolate bad arity, stale owner, loan escape or ownership-loss source errors. |
| R13 | Closure/callable capture of restricted resources and scoped loans, including recursive capture cycles | **N, FSEM source G.** [Callable scope contract](callable-scope-v1.md), [Phase1CallableScopeMain](../../test/Phase1CallableScopeMain.hs) test exact loan-scope containment and reject restricted recursive-environment cycles, but are explicitly bounded callable/closure model tests, not a full source-derived capture resource correspondence. | [CallableLifecycle.v](../../proof/Phil/Core/CallableLifecycle.v) and other callable proof/implementation slices belong to their own obligation families. | **BLOCKER C-1 / OWNERSHIP DECISION.** Establish how admitted closure source captures and callables compose with FSEM-01 resource rules; coordinate with FSEM-04 callable/authority semantics rather than duplicating their logic. |
| R14 | General structural product and nested/mixed forms outside opt-in adapters | **G (coverage).** The existing tests deliberately reject *adapter competence* for nested products, unsupported return widths, three-way source product patterns, generic/recursive functions and wrong borrow owners; a Nothing result is not necessarily a source rejection. See [#1669](https://github.com/abiggerhammer/phil/pull/1669) and [#1670](https://github.com/abiggerhammer/phil/pull/1670) fixture comments. | [DataProduct.v](../../proof/Phil/Core/DataProduct.v) and [DataMode.v](../../proof/Phil/Core/DataMode.v) cover abstract structural-mode/product properties, not every concrete source production. | **BLOCKER COVERAGE-1.** Inventory which of these forms Phase 1 *actually admits* under the normative grammar + accepted semantic contract; either add source-level positive/negative evidence or obtain an explicit scope/semantic-authority ruling. Never equate bounded non-competence to normative invalidity. |
| R15 | Model↔production representation, accepted/rejected trace and error-class preservation | **S+R with finite conditional bridge; global G.** [Phase1FSEM01ObservationWireMain](../../test/Phase1FSEM01ObservationWireMain.hs) and source-derived OBS/CONTEXT wires replay exact bytes and reject malformed/tampered evidence. Current loan and product source tests assert exact Haskell error classes and no invented post-error state for their fragments. | [SurfaceBoundedSourceSimulation.v](../../proof/Phil/Surface/SurfaceBoundedSourceSimulation.v), [SurfaceObservationProducerFidelity.v](../../proof/Phil/Surface/SurfaceObservationProducerFidelity.v), [SurfaceBorrowStepErrorBridge.v](../../proof/Phil/Surface/SurfaceBorrowStepErrorBridge.v). | **BLOCKER CORR-1 (scoped), FSEM-06 handoff (general).** Identify which FSEM-01 resource/error transitions lack source→native representation and error correspondence; model producer-fidelity is NOT a proof of runtime Map/Set/Text/UTF-8 or every Haskell error. General compiler refinement stays a separately declared FSEM-06 task. |

## B. Concrete witness and verification anchors

The recent change sequence was independently merged, with the stated
finite source/production and Rocq/model bounds. These are **merge commits
on main**, not unchecked feature branches or a retroactive claim that
every FSEM-01 rule is normative.

| Merged PR | Exact squash on main | Why included in this audit |
| --- | --- | --- |
| [#1655](https://github.com/abiggerhammer/phil/pull/1655) | 499dfa47b288cb5f268a51c4373942687cc2b057 | One parsed two-Linear-owner function, paired BorrowEscape; typed product elaboration still open at that historical point |
| [#1659](https://github.com/abiggerhammer/phil/pull/1659) | fbd4c0d86898d6077b3c4be5d324052755d693b6 | Source flat-product mixed primitive checking and conditional exact ordered-contract theorem |
| [#1664](https://github.com/abiggerhammer/phil/pull/1664) | 5e2058e427df6881394b691ee63fcfeccca26777 | Finite four-zone model and 3/7/15-owner native frame checks |
| [#1666](https://github.com/abiggerhammer/phil/pull/1666) | 635deccd0ba263131e9a9325d20445dee97cf2cf | Source-level nominal affine admission and checked borrow/consume/discard |
| [#1667](https://github.com/abiggerhammer/phil/pull/1667) | 7386b2be6f723aa132c0a2d368afbff1fe1d07fc | Single-source affine Permit + linear Bytes, precise linear completion/escape |
| [#1669](https://github.com/abiggerhammer/phil/pull/1669) | 313327ee71a0cd68fd57e00f5be3029f735eaa56 | Checked source nominal/linear product return, order/mode and duplicate negatives |
| [#1670](https://github.com/abiggerhammer/phil/pull/1670) | b057e30dde1854be2bbd2b696ec660cc98d9054a | Real Core product elimination via source tuple let; 95/95 draft exact-head PR workflows, fresh ready-for-review guard green (96/96), and a successful two-job branch-push preflight |

For details before these PRs, see the source/identity/wire/transition documents
listed under [Phase 1 FSEM-01](README.md), notably #1621/#1622,
#1626/#1627, #1631/#1632, #1635–#1644 and #1653/#1658.
Those earlier source-checking and observation slices are **not superseded
as evidence**, but historical slice notes must not be treated as today’s
overall completion status.

For the newest actual-source paired witnesses, compare:
[source affine consume](../../test/fixtures/fsem01-source-affine-v1/consume.phil)
with [borrow escape](../../test/fixtures/fsem01-source-affine-v1/escape.phil);
[mixed ownership accepted](../../test/fixtures/fsem01-mixed-affine-linear-v1/accepted.phil)
with [unpaid linear debt](../../test/fixtures/fsem01-mixed-affine-linear-v1/leak-linear.phil);
[nominal product accepted](../../test/fixtures/fsem01-nominal-affine-product-v1/accepted.phil)
with [reversed return](../../test/fixtures/fsem01-nominal-affine-product-v1/reversed.phil);
and [product elimination accepted](../../test/fixtures/fsem01-source-product-elimination-v1/accepted.phil)
with [wrong-arity restoration](../../test/fixtures/fsem01-source-product-elimination-v1/wrong-arity.phil).
The selected test files above assert expected exact classes, not just any
parse rejection. FSEM-01 has no single independent executable full-source
Rocq interpreter; that whole-language requirement belongs to FSEM-05.

## C. Six acceptance criteria from issue #1613

| Issue acceptance requirement | Audit status at cutoff | Missing evidence / action before closing FSEM-01 |
| --- | --- | --- |
| 1. Scoped rule/judgment, all premises, before/after state, outcomes and exact failure | **Partially met** for bounded linear/borrow/affine/product source paths; models for join/loop/capture exist elsewhere | Record and review the full intended *admitted FSEM-01 resource/local typing fragment*, including join/backedge/closure premises, exact terminal versus continuing outcomes and obligation residue. Explicitly classify every out-of-adapter form. |
| 2. At least one accepted and one minimally rejected executable source witness, exact cause | **Met only per cited bounded fragment**; e.g. BorrowEscape, LinearCompletion, product type/order/arity and stale use | Add accepted/rejected **complete Grammar-v1 source** cases for branch/join, scope exit and loops, and agreed capture forms where admitted, that reach the real checker and verify the decisive class/error. |
| 3. Exact theorem/test/source refs and checked head SHA per implementation bridge | **Met for named merged slices**, including #1670; no theorem/merge evidence is synthesized for gaps | Provide an exact, reviewable bridge/evidence chain for every newly claimed rule and retain current PR-head, workflow and merge SHA records. |
| 4. Scope: syntax, typing, model, elaboration or realized runtime; TCB/assumptions | **Explicit for the checked slices**, but no global Haskell↔Rocq proof | Preserve external lifecycle attestation, nominal declaration/revision metadata, abstract Ty equality and native Text/Map/Set state relation as independent premises; assign general cross-language refinement to FSEM-06 unless a narrower FSEM-01 theorem is necessary. |
| 5. Prevent semantic interface edits by conflicting lanes | **Currently met by process**, not by theorem | Use the **atomic family claim** documented in [formal-semantics coordination](../formal-semantics-coordination.md). The FSEM hamster has separately reserved FSEM-02; future FSEM-01 PRs must newly claim fsem-01. |
| 6. No merge/promotion without required evidence or generalized soundness claims | **Met for bounded merged PRs; FSEM-01 exit remains blocked** | Audit the outstanding rule rows with PL/formal-methods readers; never mark FSEM-01 complete or normative on the strength of finite tests, a single extracted kernel or an implicit weakening of admitted syntax. |

## D. Proposed short exit sequence and authority decisions

These are *candidate tasks*, **not** new approved requirement IDs or
competing issue milestones. Reconcile them against the current
[Logic Ledger and Conformance Matrix](README.md) before marking
any result discharged.

1. **Join and branch source bridge — J-1/J-2.** Start with one genuinely
   parsed program with two compatible continuing predecessors and one
   minimally changed program leaving a linear owner stranded, or with
   an unmatched affine post-state. Test the exact native join and class,
   then connect it to ContextJoin/ResourceJoin/ResourceScope. Distinguish
   terminal arms, which do not contribute continuing predecessor state.
2. **Loop ownership source bridge — L-1.** Use the existing loop-state lexical
   proof as one *premise*; require real parsed header/continue/backedge
   witnesses, explicit invariant/resource slots and at least one isolated
   negative. Do not assume the Systems resource-loop kernel proves source
   loop elaboration.
3. **Capture integration and scope decision — C-1.** Decide which closure
   capture/loan forms belong to FSEM-01 resource judgment and which
   obligations are FSEM-04 callable/effect/authority. Reuse existing
   CALL-010/014 tests and contracts; source-bridge only the agreed
   admitted subset, not a fictitious lifetime calculus.
4. **Aggregate competence inventory — COVERAGE-1.** Cross-tab normative
   Grammar-v1 forms and current admission/semantic contracts against
   the bounded adapters. Mark each as admitted + checked, admitted +
   unbridged, or explicitly unsupported by *accepted* authority. Include
   nested/recursive products and ordinary tuple-let variants; keep
   noncompetence distinct from source invalidity.
5. **Correspondence and failure review — CORR-1.** Extend actual-source
   acceptance/error-prefix observations to the newly admitted branch and
   loop paths. State any missing proof premise explicitly. General
   Haskell-to-Rocq implementation refinement, all constructs and
   independent extracted execution are tracked separately under
   FSEM-06/FSEM-05, not silently promised by a local FSEM-01 matrix.
6. **Exit decision.** Once the above are evidenced or given explicit,
   reviewed semantic-authority scope dispositions, issue #1613's six
   criteria should be checked row by row. Only then update the
   FSEM-01 checkbox and synchronize the Logic Ledger and Conformance Matrix.
   FSEM-07 normative graduation is a distinct later decision.

## E. Explicit handoff boundaries

- **FSEM-02 owns endpoint action/session progression.** Its agent has
  its own fsem-02 claim and must not repair or claim FSEM-01 concurrently.
- **FSEM-04 owns the semantics of obligations, effects and external authority.**
  The source nominal Affine attestation and any satisfies-C obligation
  stay named external premises; resource-mode admission is not assurance
  discharge.
- **FSEM-05 owns full admitted Phase 1 source operational semantics,
  fuel-bounded replay and an independent Rocq-extracted executable.**
  A finite borrow or product model is not that evaluator.
- **FSEM-06 owns each general Source→Core→Systems→target
  elaboration/behavior/error correspondence.** FSEM-01 still needs
  local source↔resource bridges for its actual asserted rules, but does
  not silently assume a universal compiler correctness theorem.
- **FSEM-07 owns normative graduation and formal-methods review.**
  This audit is non-normative until explicitly adopted through the
  repository's accepted semantic-authority process.

**Current decision: continue FSEM-01 with J-1/J-2, not another product-only
slice, unless external review changes the priority or declares a narrower
scope.** The checklist remains unchecked.
