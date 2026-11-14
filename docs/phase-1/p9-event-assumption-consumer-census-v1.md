# P9-A: native final-use / erasure / imported-assumption predecessor census

**Control:** [#1771](https://github.com/abiggerhammer/phil/issues/1771),
[#1584](https://github.com/abiggerhammer/phil/issues/1584) and
[finite lane contract](p8-p9-autonomous-lane-coordination-2026-11-14.md).
**Fixed inspected main:** `4fd2c981a599008bec5d202362f0210a8043e655` (after bootstrap #1773).
**Deliverable:** first of at most two authorized P9 PRs.
**Claim:** counterexample-preserving *bounded proof discrimination and native caller
inventory*, **not** discharge of the P9 accepted-path producer obligations.
This document intentionally does not promote record equality, a local canonical
hash, a supplied Rocq `Prop`, or a source fixture to external event authority.

## Source-derived native path and concrete check sites

| Original producer / checked datum | Native operation (on inspected main) | Consumer and what it actually checks | Incomplete predecessor |
|---|---|---|---|
| Ordinary checker/source and source-derived selected architecture | `produceVerifiedSourceSystems` → `produceVerifiedStageClosure` → `produceVerifiedFinalOrigin` (P2/P6/P7); [verified origin notes](audit-verified-final-origin-production-v1.md) | `acceptVerifiedFinalOrigin` compares checked source/manifest, VER-010 source, complete INT-005 release, replay. Constructor-private `AcceptedVerifiedFinalOrigin` distinguishes this from structural-only acceptance | Origin lineage **alone** does not prove every checker-to-assurance evidence use, SYS-012 semantic later-consumer or SYS-013 immutable stage-assumption dependency came from a competent source-domain producer |
| Verification bundle and selected immutable assurance context | `Phil.Verification.ManifestClosure.closeVerificationBundle`, source [119–153](../../src/Phil/Verification/ManifestClosure.hs); `ManifestClosureSelection` lists evidence, assumptions, exports and assurance uses | Exact bundle policy/architecture/context/revisions and accepted evidence references; selected assumption/use membership; dependency coverage and `verifyManifest`. The verifier checks manifest selection and context; it does not construct the source-to-Systems consumer universe | An exact selected `Set AssumptionId` is not itself an accepted `StageAssumptionKey→Assumption` mapping with authority/current-validity and discharge for *each actual required stage key* |
| Core checker handoff | `closeVerificationBundleWithHandoff`, [315–361](../../src/Phil/Verification/ManifestClosure.hs), plus `Handoff.bindHandoffCertificateEvidence` and direct evidence | Exact selected certificate/direct evidence revision domains, graph support, finalized ledger entries, and then `closeVerificationBundle`. Distinguishes certificate, direct named evidence and definitionally discharged support | Handoff equality and checked ledger identity do not by themselves establish the final consumer retained and used the *same original checking event*. Original check-event identity plus the real final-use occurrence must both be mapped into the final accepting event |
| Actual selected use, context and obligation closure | `Phil.Assurance.Verify.verifyManifest` [117–140,230–268,329–358](../../src/Phil/Assurance/Verify.hs) | Verifies evidence digest/result/validity, immutable `Assumption` digest/permitted scope, selected uses; `verifyUseEvidence` requires original selected evidence revision plus `evidenceUsable` | Verification that a selected use is internally consistent does not prove *all actual Core/source/Systems final uses* are present or that their original checking event has been transported |
| Erasure consumer supplied stage map | `Phil.Systems.EvidenceErasure.makeEvidenceErasureStageBundle` [189–202](../../src/Phil/Systems/EvidenceErasure.hs) | Derives revision by canonicalizing `evidenceErasureStageLaterConsumers` supplied to the constructor. `verifyEvidenceErasureStageBundle` [204–220] checks justifications, uniqueness, and **each entry** in `Map.toAscList` | No mandatory producer observed at this gate that derives the full *actual later semantic-consumer domain* from the selected source/semantic-operation inventory; a canonical digest protects the supplied map, not its external completeness |
| Later erasure semantic consumer | `checkConsumer` [330–363], `nativeCheckConsumerClosure` [379–412](../../src/Phil/Systems/EvidenceErasure.hs) | Map key, known fact/subject/reference, justification, not equal to claimed last use, representation still required vs exact successor invariant | The list is traversed only after its entries have been supplied. A second real post-erasure consumer omitted from the map is not visited. `NoLaterConsumerRevision` alone is not a trusted actual-consumer completeness proof |
| Stage-required assumptions and scope | `Phil.Systems.AssumptionDependency.deriveRequiredAssumptionConsumers` [116–147](../../src/Phil/Systems/AssumptionDependency.hs) | Derives references from stage fact dispositions, mechanisms and erasures. `verifyAssumptionDependencyStageBundle` [192–248] checks registry domain, forward map, reverse map, consistency; `checkForward` [268–304] matches local scope strings | `AssumptionBinding` [65–69] contains only stage-local key + validity-scope revision, not immutable assurance `AssumptionId`, digest, semantic subject/boundary, exact manifest selection, permission, current validity or discharge. Those are still an independently checked imported predecessor |
| Immutable assurance assumptions | `Phil.Assurance.Verify.verifyAssumption` [258–268](../../src/Phil/Assurance/Verify.hs), context/selected `manifestAssumptionNodes` | Identity key, recomputed digest, permitted `AssumptionId` and matching validity context; evidence entries check selected dependencies | No demonstrated mandatory exact bridge from every *stage-required* `StageAssumptionKey` and its scope to the *same selected* immutable assurance record, with original acceptance event and valid discharge scope |
| Whole release claim | `produceVerifiedFinalOrigin` / `acceptVerifiedFinalOrigin` then downstream **final-provenance** consumers | P2/P6/P7 seals source/checked instance/whole stage/whole release selection; structural-only callers may not assert stronger provenance | P9 needs a non-bypassable transport of actual complete evidence uses/semantic-consumer domain/assumption authority through *that same accepted* final production/consumption event, not an independent plausible ledger |

**Classification:** Handoff certificate/direct support and ledger assurance-use checks are *real native checks*; the abstract event correspondence and SYS-012/SYS-013 authoritative model inputs are **not** proven produced at those sites. In particular, this census does not assert that a completeness producer is absent everywhere in the repository; it identifies the missing *mandatory accepting-path producer binding* observed at the named public constructor/consumer edges.

## Permanent discriminating proof witnesses

The new [`P9EvidenceAuthorityDiscrimination.v`](../../proof/Phil/Assurance/P9EvidenceAuthorityDiscrimination.v)
is compiled with every existing proof dependency in a dedicated exact-head
[Rocq 9.2.0 workflow](../../.github/workflows/phase1-p9-evidence-authority-discrimination.yml).
It imports the preexisting positive/negative models but adds independent
parameterized single-field assumption mutations (digest, subject, owner/boundary,
manifest selection, verification-context permission, expired current validity)
and a forged/unmapped required key. The field mismatches all *preserve* the local
stage correspondence and must fail `ImportedAssumptionAuthorityPreserved`.

| Boundary | Positive bounded model | Adversarial model which must **not** be credited | What native gate is still needed |
|---|---|---|---|
| SYS-012 | Exact two-consumer domain, source fact, subject, representation, ordering and successor all match | Real consumers 1 and 2, supplied only 1; supplied-local closure passes while authoritative completeness fails | Exact same-build semantic use/operation domain producer consumed by SYS-012, not just traversal/digest |
| Final evidence | Checked closed and subject-bearing uses with same original checking event and **actual final consumer use** | Changed original event despite valid subject, OR metadata for correct original event but **no actual final use** | A check-event identity tied to real checker witness and actual consumed-use event, including checked closed-use classification without invented subject endpoints |
| SYS-013 | Exact imported immutable identity, content digest, semantic subject/boundary, validity scope, selected/permitted/current | Six independent one-field mutations, plus unknown stage required key and old different-scope witness, while local dependency graph remains coherent | Exact required stage key/scope → selected, accepted immutable `Assumption`, permission/validity/discharge at the real final event |
| P7→P10 | Existing sealed whole source and StageClosure/whole release selection | Independently consistent but untransported model tuple/credential | New native accepting checked producer relation *and* P8 full-domain representation before P10 can derive adapter/certification |

The model uses `nat` keys because its preexisting bounded proof models do.
They are **diagnostics**, not native Haskell→Rocq accepted-data encodings and
must not be lifted to grant `FinalArtifactCertified`. The full Rocq
`Print Assumptions` output is recorded by hosted CI; no `Admitted`, axiom,
trusted token, or extra native TCB is introduced.

## Next owned slice / P9-B preconditions

A second PR is eligible only after this PR has passed exact-head proof CI and
protected merge, and only if a coherent smallest native producer→consumer binding
exists without adding language/TCB authority. First obtain explicit shared
accepting-path ownership and re-read current `main`, active P8/FSEM/Rocq claims.

1. Establish the **authoritative relevant actual semantic consumer set** and
   precise provenance of each erasure use from the same selected source/semantic
   operation. Add actual second-consumer omission rejections at the real
   production gate, including successor/ordering/last-use preservation.
2. Bind each required stage-assumption key and validity revision to the
   **same** immutable accepted selected `Assumption` and external discharge
   context. Prove current permitted digest/subject/boundary/scope and reject
   forged or stale records at a real accepting consumer.
3. Bind original checker event and each real final evidence use to the exact
   selected whole P7 event, with both Upload/Steve positive source replay and
   changed-event/no-use negatives. Preserve subject-bearing/checked-closed split.
4. If no already competent producer exists under admitted Phase 1 semantics,
   record the smallest accepted counterexample and request a maintainer
   semantics/TCB decision. **Do not fabricate one.**

**Disposition at this PR:** P9 OPEN / not discharged, P8 OPEN,
P10 BLOCKED. P11 independent byte/signature/notary/provenance remains NOT YET,
`FinalArtifactCertified` UNPROVED, Phase 1 freeze NOT YET. No original
244 normative conformance rows touched.
