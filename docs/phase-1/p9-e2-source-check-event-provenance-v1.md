# P9-E2: original checker events in actual P2/P6 source production

**Status:** candidate source-backed P2/P6 binding; does **not** grant P9-qualified final provenance or close SYS-012/SYS-013. Owner: native `p9-evidence`, E2 PR 2/3 under [#1771](https://github.com/abiggerhammer/phil/issues/1771#issuecomment-6878199353).

## Competent producer and boundaries

The existing `checkPortableSourceBundle` parses each persisted `SourceUnitId`, resolves `DeclarationSiteId` to `DeclarationKey`, selects the actual source-checking environment, and now executes `checkSurfaceComponentWithEvidence` at the **same successful checking call**. The returned `CheckedSourceUnit` retains those original static checker events with their spans, routes, ordinals and typed uses. The public `CheckedSourceEvidenceOccurrence` adds unit and declaration identity; it is **observational data, not an authoritative token**. Callers can construct its record, like `CheckedSourceUnit`.

The only P9 source-owned path here is the **constructor-private** `VerifiedSourceSystemsProduction`, which reruns raw ordinary-source checking, verifies its checked architecture and corresponding whole `CoreSystemsProgram`, executes the actual generic Systems lowering, and stores `VerifiedSourceCheckEventGraph` from the very same just-rechecked bundle, exact K/I and admitted whole Core semantic identity. The graph's constructor remains private. Public list or record constructors cannot create a `VerifiedSourceCheckEventGraph`, and `prepareSourceSystemsAdmission` for arbitrary public checked records cannot mint one either.

`verifySourceCoreCorrespondence` now also retains the exact per-function observed source checker events alongside the already verified matching source/Core **function set**. This is a binding of source-event owner to that admitted Core function, **not** an unsupported claim that every static proof-use event maps to one concrete `CoreSystemsOperation`. The complete semantic operation correspondence/erasure domain is still unproved; limited six-counter `SourceCoreInventory` does not establish SYS-012. `Core.Value.appendEvidenceList` dedup inside a single checked `ValueResult` cannot be reversed by this graph.

P6 already carries the private `VerifiedSourceSystemsProduction` and verifies the **complete source StageBundle** in BOTH concrete and next-stage arms. Its read-only `verifiedStageClosureSourceCheckEventGraph` now projects the exact same private graph from its source producer. No caller-supplied StageClosure template creates, modifies, or replaces this graph. This does **not** prove a static branch actually executed at runtime.

## Discriminating real native checks

The P9-E2 native suite executes actual `produceVerifiedSourceSystems` with ordinary checked text, tests exactly qualified source unit/declaration site/key and private K/I+Core identity, and shows a whitespace-only event relocation has a **different site and event graph despite identical semantic K/I and whole admitted Core**. It rejects an unproved source proposition, a substituted Core function name, and avoids inventing final use for zero-use source. The existing Upload/Steve P2/P6/P7 end-to-end harness now checks the private graph on genuine repository Upload and Steve sources, including real Upload server event observations and exact P6 source-graph preservation. None of these tests fabricates a ValueResult or a P9-qualified P7 result.

## Still required

**E3**: a strong P7 consuming operation must require an authentic original E2 event and a specific *actual selected final assurance use* matched to the exact immutable manifest/whole StageClosure/certified release/LLVM/trust. P7's current accepting path does **not** do this, and `OriginalCheckEventAcceptance(..)` is still caller-constructible; neither record equality nor private E2 graph existence proves final use. Static alternatives are not executed branches.

**SYS-012**: authoritative complete actual later-consumer inventory, including fact/subject/representation/order/successor, not a template map. **SYS-013**: stage key/scope tied to exact selected immutable `AssumptionId`, digest, semantic subject/boundary, permission, validity, and discharge. **P8**: total native↔Rocq whole-object representation remains open. **P10**: HARD BLOCKED, `FinalArtifactCertified` unproved; no Phase 1 freeze, signing, notarization, or independent audit assertion. The existing language, TCB and 244 normative rows stay unchanged.
