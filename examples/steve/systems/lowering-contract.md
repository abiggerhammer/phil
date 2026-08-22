# Steve 0 systems-IR and lowering contract

Status: checker/lowering pressure-test sketch; not yet an executable `SystemsArtifact`

This note maps the current Steve 0 semantic witness and provisional ADR-010 assurance graph onto the systems IR introduced by PR #26. Its purpose is to identify the smallest faithful certified-release representation for Steve and to expose places where the current upload-shaped systems vocabulary needs to generalize.

The target remains deliberately boring: a local append-only content-addressed byte store with `put` and `get`. This note does not introduce Steve networking, garbage collection, signatures, replication, mutable references, or a new Phil semantic decision.

## Source and target boundary

The semantic source is the pair of components in `../steve.phil` together with the twelve Steve obligation revisions and their evidence/assumption graph in `test/SteveAssuranceMain.hs`.

The initial systems target should use `CertifiedRelease` and two functions:

- `StevePut`
- `SteveGet`

Provider calls remain runtime operations. Compile-time proof/evidence wrappers may disappear only through explicit ADR-010 `ErasureUse` records. Runtime digest computation, digest validation, and exact byte comparison remain visible and cost-linked.

## Execution-topology scope

Steve 0 deliberately selects the ordinary host/CPU execution topology for its first Systems artifact. The control-flow sketches below therefore use sequential CFG blocks, host-visible provider/runtime operations, and ordinary owned/borrowed byte values. Those are valid target choices for Steve 0, not generic definitions imposed on Phil Systems IR.

ADR-012 requires the generic Systems representation to remain valid when another selected execution topology has distinct address spaces/storage classes, explicit placement and transfer edges, synchronization, parallel decomposition, different runtime representations, or non-passive observation. In such a target, the same architectural Steve computation could require explicit transfer, staging, synchronization, or representation-refinement obligations and costs before a digest/storage mechanism is realized.

Accordingly, the four Steve runtime sites described below are **host-target physical Systems sites**. For the current host/LLVM ABI, a retained runtime site may specialize to one runtime call. `RuntimeSiteRef` itself must not be defined as a call instruction, linker symbol, host pointer, or assumption of one coherent address space.

## Value representation

The current `Phil.Systems` vocabulary is sufficient for a first structural sketch:

### `StevePut`

- `put.digest_provider` — `RuntimeRecord "DigestProvider[SHA256]"`
- `put.blob_provider` — `RuntimeRecord "BlobProvider"`
- `put.candidate` — `OwnedBuffer "OwnedBytes[n]"`, owning one storage identity
- `put.candidate_view` — `BorrowedSlice put.candidate`
- `put.content_id` — `RuntimeScalar "ContentId[SHA256]"`
- `put.install_result` — `RuntimeScalar "InstallIfAbsentResult"`
- `put.read_result` — `RuntimeScalar "BlobReadResult"`
- `put.existing` — `OwnedBuffer "OwnedBytes[existing]"`, distinct storage identity
- `put.existing_view` — `BorrowedSlice put.existing`
- `put.byte_relation` — `RuntimeScalar "BytewiseRelation"`
- result/failure discriminants — ordinary runtime scalars/records as needed by the eventual ABI

### `SteveGet`

- `get.digest_provider` — `RuntimeRecord "DigestProvider[SHA256]"`
- `get.blob_provider` — `RuntimeRecord "BlobProvider"`
- `get.content_id` — `RuntimeScalar "ContentId[SHA256]"`
- `get.read_result` — `RuntimeScalar "BlobReadResult"`
- `get.bytes` — `OwnedBuffer "OwnedBytes[stored]"`, owning one storage identity
- `get.bytes_view` — `BorrowedSlice get.bytes`
- result/failure discriminants — ordinary runtime scalars/records

`RuntimeRecord` is only a representation placeholder for provider handles. It does **not** by itself encode provider authority. The source/static architecture remains responsible for saying that Steve receives read/install-if-absent authority and no overwrite/delete authority.

Stable byte-object identities should be carried by systems metadata such as `systemsStorageIdentity`, not by the ephemeral `BorrowedSlice` value. This preserves the Steve rule that persistent evidence names the owner/snapshot identity rather than a loan token. Under ADR-012, that stable identity is semantic object/storage identity rather than a machine address, execution-domain placement, storage class, or one target layout. If a selected target migrates or converts the physical representation while preserving the same assurance subject, the lowering must carry an explicit checked correspondence and account for transfer/conversion obligations and costs.

## `StevePut` control-flow sketch

A faithful CFG should make the compare-before-rehash optimization visible:

1. `put.entry`
   - borrow `put.candidate_view` from `put.candidate`;
   - compute SHA-256 and `put.content_id` at the retained `put.digest.compute` runtime site;
   - call `BlobProvider.installIfAbsent` over a scoped candidate view;
   - branch on installed / already-exists / storage-failure, represented by ordinary runtime calls plus nested binary CFG branches if necessary.

2. `put.installed`
   - release the candidate owner;
   - return `PutOk`.

3. `put.already_exists`
   - call `BlobProvider.read(content_id)`;
   - branch to not-found/inconsistent-storage, storage-failure, or found.

4. `put.existing_found`
   - own `put.existing`;
   - borrow candidate and existing views;
   - execute exact `bytes_compare` at `put.byte_compare`;
   - branch on exact equality / exact inequality.

5. `put.equal`
   - release both owners;
   - return `PutOk` **without another SHA-256 computation**.

6. `put.different`
   - borrow `put.existing_view`;
   - execute `digest_check(content_id, existing)` at `put.existing.digest_check`;
   - rejected digest -> release both owners -> `PutExistingObjectCorrupt`;
   - accepted digest -> release both owners -> `PutDigestCollision`.

7. every storage-failure path
   - releases every owner still held by Steve exactly once;
   - cannot flow to `PutOk`.

The systems CFG does not need a new multiway terminator merely for Steve. Provider result variants can be lowered to runtime discriminants followed by ordinary binary `TermBranch` nodes.

The sequential CFG above is the selected host/CPU execution topology. It must not be used as evidence that every future Systems target has one scalar sequential thread of control; ADR-012 requires any alternate decomposition/synchronization topology to be represented and justified explicitly.

## `SteveGet` control-flow sketch

1. `get.entry`
   - call `BlobProvider.read(content_id)`;
   - absent -> `GetNotFound`;
   - provider failure -> `GetStorageFailure`;
   - found -> own `get.bytes`.

2. `get.found`
   - borrow `get.bytes_view`;
   - execute `digest_check(content_id, bytes)` at `get.digest_check`;
   - rejected -> release owner -> `GetIntegrityFailure`;
   - accepted -> transfer the same owner into `GetOk`.

No successful `GetOk` path exists that bypasses the digest-check success edge.

## Retained runtime sites

The current Steve assurance graph contains five `RetainedRuntimeUse` records over three cost identities. Four distinct host-target physical runtime mechanisms are expected in the systems CFG:

| Physical site | Kind | Obligation/evidence | Cost ref | Dynamic condition |
| --- | --- | --- | --- | --- |
| `put.digest.compute` | `DigestBoundary` | `STEVE-PUT-DIGEST` / `evidence.steve.put_digest.runtime` | `steve.runtime.digest_compute` | every `put` before publication |
| `put.byte_compare` | `SourceSemanticRuntime "bytes_compare"` | `STEVE-BYTE-EQUALITY-EVIDENCE` / `evidence.steve.byte_equality.runtime` | `steve.runtime.bytes_compare` | only `AlreadyExists` + successful read |
| `put.existing.digest_check` | `DigestBoundary` | `STEVE-COLLISION-FAILS` / `evidence.steve.collision.runtime` | `steve.runtime.digest_check` | only after exact inequality |
| `get.digest_check` | `DigestBoundary` | `STEVE-GET-DIGEST` / `evidence.steve.get_digest.runtime` | `steve.runtime.digest_check` | only after successful read |

`STEVE-CORRUPTION-FAILS` is also backed by `evidence.steve.corruption.runtime` and `use.steve.corruption_digest`, but corruption rejection is not a fifth physical digest computation. It is a logical property of the existing digest-check sites above. This exposes a systems-IR generalization described below; we should not invent a duplicate runtime check just to satisfy a one-evidence-per-site representation.

The names in the first column are **physical Systems-site identities in Steve 0's selected host execution topology**, not runtime primitive, linker-symbol, instruction-address, or pointer identities. In particular, `put.existing.digest_check` and `get.digest_check` may legitimately use the same digest-validation primitive/signature while remaining two distinct physical sites because they occur at different program locations and under different dynamic conditions. Conversely, each one remains a single assurance/cost-bearing site even when its exact assurance claim set contains more than one logical obligation. Runtime primitive/execution-profile identity, physical site identity, and assurance claim identity must therefore remain separately represented and separately checked.

Following PR #43, any host runtime symbol for such a primitive must be derived from the physical operation family and ABI-relevant signature/profile, not from `RevisionId`, `EvidenceEntryId`, `AssuranceUseId`, or claim-set cardinality/order. Adding a corruption-rejection claim to an existing digest site must not rename the primitive, create an alias per claim, or induce a second digest execution/cost.

For the current host/LLVM target, PR #44 demonstrates the specialization in code: physical-operation-oriented runtime symbols and independent translation validation preserve the selected runtime mechanism without using assurance evidence as the linker identity. That one-site/one-call relation is a property of this host target. A heterogeneous backend may use another explicit target realization relation, including a composite realization below Systems, provided the whole realization remains bound to the exact site/claim/cost relation and any transfer/synchronization/conversion costs remain visible.

## Stage facts

The initial `systemsExpectedSourceFacts` should correspond one-for-one with the twelve Steve obligations rather than inventing systems-only pseudo-obligations:

| Source fact | Intended systems disposition |
| --- | --- |
| `steve.put_digest` | runtime retained at candidate SHA-256 site; proof wrapper may later erase |
| `steve.get_digest` | runtime retained at get validation site; proof wrapper may later erase |
| `steve.no_clobber` | structural authority/call-surface fact plus BlobProvider assumption boundary |
| `steve.atomic_publish` | BlobProvider assumption boundary remains live |
| `steve.put_idempotent` | transferred into exact-equality CFG plus no-clobber guarantee |
| `steve.collision_fails` | transferred into inequality -> existing-digest-check -> collision CFG; runtime check retained |
| `steve.corruption_fails` | transferred into digest-reject failure edges; runtime check shared with get/collision mechanisms |
| `steve.no_delete` | structural authority/call-surface fact; no runtime delete capability or operation |
| `steve.crash_state` | BlobProvider crash-semantics assumption boundary remains live |
| `steve.install_borrow_scope` | transferred into `InvariantBorrowAliases` for the candidate plus provider copied-publication assumption |
| `steve.digest_evidence_identity` | stable semantic owner/storage identity survives; temporary borrow, physical address, placement, and layout do not become proposition identity |
| `steve.byte_equality_evidence` | exact comparison remains runtime; evidence wrapper may erase into branch control |

Facts that depend only on a provider TCB must not be mislabeled `FactRuntimeRetained`: `RuntimeSiteRef` is specifically for selected `RuntimeEnforced` evidence, whereas the provider boundaries in the Steve manifest are explicitly `Assumed`.

## Structural invariants that fit the current verifier

The current systems invariant vocabulary already gives Steve several useful checks:

- `InvariantBorrowAliases` for candidate digest/install views, candidate/existing compare views, and get/existing digest-check views;
- the borrow invariant also rejects a hidden `OpCopy` from the owner;
- `InvariantRequiredEdge` for compare-equal -> `PutOk`, compare-different -> existing digest check, digest-reject -> corruption failure, digest-accept -> collision, get-digest-accept -> `GetOk`, and get-digest-reject -> integrity failure;
- `InvariantCleanupOwners` for every branch that must release candidate/existing/get owners;
- ordinary owning-storage uniqueness rejects two systems owners for one storage identity.

Steve does not need transport-handle or ingress-recognition invariants.

These current invariants are host-target sufficient for the first Steve artifact; they are not a complete ADR-012 execution-topology model. A later non-host target would additionally need explicit placement/transfer/synchronization/representation invariants where required by its selected execution domain.

## Lowering decisions and cost attribution

The first Steve lowering ledger should include at least these decisions:

### `steve.lower.candidate_borrow`

- action: `Borrow`
- class: `SemanticRequired`
- before: owning candidate bytes
- after: owner plus non-owning slice
- cost: expected `0` bytes copied on the selected host representation
- invariant: view aliases candidate owner

### `steve.lower.digest_compute`

- action: `Retain` or `InsertCheck` according to the final call/control representation
- class: `SemanticRequired`
- obligation/evidence: `STEVE-PUT-DIGEST` / put runtime evidence
- cost: SHA-256 over candidate bytes, once per `put`
- residue: content-derived ID plus success evidence/control fact

### `steve.lower.install_if_absent`

- action: `Retain`
- class: `SemanticRequired`
- target: BlobProvider call using a borrowed candidate view
- assumptions: BlobProvider no-replace/atomic/copied-publication boundary
- no overwrite or delete operation may appear in Steve's target call surface

### `steve.lower.byte_compare`

- action: `RepresentAsControlFlow`
- class: `SemanticRequired`
- obligation/evidence: `STEVE-BYTE-EQUALITY-EVIDENCE` / comparison runtime evidence
- cost: worst-case linear byte comparison, only on existing-object path
- invariant: equal and different successors remain distinct

### `steve.lower.existing_digest_check`

- action: `InsertCheck`
- class: `SemanticRequired`
- obligation/evidence: collision runtime evidence, plus corruption authority once multi-claim sites are representable
- cost: SHA-256 over existing bytes only after exact inequality
- invariant: rejection cannot reach ordinary success; acceptance after inequality reaches collision

### `steve.lower.get_digest_check`

- action: `InsertCheck`
- class: `SemanticRequired`
- obligation/evidence: get-digest runtime evidence, plus corruption authority once multi-claim sites are representable
- cost: SHA-256 recomputation/comparison once per successful read
- invariant: rejection releases bytes; only acceptance can transfer the owner into `GetOk`

### `steve.lower.cleanup`

- action: `Cleanup`
- class: `SemanticRequired`
- every failure branch accounts for every owning byte object exactly once

The important performance property is explicit in the ledger: the equality path pays `bytes_compare` but does not pay a second `digest_check`. The existing-object SHA-256 cost is conditional on witnessed inequality.

Storage I/O costs may later receive their own lowering decisions, but they should not be smuggled into `steve.runtime.digest_*` or `steve.runtime.bytes_compare` assurance-cost identities. Likewise, if a future selected execution topology introduces transfer, staging, synchronization, or representation-conversion costs, ADR-011/012 require those costs to remain separately attributable rather than disappearing inside a vendor/backend operation.

## Proof/evidence erasure plan

The current Steve assurance manifest has retained-runtime uses but **no `ErasureUse` records**. Therefore the first systems sketch must not yet emit `OpEraseFact` and claim a certified proof wrapper disappeared.

A later append-only Steve assurance extension should explicitly authorize erasure of source-level proof values that have completed their compile-time job, likely including:

- `Proof[DigestMatches]` carried by successful `PutOk`;
- `Proof[DigestMatches]` carried by successful `GetOk`;
- `BytewiseEqual` / `BytewiseDifferent` branch evidence once represented by checked CFG edges;
- existing-object digest evidence carried by the collision result if the runtime ABI does not materialize proof objects.

Each erasure must cite an exact selected obligation revision/evidence set and must transfer any still-relevant semantic fact into a checked target invariant or selected derived obligation. `ContentId`, owned bytes, result/failure discriminants, and actual runtime checks are not proof wrappers and must not disappear merely because nearby evidence erases.

## Pressure-test findings against the current systems IR

Steve exposes four concrete generalization points.

### 1. Assumption-bound stage facts are not first-class

`FactDisposition` currently has consumed, transferred, erased, runtime-retained, and derived forms, but no form that points to an ADR-010 `AssumptionId`. `StageContract.stageAssumptions` is only `[Text]`.

That is insufficient for Steve's `STEVE-ATOMIC-PUBLISH` and `STEVE-CRASH-STATE`, whose accepted authority is explicitly an assumption node. Encoding them as `FactConsumed "delegated to provider"` would erase the content-addressed assumption boundary we just worked to make explicit.

Likely systems generalization: a first-class assumption-bound disposition such as `FactAssumed AssumptionId`, checked against the selected manifest and effective validity scope.

### 2. One physical runtime site may justify several obligation revisions

`RuntimeSiteRef` currently contains exactly one revision and one evidence entry. Steve's get digest check simultaneously realizes `STEVE-GET-DIGEST` and the fail-closed `STEVE-CORRUPTION-FAILS` property; the existing-object digest check similarly realizes collision classification and corruption rejection.

Duplicating the physical check would falsify the cost model. Picking only one evidence entry would understate the assurance relation.

The required generalization is now sharper than merely replacing the singleton evidence field with a list. The model must distinguish:

> runtime primitive/execution-profile identity != physical Systems-site identity != assurance claim identity

One physical site should carry a nonempty set/list of exact `(RevisionId, EvidenceEntryId, subject...)` assurance claims plus one physical cost reference and an independently identified runtime primitive/execution profile. Multiple sites may use the same primitive. One site may carry multiple claims. Neither relationship licenses collapsing or duplicating the assurance/cost-bearing mechanism.

PR #43 applied this lesson outside Steve: recognized-record ABI v1 forbids deriving host runtime primitive symbols from evidence/revision/use IDs or claim-set shape. PR #44 then demonstrated the host specialization in the implemented/validated ABI candidate. ADR-012 constrains the generic form further: the site cannot itself mean “LLVM call”; other targets may use different explicit realization relations below Systems.

### 3. Provider authority needs a checked systems invariant

Steve's no-clobber/no-delete claims are architectural authority claims: the target should possess/use only `read` and atomic `install-if-absent`, never arbitrary replace/delete. `RuntimeRecord "BlobProvider"` does not express that restriction, and the current invariant vocabulary has no provider-call-surface/capability claim.

Likely systems generalization: a provider/capability invariant that can say which operations a systems function may invoke through a provider handle, with negative authority made checkable rather than prose.

ADR-012's execution-domain capability model is adjacent but distinct: provider capability constrains external/provider authority, while execution-domain capability constrains placement, representation, synchronization, numerical/resource behavior, and target feasibility. The generic Systems model should keep those authority surfaces explicit rather than collapsing either one into backend convention.

### 4. Stable evidence identity is only partially represented

`systemsStorageIdentity` plus `BorrowedSlice owner` correctly separates owner identity from loan identity, and `InvariantBorrowAliases` checks aliasing/no-copy. But the systems verifier cannot yet state that the persistent evidence attached to a digest site is about the owner's stable semantic identity and **not** the borrow value.

ADR-012 also means that stable subject identity cannot be defined by physical address, current execution-domain placement, storage class, or one runtime layout. A target may preserve a semantic assurance subject across an explicit transfer/migration/representation refinement, but that continuity must be checked rather than inferred from pointer equality, equal bytes, or target convention.

Likely systems generalization: an invariant or runtime-site subject binding that links an assurance claim to a stable semantic systems value/storage identity while recording borrowed views and target representations only as observation/realization mechanisms, plus explicit correspondence for any placement/representation change that preserves the subject.

## Classification

These findings do not currently justify a new Steve-specific Phil ADR. They are representation/verifier generalizations required to carry already-accepted decisions through the Systems boundary:

- ADR-001/002/005 define authority, ownership, loans, and per-arm resource behavior;
- ADR-006 defines opaque claims/evidence and competent runtime producers;
- ADR-007 requires property-directed systems representations;
- ADR-010 makes assumptions/evidence/uses content-addressed and explicit;
- ADR-011 requires runtime residue and cost attribution to remain explicit;
- ADR-012 requires execution placement, data movement, synchronization, representation, and target capability to become explicit at the Systems boundary, while forbidding generic assumptions of one coherent address space, one scalar sequential control model, invisible/free transfer, or one canonical runtime representation.

Steve is doing its intended job here: the upload witness established the first systems vocabulary, and the first independent program is showing exactly where that vocabulary was still upload-shaped. PR #43 is concrete evidence that the pressure test is also catching cross-layer leaks early: Generalization 2 changed a runtime ABI rule before the first recognized-record implementation/certification artifact existed. ADR-012 ensures that the resulting fix remains a genuine Systems abstraction rather than merely a cleaner host ABI.

## Executable-promotion criteria

A branch-local executable Steve systems fixture should be added only after the representation can say these things without lying:

1. provider assumption-bound facts remain first-class and selected;
2. one physical digest site can carry all of its exact assurance claims without duplicating runtime cost, while runtime primitive/execution-profile identity remains independent of both physical site identity and claim-set identity and distinct sites do not collapse merely because they use the same primitive;
3. the generic physical-site representation is not defined by a host call, linker symbol, pointer/address identity, coherent address space, or universal sequential control model; the first Steve artifact may select those host simplifications only as its execution topology;
4. no-clobber/no-delete authority is checkable at the systems provider boundary;
5. stable evidence subjects are bound to semantic owner/storage identity rather than borrow token, physical address, placement, or one target representation, with explicit checked correspondence for any subject-preserving transfer/representation change;
6. Steve's assurance graph is extended with any required erasure uses before proof wrappers disappear;
7. the systems verifier accepts the positive Steve artifact and rejects mutations for duplicate ownership, hidden copy, missing digest check, equality-path rehash, collision-as-success, corruption laundering, missing cleanup, provider authority widening, assumption loss, primitive/site/claim identity conflation, unaccounted target transfer/representation change, and lowering/cost-root tampering.

Until then this document is the systems-IR handoff target, not a claim that Steve already has a certified systems lowering.
