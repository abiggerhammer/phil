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
- `get.bytes` — `OwnedBuffer "OwnedBytes[stored]"`
- `get.bytes_view` — `BorrowedSlice get.bytes`
- result/failure discriminants — ordinary runtime scalars/records

`RuntimeRecord` is only a representation placeholder for provider handles. It does **not** by itself encode provider authority. The source/static architecture remains responsible for saying that Steve receives read/install-if-absent authority and no overwrite/delete authority.

Stable byte-object identities should be carried by systems metadata such as `systemsStorageIdentity`, not by the ephemeral `BorrowedSlice` value. This preserves the Steve rule that persistent evidence names the owner/snapshot identity rather than a loan token.

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

The current Steve assurance graph contains five `RetainedRuntimeUse` records over three cost identities. Four distinct physical runtime mechanisms are expected in the systems CFG:

| Physical site | Kind | Obligation/evidence | Cost ref | Dynamic condition |
| --- | --- | --- | --- | --- |
| `put.digest.compute` | `DigestBoundary` | `STEVE-PUT-DIGEST` / `evidence.steve.put_digest.runtime` | `steve.runtime.digest_compute` | every `put` before publication |
| `put.byte_compare` | `SourceSemanticRuntime "bytes_compare"` | `STEVE-BYTE-EQUALITY-EVIDENCE` / `evidence.steve.byte_equality.runtime` | `steve.runtime.bytes_compare` | only `AlreadyExists` + successful read |
| `put.existing.digest_check` | `DigestBoundary` | `STEVE-COLLISION-FAILS` / `evidence.steve.collision.runtime` | `steve.runtime.digest_check` | only after exact inequality |
| `get.digest_check` | `DigestBoundary` | `STEVE-GET-DIGEST` / `evidence.steve.get_digest.runtime` | `steve.runtime.digest_check` | only after successful read |

`STEVE-CORRUPTION-FAILS` is also backed by `evidence.steve.corruption.runtime` and `use.steve.corruption_digest`, but corruption rejection is not a fifth physical digest computation. It is a logical property of the existing digest-check sites above. This exposes a systems-IR generalization described below; we should not invent a duplicate runtime check just to satisfy a one-evidence-per-site representation.

The names in the first column are **physical program-site identities**, not runtime primitive or linker-symbol identities. In particular, `put.existing.digest_check` and `get.digest_check` may legitimately invoke the same digest-validation primitive/signature while remaining two distinct physical sites because they occur at different program locations and under different dynamic conditions. Conversely, each one remains a single physical site even when its exact assurance claim set contains more than one logical obligation. Runtime primitive/signature identity, physical site identity, and assurance claim identity must therefore remain separately represented and separately checked.

Following PR #43, any eventual runtime symbol for such a primitive must be derived from the physical operation family and ABI-relevant signature/profile, not from `RevisionId`, `EvidenceEntryId`, `AssuranceUseId`, or claim-set cardinality/order. Adding a corruption-rejection claim to an existing digest site must not rename the primitive, create an alias per claim, or induce a second digest execution/cost.

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
| `steve.digest_evidence_identity` | stable owner/storage identity survives; temporary borrow does not become the proposition identity |
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

## Lowering decisions and cost attribution

The first Steve lowering ledger should include at least these decisions:

### `steve.lower.candidate_borrow`

- action: `Borrow`
- class: `SemanticRequired`
- before: owning candidate bytes
- after: owner plus non-owning slice
- cost: expected `0` bytes copied
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

Storage I/O costs may later receive their own lowering decisions, but they should not be smuggled into `steve.runtime.digest_*` or `steve.runtime.bytes_compare` assurance-cost identities.

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

> runtime primitive/signature identity != physical program-site identity != assurance claim identity

One physical site should carry a nonempty set/list of exact `(RevisionId, EvidenceEntryId, subject...)` assurance claims plus one physical cost reference and an independently identified runtime primitive/signature. Multiple sites may invoke the same primitive. One site may carry multiple claims. Neither relationship licenses collapsing or duplicating physical execution.

PR #43 has already applied this lesson outside Steve: recognized-record ABI v1 now forbids deriving runtime primitive symbols from evidence/revision/use IDs or claim-set shape. That change prevents the old singleton assurance representation from being frozen into a linker-visible ABI before the generalized Systems model lands.

### 3. Provider authority needs a checked systems invariant

Steve's no-clobber/no-delete claims are architectural authority claims: the target should possess/use only `read` and atomic `install-if-absent`, never arbitrary replace/delete. `RuntimeRecord "BlobProvider"` does not express that restriction, and the current invariant vocabulary has no provider-call-surface/capability claim.

Likely systems generalization: a provider/capability invariant that can say which operations a systems function may invoke through a provider handle, with negative authority made checkable rather than prose.

### 4. Stable evidence identity is only partially represented

`systemsStorageIdentity` plus `BorrowedSlice owner` correctly separates owner identity from loan identity, and `InvariantBorrowAliases` checks aliasing/no-copy. But the systems verifier cannot yet state that the persistent evidence attached to a digest site is about the owner's stable identity and **not** the borrow value.

Likely systems generalization: an invariant or runtime-site subject binding that links an assurance claim to a stable systems value/storage identity while recording the borrowed view only as the observation mechanism.

## Classification

These findings do not currently justify a new Phil ADR. They are representation/verifier generalizations required to carry already-accepted decisions through ADR-007/010/011:

- ADR-001/002/005 define authority, ownership, loans, and per-arm resource behavior;
- ADR-006 defines opaque claims/evidence and competent runtime producers;
- ADR-007 requires property-directed systems representations;
- ADR-010 already makes assumptions/evidence/uses content-addressed and explicit;
- ADR-011 requires runtime residue and cost attribution to remain explicit.

Steve is doing its intended job here: the upload witness established the first systems vocabulary, and the first independent program is showing exactly where that vocabulary was still upload-shaped. PR #43 is concrete evidence that the pressure test is also catching cross-layer leaks early: Generalization 2 changed a runtime ABI rule before the first recognized-record implementation/certification artifact existed.

## Executable-promotion criteria

A branch-local executable Steve systems fixture should be added only after the representation can say these things without lying:

1. provider assumption-bound facts remain first-class and selected;
2. one physical digest check can carry all of its exact assurance claims without duplicating runtime cost, while runtime primitive/signature identity remains independent of both physical site identity and claim-set identity and distinct sites do not collapse merely because they invoke the same primitive;
3. no-clobber/no-delete authority is checkable at the systems provider boundary;
4. stable evidence subjects are bound to owner/storage identity rather than the borrow token;
5. Steve's assurance graph is extended with any required erasure uses before proof wrappers disappear;
6. the systems verifier accepts the positive Steve artifact and rejects mutations for duplicate ownership, hidden copy, missing digest check, equality-path rehash, collision-as-success, corruption laundering, missing cleanup, provider authority widening, assumption loss, primitive/site/claim identity conflation, and lowering/cost-root tampering.

Until then this document is the systems-IR handoff target, not a claim that Steve already has a certified systems lowering.