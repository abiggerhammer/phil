# Steve systems generalization handoff

Status: implementation/proof handoff; branch-only pressure-test material; no new Phil ADR proposed

Baseline for this handoff:

- `main` through PR #35 (`b215c5b0fc434d420d1847901f5f399516c857f6`), including the Systems ownership/runtime proofs, LLVM translation-validation proofs, runnable `philc`, typed scalar transport, and concrete Phase 0 LLVM translation certification;
- `steve/architecture-sketch` synchronized through that baseline;
- Steve rejected fixture 02 promoted to a branch-local semantic CI check requiring exactly `OpaqueProof` for generic proof of opaque `DigestMatches`;
- PR #36 is intentionally separate work on the first real checked Surface -> Systems scalar SSA/dataflow lowering. Do not fold Steve-specific resource/provider lowering into that tranche.

This document turns the four gaps identified in `lowering-contract.md` into a concrete Haskell/Rocq handoff. The goal is not to make the existing verifier accept Steve by special case. The goal is to generalize the current property-directed Systems representation so that Steve can be expressed without lying about assumptions, physical runtime cost, authority, or evidence subject identity.

## Invariants for the generalization

Any implementation should preserve these constraints:

1. Existing Phase 0/upload Systems artifacts remain valid singleton cases of the generalized representation.
2. No generic Systems/LLVM module contains Steve-specific names, filename switches, obligation IDs, or provider names.
3. A physical runtime operation is represented once. Runtime primitive/signature identity, physical program-site identity, and assurance claim identity are distinct; multiple logical claims must not force duplicated calls, branches, linker symbols, or cost.
4. Assumptions remain content-addressed assurance nodes with explicit validity scope; they are never collapsed to prose such as `"delegated to provider"`.
5. Negative authority claims are about what capability is possessed, not merely about which calls happen to appear in one program.
6. Persistent assurance subjects bind to stable owner/storage identity. Borrowed views may be observation mechanisms but must not silently become persistent identities.
7. Existing ADR-010 erasure discipline remains unchanged: no `OpEraseFact` without an exact selected erasure use and surviving semantic carrier.
8. Current Systems and LLVM proof obligations should be generalized monotonically: the existing one-claim/singleton cases should follow as special cases rather than being replaced by unrelated theorems.

## Generalization 1: first-class assumption dependencies on stage facts

### Problem

`FactDisposition` currently provides consumed, transferred, erased, runtime-retained, and derived cases. `StageContract.stageAssumptions` is only `[Text]`.

That cannot faithfully represent a fact whose authority remains assumption-bound after lowering. Steve's `STEVE-ATOMIC-PUBLISH` and `STEVE-CRASH-STATE` are pure examples. Mixed cases are more revealing: `STEVE-NO-CLOBBER` has both a structural authority component and a BlobProvider assumption boundary, while `STEVE-INSTALL-BORROW-SCOPE` has a checked alias/scope component plus a provider copied-publication assumption.

A single new `FactAssumed AssumptionId` constructor is therefore useful but not sufficient by itself: mixed facts need to transfer structure while retaining an explicit assumption dependency.

### Target representation

An acceptable shape is conceptually:

```haskell
data FactDisposition
  = FactConsumed Text
  | FactTransferred [InvariantId]
  | FactErased AssuranceUseId
  | FactRuntimeRetained EvidenceEntryId
  | FactDerived RevisionId
  | FactAssumed AssumptionId

data FactTransfer = FactTransfer
  { factTransferId :: Text
  , factSourceRevision :: Maybe RevisionId
  , factDisposition :: FactDisposition
  , factAssumptionDependencies :: Set AssumptionId
  }
```

The exact Haskell spelling is not normative. The semantic distinction is:

- `FactAssumed a`: the target fact itself remains discharged only through assumption `a`;
- `factAssumptionDependencies`: assumptions that remain live even when another part of the same source fact is transferred/retained/derived.

Do not encode mixed facts as multiple fake source facts merely to fit the datatype. The source-fact set should still correspond to actual obligation revisions.

### Verifier requirements

For every assumption attached to a stage fact, verification should establish all of the following:

- the `AssumptionId` exists in the assurance ledger;
- it is selected by the manifest;
- its validity scope is effective in the manifest/build validity context;
- the source revision is exact when `factSourceRevision` is present;
- the accepted assurance closure for that source revision actually depends on selected `Assumed` evidence citing the same assumption, rather than an unrelated selected assumption being attached opportunistically;
- a fact listed in `systemsFactsRequiringTransfer` cannot evade its transfer requirement merely by attaching an assumption unless the context explicitly classifies that fact as assumption-dischargeable.

The free-text `stageAssumptions` field may remain as commentary/provenance if useful, but it must no longer be the authority-bearing representation.

### Rocq target

Generalize `proof/Phil/Systems/FactDisposition.v` so successful normalized fact verification proves exact selected/effective assumption authority for both pure-assumed and mixed transferred-plus-assumption cases. Preserve the existing consumed/transferred/erased/runtime/derived theorems as singleton cases.

### Adversarial tests

Reject at least:

- assumption ID absent from the ledger;
- assumption present but not selected by the manifest;
- selected assumption with incompatible validity scope;
- assumption attached to the wrong source revision;
- mixed structural fact with its required assumption dependency deleted;
- pure assumption-backed fact rewritten as `FactConsumed "delegated"`;
- transfer-required fact replaced by an assumption without explicit authorization.

Steve acceptance examples after the generalization:

- `STEVE-ATOMIC-PUBLISH`: pure BlobProvider assumption-bound disposition;
- `STEVE-CRASH-STATE`: pure BlobProvider assumption-bound disposition;
- `STEVE-NO-CLOBBER`: provider-authority invariant plus BlobProvider assumption dependency;
- `STEVE-INSTALL-BORROW-SCOPE`: borrow/alias invariant plus BlobProvider assumption dependency.

## Generalization 2: one physical runtime site, multiple exact assurance claims

### Problem

`RuntimeSiteRef` currently binds one `RevisionId`, one `EvidenceEntryId`, and one cost reference. PR #31 mechanizes the corresponding runtime realization discipline.

Steve has four physical runtime mechanisms but five retained-runtime assurance uses. A get-side digest validation physically executes once while supporting both the successful-digest obligation and corruption rejection. The existing-object digest validation likewise physically executes once while supporting collision classification and corruption rejection.

Duplicating a digest operation to satisfy the representation would make the cost model false. Selecting only one claim would make the assurance relation incomplete.

### Target representation

Represent a physical site once, with an explicit physical site identity, one physical primitive/signature identity, one physical kind/cost identity, and a nonempty exact claim set. Conceptually:

```haskell
data RuntimePrimitiveRef = RuntimePrimitiveRef
  { runtimePrimitiveOperation :: Text
  , runtimePrimitiveABIProfile :: Text
  , runtimePrimitiveSignature :: RuntimeSignature
  }

data RuntimeSiteClaim = RuntimeSiteClaim
  { runtimeClaimRevision :: RevisionId
  , runtimeClaimEvidence :: EvidenceEntryId
  , runtimeClaimSubjects :: [AssuranceSubjectBinding]
  }

data RuntimeSiteRef = RuntimeSiteRef
  { runtimeSiteId :: RuntimeSiteId
  , runtimeSitePrimitive :: RuntimePrimitiveRef
  , runtimeSiteKind :: RuntimeSiteKind
  , runtimeSiteClaims :: NonEmpty RuntimeSiteClaim
  , runtimeSiteCostRef :: Text
  }
```

The exact Haskell spelling is not normative. `runtimeClaimSubjects` is described under Generalization 4; it may be introduced in the same tranche or immediately after the multi-claim shape.

### Identity separation

PR #43 exposed a cross-layer consequence of this generalization before the first recognized-record ABI implementation artifact existed. The generalized model must preserve three independent identities:

> runtime primitive/signature identity != physical program-site identity != assurance claim identity

A runtime primitive identifies the semantic/physical operation family together with its ABI-relevant signature/profile. A physical site identifies one program invocation site and carries its physical cost attribution. The claim set identifies the exact logical assurance bindings justified at that site. None is derivable from either of the others.

Therefore:

- multiple distinct physical sites may invoke the same runtime primitive symbol;
- one physical site may justify multiple exact assurance claims;
- adding, removing, or reordering assurance claims must not by itself rename the runtime primitive or duplicate physical execution/cost;
- changing the primitive ABI signature/profile must change the bound primitive/profile identity even when the claim set is unchanged;
- linker-visible runtime symbols must not be derived from `RevisionId`, `EvidenceEntryId`, `AssuranceUseId`, or claim-set cardinality/order.

This is not merely a symbol-naming convention. It is the representation boundary that prevents a contingent assurance decomposition from becoming a physical ABI commitment. Semantic operation names such as a schema field accessor may still appear in a symbol when they describe the operation actually being performed; assurance bookkeeping identities may not.

### Verifier requirements

For each physical site:

- every claim pair is unique;
- every revision and evidence entry is selected;
- every evidence entry exists, is `RuntimeEnforced`, and names the exact revision;
- the physical cost ref is authorized by each claim's selected runtime evidence where the claim asserts that physical mechanism;
- expected runtime-site kind checks remain exact;
- no claim may be added merely because an evidence entry happens to share a cost string;
- the physical site identity remains distinct from the primitive identity, so two sites invoking the same primitive cannot collapse into one site;
- the primitive identity is determined by operation/signature/profile rather than assurance IDs or claim-set shape;
- changing only the exact claim set cannot by itself change the primitive/symbol identity or multiply the physical site.

For retained-runtime uses, generalize the PR #31 rule from "one use -> one matching singleton site" to:

> every selected `RetainedRuntimeUse` has exactly one physical site whose claim set contains its exact `(revision,evidence)` pair and whose physical cost ref is the use's cost ref.

Several distinct uses may map to the same physical site. The reverse relation is therefore not injective. A physical site must not be duplicated per logical use.

### Rocq target

Generalize `proof/Phil/Systems/Runtime.v` to model physical sites with claim sets. The key theorem should preserve per-use uniqueness while allowing multiple uses to inhabit one site. Existing singleton Phase 0 sites should prove the generalized theorem directly.

The normalized model should not identify sites merely because they share a primitive/signature, nor identify primitive identity with any assurance claim. If symbol construction is modeled, its inputs should be the primitive operation/profile/signature rather than evidence/revision/use identity.

### Downstream LLVM consequence

PR #33/#35 make runtime-site preservation part of the LLVM translation-validation/certification chain, and PR #43 makes the identity split explicit at the ABI boundary. The LLVM boundary must preserve **physical site multiplicity and the exact claim set** without using assurance IDs to determine the runtime linker symbol.

Translation validation should therefore check two distinct properties:

1. **physical operation preservation** — each Systems physical site maps to exactly one corresponding LLVM call site with the expected primitive/signature/profile and physical cost identity; distinct Systems sites remain distinct even when they invoke the same primitive symbol;
2. **claim-set preservation** — every exact `(revision,evidence,subject...)` binding attached to that Systems site survives in the LLVM-side verification relation, without manufacturing extra calls or changing the primitive symbol merely because the claim set changed.

If the normalized `PHIL-LLVM-PRESERVE-001` model counts runtime sites, generalize it so the count remains a count of physical mechanisms and claim-set identity is checked separately. The concrete Phase 0 certification should remain green as a singleton instance.

### Adversarial tests

Reject at least:

- claim with unselected evidence;
- claim whose evidence names another revision;
- duplicate `(revision,evidence)` within one site;
- retained use missing from every physical site's claim set;
- retained use appearing in two physical sites;
- shared physical site split into duplicate calls solely to satisfy two claims;
- physical cost ref inconsistent with one of the claims;
- LLVM target that preserves the calls but drops or mutates one claim binding;
- changing a runtime primitive symbol solely because a second assurance claim is attached;
- encoding an evidence/revision/use ID into a runtime primitive symbol;
- collapsing two distinct physical sites merely because they invoke the same primitive/signature;
- changing the primitive ABI signature without changing the bound runtime ABI/profile identity.

Steve acceptance examples:

- `get.digest_check`: one physical SHA-256 validation site carrying `STEVE-GET-DIGEST` and `STEVE-CORRUPTION-FAILS` claims;
- `put.existing.digest_check`: one physical SHA-256 validation site carrying `STEVE-COLLISION-FAILS` and the relevant corruption-rejection claim.

Those two sites may legitimately invoke the same digest-validation primitive/signature while remaining distinct physical sites because they occur at different program locations and under different dynamic conditions. Conversely, each site remains one physical execution even when its claim set contains multiple logical obligations.

## Generalization 3: checked provider capability possession and use

### Problem

`RuntimeRecord "BlobProvider"` is only a representation placeholder. Current `OpRuntimeCall` names an operation and lists input/output values, but it does not state which capability authorizes the call. Consequently the Systems verifier cannot distinguish:

- possessing a restricted provider capability that exposes only read and atomic install-if-absent;
- possessing a broader provider object but simply not calling replace/delete in this particular artifact.

Steve's `STEVE-NO-CLOBBER` and `STEVE-NO-DELETE` require the former. Absence of a call is not proof of absence of authority.

### Target representation

Introduce an explicit provider/capability concept at Systems level. The exact encoding is open, but it must represent both possession and use. One plausible decomposition is:

```haskell
data SystemsValueRole
  = ...
  | ProviderCapability ProviderContractId

data RuntimeAuthorityUse = RuntimeAuthorityUse
  { authorityHandle :: ValueId
  , authorityOperation :: Text
  }
```

and make provider-backed `OpRuntimeCall` cite its `RuntimeAuthorityUse` rather than relying on an input-position convention.

The provider contract/capability identity should determine the allowed operation set. A stage invariant may additionally bind a function boundary to the exact capability surface expected by the source architecture.

Do not make this a Steve-specific enum of `read/install/delete`. Generic text or content-identified operation names are fine; the important point is checked authority identity.

### Verifier requirements

- every authority-bearing runtime call cites an existing provider capability value;
- the cited operation is permitted by that capability's selected contract;
- the provider capability supplied to the function matches the architecture/stage invariant expected for that semantic boundary;
- broad capability cannot be silently substituted for a narrow one merely because only narrow calls occur;
- copying/forging/delegating provider authority follows the existing structural mode rules rather than becoming unrestricted by representation accident.

For Steve the accepted BlobProvider capability must expose exactly the operations needed by Steve 0 (`read`, atomic no-replace `install-if-absent`) and no replace/delete authority. DigestProvider should similarly expose only the declared digest/check surface.

### Rocq target

Add a normalized authority/call-surface model proving that successful Systems verification implies every provider operation is authorized by the exact capability possessed at that boundary, and that widening the capability or invoking an unauthorized operation makes verification impossible.

### Adversarial tests

Reject at least:

- `replace` call through read/install-only BlobProvider capability;
- `delete` call;
- call with no authority handle;
- call authorized by the wrong provider handle;
- target function given a broader provider capability than the stage contract permits;
- forged/copy-created capability if the source authority was restricted;
- invariant claiming a narrow surface while the actual capability identity is broad.

## Generalization 4: bind assurance subjects to stable owner/storage identity

### Problem

`systemsStorageIdentity` and `BorrowedSlice owner` correctly separate owner identity from a loan. `InvariantBorrowAliases` checks aliasing/no hidden copy. But a runtime assurance claim cannot yet state that its persistent subject is the stable owner/storage identity while the borrowed view is merely how the runtime observes the bytes.

That distinction is central to `STEVE-DIGEST-EVIDENCE-IDENTITY`: a digest claim must survive the borrow scope and therefore cannot be indexed by the ephemeral view token.

### Target representation

Add an explicit correspondence from assurance-level subject IDs to stable Systems values. Conceptually:

```haskell
data AssuranceSubjectBinding = AssuranceSubjectBinding
  { assuranceSubjectId :: Text
  , assuranceSubjectOwner :: ValueId
  }
```

The verifier should derive/check the stable storage identity from `assuranceSubjectOwner`; do not accept a free text storage ID with no owning value behind it.

Runtime operation inputs remain the observation mechanism. A digest call may consume/read `BorrowedSlice owner`, while the `RuntimeSiteClaim` binds the persistent assurance subject to `owner` and its `systemsStorageIdentity`.

### Verifier requirements

- the semantic subject ID occurs in the exact selected obligation revision's `revisionSubjectIds`;
- the bound Systems value exists and is an owning/stable-identity-bearing role where required;
- the owner has a stable `systemsStorageIdentity`;
- if the runtime mechanism observes through a `BorrowedSlice`, that view aliases the same owner;
- a borrowed view itself cannot be accepted as the persistent subject of the claim;
- hidden copies cannot silently change the subject while preserving only equal bytes.

### Rocq target

Extend the ownership/runtime normalized models with a subject-correspondence relation: persistent claim subject -> stable owner/storage identity, with borrow -> owner as an observation relation. Prove that successful verification cannot bind persistent evidence to the borrow token or to an unrelated owner.

### Adversarial tests

Reject at least:

- digest claim subject bound to `BorrowedSlice` rather than owner;
- subject bound to an owner with no stable identity;
- subject ID absent from the selected revision;
- observation view aliases a different owner;
- hidden copy used as the subject while the revision names the original object;
- correct owner/value but mismatched stable storage identity after target mutation.

## Cross-layer implementation order

The least disruptive order is:

1. land/finish the generic scalar SSA/dataflow work of PR #36 independently;
2. generalize Systems fact/assumption representation and `FactDisposition.v`;
3. generalize physical runtime sites and `Runtime.v`;
4. add provider capability possession/use plus its normalized authority proof;
5. add stable assurance-subject binding, preferably integrated with runtime-site claims;
6. update Systems digests/renderers and all Phase 0 constructors/tests so current artifacts are unchanged semantically;
7. update LLVM projection/verification and `Preservation.v` only where the generalized Systems metadata crosses that boundary;
8. re-run the concrete Phase 0 LLVM certification from PR #35 and keep it a singleton instance of the generalized model.

These may be rearranged if implementation dependencies demand it, but do not use Steve-specific wrappers to avoid touching the generic proof/model layer.

## Steve executable Systems promotion after the generalizations land

Only then add a branch-local positive `SystemsArtifact` for the control flow specified in `lowering-contract.md`.

The first positive artifact should preserve these physical facts exactly:

- four physical runtime mechanisms, not five;
- equal-byte retry performs exact byte comparison but no second SHA-256 digest;
- existing-object SHA-256 validation occurs only after witnessed byte inequality;
- `GetOk` is reachable only through digest-check acceptance;
- every failure path disposes of every owned buffer exactly once;
- BlobProvider authority is read + atomic no-replace install-if-absent, with no replace/delete capability;
- persistent digest evidence names stable byte-object identity, not borrow identity;
- runtime primitive/signature identity remains independent of both physical site identity and exact assurance claim-set identity;
- no proof/evidence wrapper is erased until Steve's assurance graph contains exact selected `ErasureUse` authority.

Then add adversarial mutations covering:

- omitted/wrong/stale assumption;
- missing one claim from a shared physical runtime site;
- duplicated physical site/cost for a second logical claim;
- evidence/revision/use identity leaking into a runtime primitive symbol;
- two distinct physical sites collapsed because they share a primitive/signature;
- widened BlobProvider authority or invented replace/delete call;
- digest subject rebound to borrowed view or wrong owner;
- equality path rehash;
- inequality path bypassing existing-object digest validation;
- get success bypassing digest validation;
- cleanup omission/double release/duplicate owner;
- hidden copy;
- forged erasure without selected `ErasureUse`;
- lowering decision/root or artifact identity tampering.

## What not to claim yet

Until the four representation points are implemented and the positive/adversarial Steve Systems fixtures pass:

- Steve does not have a certified Systems lowering;
- Steve does not have an LLVM artifact or native implementation produced by `philc`;
- PR #35 certifies only the exact canonical Phase 0 Systems -> LLVM pair, not arbitrary Phil programs and not Steve;
- the branch-local Steve assurance manifest remains a provisional semantic assurance case, not native provider implementation evidence.

## Definition of done for this handoff

This handoff is satisfied when all of the following are true on `main` without Steve-specific generic code:

1. the generalized Systems IR can represent all four points above faithfully, including the separation of runtime primitive/signature, physical site, and exact assurance claim identities;
2. the Haskell verifier rejects the listed generic adversarial cases;
3. Rocq proofs cover the generalized fact-assumption, runtime-site, provider-authority, and stable-subject rules;
4. existing Phase 0 Systems/LLVM fixtures and concrete PR #35 certification remain green;
5. the Steve branch can construct one honest positive Systems artifact with four physical runtime sites and twelve source obligation facts, and the Steve mutation suite fails closed.

At that point Steve stops being only a design pressure test at the Systems boundary and becomes the first independent application exercising the generalized property-directed lowering model.
