# Steve systems generalization handoff

Status: implementation/proof handoff; branch-only pressure-test material; no new Phil ADR proposed

Baseline for this handoff:

- `main` through PR #35 (`b215c5b0fc434d420d1847901f5f399516c857f6`), including the Systems ownership/runtime proofs, LLVM translation-validation proofs, runnable `philc`, typed scalar transport, and concrete Phase 0 LLVM translation certification;
- `steve/architecture-sketch` synchronized through that baseline;
- Steve rejected fixture 02 promoted to a branch-local semantic CI check requiring exactly `OpaqueProof` for generic proof of opaque `DigestMatches`;
- PR #36 is intentionally separate work on the first real checked Surface -> Systems scalar SSA/dataflow lowering. Do not fold Steve-specific resource/provider lowering into that tranche.

This document turns the four gaps identified in `lowering-contract.md` into a concrete Haskell/Rocq handoff. The goal is not to make the existing verifier accept Steve by special case. The goal is to generalize the current property-directed Systems representation so that Steve can be expressed without lying about assumptions, physical runtime cost, authority, or evidence subject identity.

ADR-012 is now an accepted cross-cutting constraint on this work. The host/CPU and LLVM call shapes used in the current Phase 0 examples are target-specific realizations, not definitions of the generic Systems abstractions. Execution placement, data movement, synchronization, representation changes, and execution-domain capabilities must remain explicit where a selected execution topology requires them.

## Invariants for the generalization

Any implementation should preserve these constraints:

1. Existing Phase 0/upload Systems artifacts remain valid singleton cases of the generalized representation.
2. No generic Systems/LLVM module contains Steve-specific names, filename switches, obligation IDs, or provider names.
3. A Systems physical runtime mechanism is represented once as an assurance- and cost-bearing site. Runtime primitive/signature identity, physical site identity, and assurance claim identity are distinct; multiple logical claims must not force duplicated physical mechanisms or cost. The backend realization of a site is target-specific and need not generically be a single function call.
4. Assumptions remain content-addressed assurance nodes with explicit validity scope; they are never collapsed to prose such as `"delegated to provider"`.
5. Negative authority claims are about what capability is possessed, not merely about which calls happen to appear in one program.
6. Persistent assurance subjects bind to stable semantic owner/object identity, not to a borrow token, machine address, execution-domain placement, or one runtime representation. Borrowed views and target representations may be observation mechanisms but must not silently become persistent identities.
7. Existing ADR-010 erasure discipline remains unchanged: no `OpEraseFact` without an exact selected erasure use and surviving semantic carrier.
8. Current Systems and LLVM proof obligations should be generalized monotonically: the existing one-claim/singleton host cases should follow as special cases rather than being replaced by unrelated theorems.
9. The generic representation must not require one coherent address space, one sequential control thread, invisible/cost-free transfer, or a canonical runtime representation. Any such simplification belongs to a selected execution topology or target-specific lowering after the ADR-012 boundary.

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

The exact Haskell spelling is not normative. In particular, `RuntimePrimitiveRef` must not imply a linker symbol, C ABI call, coherent host address space, or single-instruction backend realization; it denotes the selected Systems execution-topology mechanism/operation and the target-relevant profile needed to validate its realization. `runtimeClaimSubjects` is described under Generalization 4; it may be introduced in the same tranche or immediately after the multi-claim shape.

### Identity separation

PR #43 exposed a cross-layer consequence of this generalization before the first recognized-record ABI implementation artifact existed. The generalized model must preserve three independent identities:

> runtime primitive/signature identity != physical Systems-site identity != assurance claim identity

A runtime primitive identifies the semantic/physical operation family together with the selected execution-domain/ABI-relevant profile. A physical site identifies one assurance- and cost-bearing mechanism in the chosen Systems execution topology. The claim set identifies the exact logical assurance bindings justified at that site. None is derivable from either of the others.

Therefore:

- multiple distinct physical sites may use the same runtime primitive/mechanism profile;
- one physical site may justify multiple exact assurance claims;
- adding, removing, or reordering assurance claims must not by itself rename the runtime primitive or duplicate physical execution/cost;
- changing the primitive ABI/execution profile must change the bound primitive/profile identity even when the claim set is unchanged;
- linker-visible runtime symbols, when a target has them, must not be derived from `RevisionId`, `EvidenceEntryId`, `AssuranceUseId`, or claim-set cardinality/order.

This is not merely a symbol-naming convention. It is the representation boundary that prevents a contingent assurance decomposition from becoming a physical ABI or execution-topology commitment. Semantic operation names such as a schema field accessor may still appear in a symbol when they describe the operation actually being performed; assurance bookkeeping identities may not.

### ADR-012 execution-topology constraint

The generic meaning of a physical site must remain execution-topology-neutral. ADR-012 makes the Systems IR the layer where a chosen execution topology becomes explicit, but it does not define physical mechanisms as host function calls. Depending on the selected domain, a mechanism may be realized below Systems as a host runtime call, accelerator operation, kernel/graph node, pipeline stage, synchronization-delimited region, or another target-specific construct.

The required invariant is therefore not globally “one Systems site equals one backend call instruction.” It is:

> one Systems site remains one exact assurance/cost-bearing mechanism in the selected execution topology, and the target lowering provides an explicit realization relation for that site without manufacturing or losing claim authority or attributable cost.

A target realization may be structurally composite below the Systems boundary. If it is, the lowering/certification relation must identify the whole realization with the exact Systems site and account for any target-required transfers, synchronization, staging, representation conversion, or other costs. Claim multiplicity must never be used as a reason to duplicate that realization.

For the current Phase 0 host/LLVM target, the selected ABI specializes this rule to one Systems runtime site -> one corresponding LLVM runtime call site. That host specialization must not leak back into the generic `RuntimeSiteRef` ontology or Rocq theorem statement.

### Verifier requirements

For each physical site:

- every claim pair is unique;
- every revision and evidence entry is selected;
- every evidence entry exists, is `RuntimeEnforced`, and names the exact revision;
- the physical cost ref is authorized by each claim's selected runtime evidence where the claim asserts that physical mechanism;
- expected runtime-site kind checks remain exact;
- no claim may be added merely because an evidence entry happens to share a cost string;
- the physical site identity remains distinct from the primitive identity, so two sites using the same primitive cannot collapse into one site;
- the primitive identity is determined by operation/execution profile/signature rather than assurance IDs or claim-set shape;
- changing only the exact claim set cannot by itself change the primitive identity or multiply the physical site;
- site identity is not derived from a backend instruction address, linker symbol, host pointer, or other target-local representation artifact;
- when target lowering represents one site with a composite backend realization, the exact realization relation and total attributable cost remain bound to that one site.

For retained-runtime uses, generalize the PR #31 rule from "one use -> one matching singleton site" to:

> every selected `RetainedRuntimeUse` has exactly one physical site whose claim set contains its exact `(revision,evidence)` pair and whose physical cost ref is the use's cost ref.

Several distinct uses may map to the same physical site. The reverse relation is therefore not injective. A physical site must not be duplicated per logical use.

### Rocq target

Generalize `proof/Phil/Systems/Runtime.v` to model physical sites with claim sets. The key theorem should preserve per-use uniqueness while allowing multiple uses to inhabit one site. Existing singleton Phase 0 sites should prove the generalized theorem directly.

The normalized Systems theorem should be phrased in terms of site/mechanism identity, claims, and cost rather than host call instructions. A separate target-preservation theorem may specialize the relation to one LLVM call for the current host ABI. The normalized model should not identify sites merely because they share a primitive/signature, nor identify primitive identity with any assurance claim. If symbol construction is modeled, its inputs should be the primitive operation/profile/signature rather than evidence/revision/use identity.

### Downstream target-lowering consequence

PR #33/#35 make runtime-site preservation part of the LLVM translation-validation/certification chain, and PR #43 makes the identity split explicit at the ABI boundary. ADR-012 requires the generic target relation to preserve the Systems physical mechanism without making host call structure universal.

At the target boundary, validation should check two distinct properties:

1. **physical mechanism preservation** — the exact Systems site has one declared target realization with the expected primitive/execution profile and attributable cost; distinct Systems sites remain distinct even when they use the same primitive/profile, and any composite target realization is explicitly bound as one site's realization;
2. **claim-set preservation** — every exact `(revision,evidence,subject...)` binding attached to that Systems site survives in the target-side verification relation, without manufacturing extra mechanisms or changing target primitive identity merely because the claim set changed.

For the current host/LLVM target, physical-mechanism preservation specializes further: each Systems runtime site maps to exactly one corresponding LLVM runtime call site with the expected primitive/signature/profile and physical cost identity. If the normalized `PHIL-LLVM-PRESERVE-001` model counts runtime sites, the count remains a count of Systems physical mechanisms and claim-set identity is checked separately. The concrete Phase 0 certifications should remain green as singleton host instances.

### Adversarial tests

Reject at least:

- claim with unselected evidence;
- claim whose evidence names another revision;
- duplicate `(revision,evidence)` within one site;
- retained use missing from every physical site's claim set;
- retained use appearing in two physical sites;
- shared physical site split into duplicate target mechanisms solely to satisfy two claims;
- physical cost ref inconsistent with one of the claims;
- target artifact that preserves the mechanism but drops or mutates one claim binding;
- changing a runtime primitive symbol solely because a second assurance claim is attached;
- encoding an evidence/revision/use ID into a runtime primitive symbol;
- collapsing two distinct physical sites merely because they use the same primitive/signature/profile;
- changing the primitive ABI/execution profile without changing the bound target profile identity;
- treating a backend call address, symbol, instruction ID, or pointer as the generic physical-site identity;
- using a composite target realization without an explicit relation tying the whole realization and its total attributable cost back to the exact Systems site.

Steve acceptance examples:

- `get.digest_check`: one physical SHA-256 validation site carrying `STEVE-GET-DIGEST` and `STEVE-CORRUPTION-FAILS` claims;
- `put.existing.digest_check`: one physical SHA-256 validation site carrying `STEVE-COLLISION-FAILS` and the relevant corruption-rejection claim.

For Steve 0's selected host/CPU execution topology, those two sites may legitimately invoke the same digest-validation runtime primitive/signature while remaining distinct physical sites because they occur at different program locations and under different dynamic conditions. Conversely, each site remains one physical execution/cost-bearing mechanism even when its claim set contains multiple logical obligations.

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

ADR-012 introduces execution-domain capability as a neighboring Systems concept, but provider authority and execution-domain capability must not be conflated. A provider contract answers which external/provider operations the program may perform; an execution-domain capability answers which placements, representations, synchronization mechanisms, numerical modes, and resources a selected target can support. Both must be explicit when they carry correctness authority.

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

ADR-012 sharpens the requirement further: a stable assurance subject must also survive permitted execution-placement, address-space, and representation changes. Stable subject identity is semantic identity, not pointer/address identity and not a claim that the bytes must forever inhabit one storage class or layout.

### Target representation

Add an explicit correspondence from assurance-level subject IDs to stable Systems values. Conceptually:

```haskell
data AssuranceSubjectBinding = AssuranceSubjectBinding
  { assuranceSubjectId :: Text
  , assuranceSubjectOwner :: ValueId
  }
```

The verifier should derive/check the stable semantic storage/object identity from `assuranceSubjectOwner`; do not accept a free text storage ID with no owning value behind it. The identity must not be defined by the owner's current machine address, execution domain, storage class, or target representation.

Runtime operation inputs remain the observation mechanism. A digest call may consume/read `BorrowedSlice owner`, while the `RuntimeSiteClaim` binds the persistent assurance subject to `owner` and its `systemsStorageIdentity`.

If a selected execution topology transfers, migrates, stages, or converts the owner's physical representation, that change must be represented by an explicit checked correspondence/refinement showing what semantic subject survives the change. ADR-011/012 costs for transfer, synchronization, staging, or representation conversion remain attributable; equal bytes, pointer reuse, or backend convention alone do not establish subject continuity.

### Verifier requirements

- the semantic subject ID occurs in the exact selected obligation revision's `revisionSubjectIds`;
- the bound Systems value exists and is an owning/stable-identity-bearing role where required;
- the owner has a stable semantic `systemsStorageIdentity`;
- if the runtime mechanism observes through a `BorrowedSlice`, that view aliases the same owner;
- a borrowed view itself cannot be accepted as the persistent subject of the claim;
- hidden copies cannot silently change the subject while preserving only equal bytes;
- stable subject identity is not inferred from machine address, pointer equality, placement, storage class, or target layout;
- if placement or representation changes while the assurance subject is preserved, an explicit checked transfer/correspondence relation ties the pre- and post-change values to that same subject and accounts for any live obligations and attributable costs.

### Rocq target

Extend the ownership/runtime normalized models with a subject-correspondence relation: persistent claim subject -> stable semantic owner/object identity, with borrow -> owner as an observation relation. Prove that successful verification cannot bind persistent evidence to the borrow token, to an unrelated owner, or merely to a coincident backend address/representation.

The relation should permit an explicitly witnessed target transfer/representation refinement to preserve the same semantic subject without requiring the physical address, execution domain, storage class, or layout to remain unchanged.

### Adversarial tests

Reject at least:

- digest claim subject bound to `BorrowedSlice` rather than owner;
- subject bound to an owner with no stable identity;
- subject ID absent from the selected revision;
- observation view aliases a different owner;
- hidden copy used as the subject while the revision names the original object;
- correct owner/value but mismatched stable storage identity after target mutation;
- target migration/representation conversion that claims subject continuity without an explicit checked correspondence;
- pointer/address reuse accepted as proof that two target representations denote the same persistent assurance subject;
- a transfer or representation conversion whose required ADR-011/012 cost/obligation residue disappears from the lowering account.

## Cross-layer implementation order

The least disruptive order is:

1. land/finish the generic scalar SSA/dataflow work of PR #36 independently;
2. generalize Systems fact/assumption representation and `FactDisposition.v`;
3. generalize physical runtime sites and `Runtime.v`, keeping site/mechanism identity target-neutral and host-call shape target-specific;
4. add provider capability possession/use plus its normalized authority proof;
5. add stable assurance-subject binding, preferably integrated with runtime-site claims and explicitly independent of physical address/placement/representation;
6. review the generalized datatypes/verifier against ADR-012's no-single-address-space/no-universal-sequential-control/no-free-transfer constraints before freezing their content identities;
7. update Systems digests/renderers and all Phase 0 constructors/tests so current artifacts are unchanged semantically;
8. update LLVM projection/verification and `Preservation.v` only where the generalized Systems metadata crosses that boundary, keeping the one-site/one-call rule explicitly scoped to the current host ABI;
9. re-run the concrete Phase 0 LLVM certifications and keep them singleton host instances of the generalized model.

These may be rearranged if implementation dependencies demand it, but do not use Steve-specific wrappers or host-only representation assumptions to avoid touching the generic proof/model layer.

## Steve executable Systems promotion after the generalizations land

Only then add a branch-local positive `SystemsArtifact` for the control flow specified in `lowering-contract.md`.

Steve 0 deliberately selects the host/CPU execution topology. Its first positive artifact therefore has host-visible sequential CFG blocks and four host-target physical runtime mechanisms. That selection is a valid ADR-012 target instance, not a definition of generic Systems runtime-site semantics.

The first positive artifact should preserve these physical facts exactly:

- four host-target physical runtime mechanisms, not five;
- equal-byte retry performs exact byte comparison but no second SHA-256 digest;
- existing-object SHA-256 validation occurs only after witnessed byte inequality;
- `GetOk` is reachable only through digest-check acceptance;
- every failure path disposes of every owned buffer exactly once;
- BlobProvider authority is read + atomic no-replace install-if-absent, with no replace/delete capability;
- persistent digest evidence names stable semantic byte-object identity, not borrow identity, pointer/address identity, or one physical placement/layout;
- runtime primitive/execution-profile identity remains independent of both physical site identity and exact assurance claim-set identity;
- no proof/evidence wrapper is erased until Steve's assurance graph contains exact selected `ErasureUse` authority.

Then add adversarial mutations covering:

- omitted/wrong/stale assumption;
- missing one claim from a shared physical runtime site;
- duplicated physical site/cost for a second logical claim;
- evidence/revision/use identity leaking into a runtime primitive symbol;
- two distinct physical sites collapsed because they share a primitive/signature/profile;
- backend call/pointer identity substituted for generic site identity;
- widened BlobProvider authority or invented replace/delete call;
- digest subject rebound to borrowed view or wrong owner;
- subject continuity inferred from address/placement/representation without a checked correspondence;
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
- the existing Phase 0 LLVM certifications bind only their exact canonical source/target/runtime-ABI tuples, not arbitrary Phil programs and not Steve;
- the branch-local Steve assurance manifest remains a provisional semantic assurance case, not native provider implementation evidence;
- the current host/CPU sketch does not establish a generic GPU/NPU/FPGA or other heterogeneous execution model for Steve; it only requires the generic Systems abstractions not to preclude those ADR-012 target instances.

## Classification

These findings still do not require a new Steve-specific Phil ADR. They are representation/verifier generalizations required to carry already-accepted Phil decisions through the Systems boundary:

- ADR-001/002/005 define authority, ownership, loans, and per-arm resource behavior;
- ADR-006 defines opaque claims/evidence and competent runtime producers;
- ADR-007 requires property-directed Systems representations;
- ADR-010 makes assumptions/evidence/uses content-addressed and explicit;
- ADR-011 requires runtime residue and cost attribution to remain explicit;
- ADR-012 requires execution placement, data movement, synchronization, representation, and target capability to remain explicit at the Systems boundary and forbids generic assumptions of one address space, one sequential control model, or free/passive transfer.

Steve is doing its intended job here: the upload witness established the first Systems vocabulary, and the first independent program is showing exactly where that vocabulary was still upload-shaped. PR #43 is concrete evidence that the pressure test also catches cross-layer leaks early: Generalization 2 changed a runtime ABI rule before the first recognized-record implementation/certification artifact existed. ADR-012 now prevents the fix itself from hardening into a host-only definition of physical-site identity.

## Definition of done for this handoff

This handoff is satisfied when all of the following are true on `main` without Steve-specific generic code:

1. the generalized Systems IR can represent all four points above faithfully, including separation of runtime primitive/execution profile, physical Systems site, and exact assurance claim identities without defining site identity as a host call/address artifact;
2. the Haskell verifier rejects the listed generic adversarial cases;
3. Rocq proofs cover the generalized fact-assumption, runtime-site, provider-authority, and stable-subject rules with the host one-call and fixed-address cases only as specializations where selected;
4. existing Phase 0 Systems/LLVM fixtures and exact certifications remain green;
5. the generic representation satisfies ADR-012's heterogeneous-execution constraint: no required coherent address space, universal sequential control, invisible/free transfer, or canonical physical representation;
6. the Steve branch can construct one honest host/CPU positive Systems artifact with four physical runtime sites and twelve source obligation facts, and the Steve mutation suite fails closed.

At that point Steve stops being only a design pressure test at the Systems boundary and becomes the first independent application exercising the generalized property-directed lowering model.
