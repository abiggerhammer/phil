# PHIL-ASSURE-CARRIER-001 — Runtime Carrier production binding v1

This closeout binds the existing DEP-001/DEP-002 production correspondence to the exact Rocq-extracted `RuntimeCarrierKernel.hs` staged in #643.

## Exact kernel

The exact staging extraction SHA-256 is:

`803113d79bd8b0173f370bcef5997a8d6f756b62df01525bcc4cda53caa0db9f`

Production carries byte-identical copies at:

- `generated/RuntimeCarrierKernel.hs`
- `src/RuntimeCarrierKernel.hs`

The closeout workflow freshly recompiles and extracts the kernel under Rocq 9.2.0, checks the SHA-256 above, and byte-compares both checked-in copies.

## Why the final seam is compositional

Neither legacy DEP checker alone possesses every fact in Certified `ExactCarrierBinding`.

`checkRuntimeCarrierBindings` owns the selected retained assurance-use -> carrier -> exact Systems runtime-site identity, but it does not carry process/execution coverage or runtime-claim identity.

`checkRuntimeCarrierCoverage` owns process-local execution coverage and preserve/replace/discharge/end-validity transfer accounting, but it does not know which selected assurance use or verified runtime claim the carrier realizes.

The final production boundary is therefore `Phil.Systems.RuntimeCarrierCertification.verifyRuntimeCarrierCertification`. It composes:

1. `verifyManifest`, which is already production-bound to PHIL-ASSURE-EVID-001 and establishes selected RuntimeEnforced evidence, complete mechanism/residue/cost authority, and exact retained-use identity;
2. `verifyStageClosureBundle`, which recursively verifies the Systems chain and is already production-bound to PHIL-SYS-RUNTIME-GRAPH-001;
3. unchanged DEP-001 exact carrier/site binding checks;
4. DEP-002 coverage/transfer checks;
5. one explicit cross-layer witness mapping each covered target use to its selected retained assurance use and each carrier to its exact verified runtime claim; and
6. the exact extracted Runtime Carrier classifiers.

A kernel rejection after all predecessor/native checks succeeds is an internal fail-closed certification error.

## StageContract obligation reconciliation

The real framed-upload StageContract carries its RuntimeEnforced source obligations as `FactTransfer.factSourceRevision`; `stageDerivedObligations` is reserved for obligations introduced by target strengthening. DEP-002 previously admitted only the latter, which made the real source RuntimeBound carrier path impossible despite the Certified model treating `CarrierObligationId` generically.

This closeout narrows that implementation mismatch by defining the StageContract carrier-obligation domain as the union of:

- exact source revisions already named by `stageFacts`; and
- exact `stageDerivedObligations`.

No new obligation can be invented: an obligation absent from both domains still rejects. Existing DEP-002 diagnostics and ordering are retained.

## Certified exact carrier binding

For every covered target use linked to one retained assurance use, production reflects only concrete facts already checked by the composed stack:

- exact selected binding identity;
- selected retained use;
- known exact carrier;
- covered-use disposition names that same carrier;
- exact obligation identity across assurance use, target use, and carrier;
- exact runtime-site revision/evidence/cost identity;
- unique occurrence of the exact runtime site in the verified Systems artifact;
- exact carrier -> verified runtime-claim identity, with the site present in that claim and its reverse index;
- exact process identity;
- exact physical-execution coverage; and
- successful full RuntimeEnforced authority verification from `verifyManifest`.

`decideExactCarrierBindingByFacts` must accept all of those facts, and `decideCoveredCarrierUseByFacts` must then accept the covered-use accounting relation.

Explicit boundary uses are admitted only when their actual boundary identifier is nonempty and `decideExplicitBoundaryCarrierUseByFacts` accepts. Statically safe uses are theorem-trivial after the native finite enumeration.

## Transition accounting

After the unchanged DEP-002 checker accepts an active transition, production independently reflects the concrete carrier/process/obligation/execution facts into:

- `decidePreservedCarrierTransitionByFacts`;
- `decideReplacedCarrierTransitionByFacts`; or
- `decideClosedCarrierTransitionByFacts` for discharge and validity-end.

For discharge and validity-end, destination RuntimeBound absence is recomputed from the actual target-use list rather than asserted.

Duplicate target-use IDs and duplicate transition IDs are rejected at the final layer because the Certified model indexes both domains functionally.

## Preserved boundaries

This implementation refinement does not certify facts outside the theorem:

- concrete Text/Map/Set/list representation and finite enumeration remain Haskell correspondence boundaries;
- ProcessExecutionRealization truth remains its separate concurrency-realization boundary;
- runtime-site, claim, source-fact, and failure-fact construction remain verified/predecessor correspondence boundaries;
- selected provider/platform/hardware enforcement truth remains external evidence;
- detailed native diagnostic payloads remain handwritten; and
- GHC/runtime behavior and Rocq extraction correctness remain TCB assumptions.

## Closeout gate

The production workflow must:

- fresh-recompile RuntimeCarrier.v plus the #643 implementation proof and extraction under Rocq 9.2.0;
- reproduce exact kernel SHA-256 `803113d79bd8b0173f370bcef5997a8d6f756b62df01525bcc4cda53caa0db9f` and byte identity;
- build `lib:phil-core` with `-Werror`;
- strict-typecheck the kernel, final certification module, production harness, legacy DEP checkers, and predecessor witness modules;
- rerun the 18 direct extracted-kernel controls;
- run the production harness against the real Phase 0 upload assurance manifest plus the real Phase 1 upload StageClosure runtime graph;
- rerun the unchanged 9-case DEP-001 and 9-case DEP-002 corpora;
- rerun the unchanged 23-case Assurance corpus and 20-case final StageClosure corpus; and
- package exact production identities as a closeout artifact.

Only a fully green exact-head closeout permits PHIL-ASSURE-CARRIER-001 to move from `Discharged / Certified` to `Discharged / Implementation Refined`.
