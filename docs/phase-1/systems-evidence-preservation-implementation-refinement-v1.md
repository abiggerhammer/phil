# Systems evidence preservation implementation refinement v1

`PHIL-SYS-EVID-001` is already Certified. This tranche stages only its representation-neutral executable decision surface; production behavior remains unchanged.

## Existing predecessor binding

SYS-011 subject transfer is not duplicated here. `Phil.Systems.EvidenceSubjectTransfer` already routes the exact copy/byte-equality/transfer-law/evidence-reference/validity-scope semantic gates through the production-bound `BoundarySubjectKernel`, which implements the Certified `PHIL-BND-SUBJECT-001` predecessor used by `SystemsEvidencePreservation.v`.

This staging slice therefore extracts only the semantic suffix owned by `PHIL-SYS-EVID-001` itself:

- SYS-012 evidence erasure after accepted Assurance use and complete later-consumer closure;
- SYS-013 exact assumption registry/authority/scope/forward/reverse preservation; and
- cumulative SYS-011--013 acceptance over an already-accepted subject-transfer predecessor.

## Extracted SYS-012 decision

`decideEvidenceErasureByFacts` owns the ordered representation-neutral gates for:

1. accepted exact Assurance erasure use;
2. exact source-fact subject binding;
3. exact discharge-evidence subject binding;
4. nonempty erased-representation identity;
5. explicit last semantic use;
6. explicit no-later-consumer basis;
7. well-formed optional successor-invariant revision;
8. well-formed optional runtime-residue-change revision;
9. well-formed optional cost-change revision; and
10. complete closure of every modeled later semantic consumer.

The correspondence theorem reflects those Boolean facts back to the exact fields of Certified `EvidenceErasurePreserved` under explicit reflection hypotheses. The concrete checker may continue to enumerate consumers and recover exact diagnostics natively.

## Extracted SYS-013 decision

`decideAssumptionDependencyByFacts` owns the ordered semantic gates for:

1. exact required-assumption/registry correspondence;
2. Certified assumption authority for every registered assumption;
3. nonempty validity scopes;
4. exact forward dependencies;
5. exact registered scope on every forward edge; and
6. exact reverse dependencies.

The concrete `Map`/`Set` domain construction and diagnostic payloads remain native. Assumption authority is an explicit predecessor/evidence fact from Certified `PHIL-ASSURE-ASSUME-001`; this layer does not invent a second authority verifier.

## Cumulative decision

`decideSystemsEvidenceByFacts` composes three facts in Certified predecessor order:

1. SYS-011 subject transfer accepted;
2. SYS-012 erasure accepted; and
3. SYS-013 assumption dependencies accepted.

The correspondence theorem reflects cumulative acceptance to `SystemsEvidencePreserved` when the three input Booleans reflect the exact Certified subrelations.

## Explicit native / evidence boundary

This staging tranche does not claim Rocq ownership of:

- concrete `Text`, key, revision, `Map`, `Set`, or list representation/equality/enumeration;
- source-fact, semantic-subject, later-consumer, or assumption-map derivation/completeness;
- exact diagnostic precedence or payload construction;
- stage-revision construction or canonical serialization;
- truth/competence of selected evidence beyond the already-Certified Assurance verifier gates;
- runtime/backend behavior; or
- Rocq/GHC/extraction/toolchain correctness.

Those remain explicit implementation-correspondence, evidence, or TCB boundaries.

## Staging validation

The registered `Phase 1 Systems Evidence Proofs` workflow is extended additively to:

- recompile the Certified predecessor/proof chain plus implementation correspondence;
- fresh-extract `SystemsEvidencePreservationKernel.hs` under Rocq 9.2;
- strict-typecheck and execute 22 direct extracted-kernel controls;
- strict-typecheck unchanged SYS-011--013 production modules;
- rerun the unchanged 36-case SYS-011--013 correspondence corpus; and
- record exact proof, extraction, production, test, harness, and staging-document identities.

A green staging run is mechanized implementation-correspondence evidence only. Production remains unchanged, so `PHIL-SYS-EVID-001` stays `Discharged / Certified` until a separate exact-kernel production-binding closeout lands.
