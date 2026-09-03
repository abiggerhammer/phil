# Runtime Carrier implementation refinement v1

`PHIL-ASSURE-CARRIER-001` is Certified by `proof/Phil/Assurance/RuntimeCarrier.v`. This staging slice adds a representation-neutral executable correspondence layer without changing the production DEP-001 or DEP-002 Haskell checkers.

## Extracted decision surface

`proof/Phil/Assurance/RuntimeCarrierImplementation.v` proves executable Boolean classifiers equivalent to the exact Certified predicates for:

- retained RuntimeEnforced use → exact carrier → exact Systems runtime-site binding, including selected revision/evidence/cost, establishment site, claim lineage, ProcessKey, physical execution coverage, and complete RuntimeEnforced authority;
- covered-use acceptance only with an exact carrier binding;
- explicit-boundary acceptance only with a nonzero/nonempty boundary witness;
- preserved carrier transitions with exact obligation/process/from/to coverage;
- replacement transitions with exact prior/next carrier, obligation, process, and execution lineage;
- discharge and end-validity transitions only when the source carrier is exact and the destination is no longer RuntimeBound.

The extraction driver emits `RuntimeCarrierKernel.hs`. Staging tests call these extracted functions directly and rerun the unchanged DEP-001 and DEP-002 corpora.

## Native correspondence boundaries retained

The following remain deliberately native and are not silently promoted into the extracted kernel:

- `Text`, `Map`, `Set`, list, `ProcessKey`, physical-execution-key, revision/evidence/cost representation and equality;
- enumeration of selected retained RuntimeEnforced uses and potentially violating target uses;
- exact Map-domain, map-key, StageContract-derived-obligation, process-realization, runtime-site occurrence/cardinality, and failure-fact lookup;
- construction of runtime mechanisms and truth/soundness of the underlying hardware/runtime enforcement;
- profile-policy admission of RuntimeBound closure;
- failure-fact kind/process attribution and detailed typed diagnostic ordering/payloads;
- concrete correspondence from Haskell empty text to the proof model's nonzero explicit-boundary witness;
- scheduler/device/platform behavior and provider/profile evidence truth;
- GHC/runtime behavior and Rocq extraction correctness.

A green staging PR does **not** promote the obligation above `Discharged / Certified`. Production binding must check in the exact extracted kernel and route the successful DEP-001/DEP-002 semantic decisions through it before the ledger can be promoted to `Implementation Refined`.
