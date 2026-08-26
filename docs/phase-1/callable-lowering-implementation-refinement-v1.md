# CALL-016 implementation refinement v1

`PHIL-CALL-LOWER-IMPL-001` mechanically links the CALL-016 StageContract checker to its certified semantics.

The executable kernel owns the ordered decision over sixteen exact semantic/accounting coordinates: contract revision, machine shape, callable occurrence, structural mode, captures, callee transition, caller authority, internal authority, effect bound, failure surface, live loans, and the five target-introduced accounting categories (effects, failures, assumptions, carriers, cost). Target representation choice and representation identity do not occur in the projection.

This migration intentionally fixes one gap exposed by implementation refinement: the existing Haskell `SourceCallableLoweringFacts` / `TargetCallableLoweringFacts` do not yet carry machine shape even though the certified Rocq CALL-016 model bundles machine shape into its callable surface equality. Therefore this first tranche extracts and typechecks the correct sixteen-coordinate kernel but does not yet bind it to production.

The final production-binding commit must add exact source/target machine-shape fields and a mismatch diagnostic, project all sixteen equality facts into the extracted kernel, require byte-identical regeneration, and route acceptance through that kernel. Only after that strengthened checker is green may CALL-016 become `Implementation Refined`.

Rocq proves the extracted decision accepts exactly when all sixteen coordinates hold, and proves accepted production decisions refine the existing `CallableLoweringAccepts` relation given the concrete exact-equality bridge. Native equality for the concrete Haskell semantic values remains a named primitive TCB component; representation coincidence is never an acceptance input.
