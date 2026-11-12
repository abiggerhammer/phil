# Record/data optional generic-requirements recursive grouping v1

PHIL-SURFACE-GRAMMAR-CORR-001 G3 continuation after merged #1749.

This bounded declaration lift replaces only the optional `generic_requirements`
carrier in `record_decl` and `data_decl` with the recursively-grouped
thirteen-way values already proved by #1586 and #1749. It retains existing
identifiers, generic parameters, structural mode, record-field bodies, data
variant head/suffix bodies, branch/shell structure, and exact whole-tree erasure.

The source/spine round trips and declaration-level canonical-`Derives`
totalities have no caller-supplied fuel or child-success premises. Examples
distinguish missing requirements from present-empty `requires {}` and
check unchanged data declaration erasure. Strict warning compilation, closed
assumption checks, full recursive checker endpoints, and source/object
identity inventory are extended in the source-spine workflow.

**Boundary:** No production AST binding, implementation-representation
consumer, command/failure-target body refinement, static-reference or
named-postfix interior refinement, G2/G4 closure, or Phase 1 closure is claimed.
The Logic Ledger remains unchanged.
