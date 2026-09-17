# PHIL-EXEC-ORDER-001 proof boundary

This note records the mechanized boundary for deterministic local Phil execution order and checked target reordering.

The proof is intentionally split along the same authority boundaries as the implementation.

## Source-local authority

`Phil.Surface.GrammarV1.SequentialExecution` owns the canonical bounded local source trace for Grammar-v1. The Rocq model captures the semantic invariants that matter across representation changes:

- sequential statements contribute their traces in source order;
- once local control stops, no suffix statement contributes source events;
- strict child expressions contribute left-to-right, and a stopping child suppresses later children;
- a condition or scrutinee contributes its events before the selected branch;
- only the selected branch contributes local source events; an untaken arm is nonsemantic to that execution trace; and
- general loop iteration remains outside this bounded local walker unless the separate loop authority supplies it.

Concrete AST constructors, `Located` occurrence identity, branch-choice evidence lookup, terminal-evidence lookup, and the exact Haskell traversal implementation remain correspondence boundaries.

## Omitted `else`

EXEC-015 is modeled separately because an omitted `else` is not an absent predecessor. Its false branch is exactly one continuing Unit-valued identity predecessor carrying the incoming resource, evidence, and obligation state unchanged into ordinary join checking.

The proof certifies that exact false-predecessor identity. It does not replace the existing Core resource join: affine weakening and rejection of incompatible linear/unrestricted/evidence/obligation states remain owned by that already-checked join boundary.

## Target reordering

Physical target instruction order is not source semantic identity. `Phil.Systems.SequentialTrace` binds an ordered source projection to an exact StageContract/source artifact/target artifact identity.

A changed target projection is admissible only when:

- source and target event domains match exactly;
- the exact trace relation is recorded in the StageContract;
- every changed crossing has explicit nonempty commuting evidence recorded in that StageContract; and
- the other StageContract effect/resource/failure/authority/observable preservation relations remain valid.

An unproved swap therefore fails closed. Adding an untaken/speculative source-visible event also fails closed as event-domain drift.

The Rocq proof treats the broader StageContract semantic-preservation fact as an imported authority rather than reimplementing all StageContract relations inside the order theorem.

## Representation and TCB boundaries

The following remain explicit boundaries rather than theorem claims:

- Haskell `Text`, `Digest`, `Set`, sorting and finite-list traversal;
- canonical rendering of trace and commutation relations;
- concrete source/target artifact digest construction;
- the adjacent-crossing search used by `checkSequentialTraceRefinement`;
- source-to-checked Grammar-v1 elaboration correctness;
- StageContract construction and serialization correctness;
- GHC/runtime correctness and Rocq/toolchain correctness; and
- target execution correctness outside the checked source-observable refinement relation.

The theorem therefore certifies the source-order and refinement contract without claiming that physical target instruction order must literally equal source order.
