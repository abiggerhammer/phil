# PHIL-CALL-INVOKE-001 proof boundary

This slice certifies the Phase-1 CALL-019 ordinary callable-invocation
composition boundary.

## Certified semantic composition

An accepted ordinary callable invocation must satisfy all of these independent
conditions:

- ordinary Surface checking has accepted the invocation's argument/result shape
  and structural transfer;
- the invocation resolves to one exact callable DeclarationKey;
- an exact semantic callable contract exists for that same declaration
  identity;
- the operation remains in the ordinary callable namespace rather than falling
  back to provider-primitive or host-language dispatch;
- every required callable authority is backed by an exact checked possessed
  capability;
- callable substitutability obeys the already-Certified refinement relation:
  authority may not strengthen, effects may not widen, failures may not widen,
  and callee transition is exact;
- reachable invocation effects fit the enclosing callable's public effect bound;
- reachable modeled failures fit the enclosing callable's public failure bound;
- branch-sensitive invocations have exact outcome-class-domain coverage;
- every admitted branch preserves the exact outcome state, callee transition,
  postconditions, residual obligations, assumptions, effects, and discharged
  facts certified by PHIL-CALL-OUTCOME-001;
- caller control remains exact:
  success and typed-negative branches continue, declared-terminal branches
  terminate with their exact outcome identity, and declared-fatal branches
  terminate fatally with their exact outcome identity;
- declared fatal control is not represented as generic failure or ordinary
  declared closure;
- residual-obligation bindings and caller-visible branch resource residue remain
  exact; and
- Preserve/Consume/Replace callee lifecycle is justified by exact concrete
  occurrence-state evidence and the Certified PHIL-CALL-LIFE-001 semantics.

## Certified predecessors

The aggregate composes existing authorities rather than redefining them:

- PHIL-CALL-MODE-001
- PHIL-CALL-EFFECT-001
- PHIL-CALL-LIFE-001
- PHIL-CALL-REFINE-001
- PHIL-CALL-OUTCOME-001
- PHIL-AUTH-POSSESS-001

PR #1156 closed the former CALL-019 blocker by adding an exact neutral
`CallableOutcomeFatals Outcome` caller-control carrier. Compiler continuation
state preserves that as a distinct fatal disposition rather than coercing it to
generic `Failed` or ordinary declared-terminal closure.

## Production correspondence

The production path remains:

- `Phil.Surface.Check` for ordinary invoke lookup, arity/type/mode checking,
  outcome-label uniqueness, residual-obligation arity, and continuing branch
  resource-domain checks;
- `Phil.Compiler.CallableSurfaceSemantics` for exact DeclarationKey-to-semantic
  contract binding;
- `Phil.Compiler.CallableInvocationSemantics` for caller-visible semantic
  account projection;
- `Phil.Compiler.CallableAuthorityPossession` for possession-backed authority;
- `Phil.Compiler.CallableInvocationContext` for authority/effect/failure,
  branch-domain, exact contract/control, and lifecycle-aware admission;
- `Phil.Compiler.CallableOutcomeDispatch`,
  `CallableOutcomeBranchSemantics`, and `CallableOutcomeContinuation` for exact
  branch/control correspondence;
- branch fact/resource/residue modules for exact per-arm state; and
- `Phil.Compiler.CallableInvocationLifecycle` for exact concrete
  Preserve/Consume/Replace occurrence-state transitions.

The dedicated workflow replays the complete focused CALL-019 regression family.

## Explicit boundaries / TCB

Still explicit:

- concrete Text, SourceSpan, DeclarationKey, Outcome, Map/Set/list
  representation and finite traversal;
- parser and source-elaboration correspondence;
- construction/truth of semantic callable contracts and possessed capabilities;
- source expression evaluation order outside the already-checked CALL-019
  occurrence sequence;
- detailed Haskell diagnostic ordering/payload construction;
- backend closure conversion, ABI realization, and runtime enforcement;
- GHC/runtime correctness; and
- Rocq/toolchain correctness.

Provider primitive lookup remains a separate namespace and competence path.
Dynamic dispatch beyond the admitted callable model is not introduced by this
proof.
