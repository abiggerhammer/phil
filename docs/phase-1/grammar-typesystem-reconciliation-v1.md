# Phase 1 Grammar / Type-System Reconciliation v1

## Status

Design reconciliation for the Phase 1 canonical surface grammar. This note does not add new Core semantics. It makes Grammar v1 capable of expressing semantic commitments that were already present in the accepted Phase 0/1 Core, ADRs, and Phase 1 source/type-system contracts.

The normative concrete-syntax authority remains `grammar/phase1-surface.ebnf`.

## Why this pass exists

A comparison of the canonical Grammar v1 against the Phase 1 type-system rationale, source/declaration contract, and existing Core representation found several places where the semantic language was strictly richer than its normative concrete syntax.

That is acceptable while syntax is provisional, but it must be repaired before SURF-002 parser-production coverage and parser/grammar correspondence are used as a Phase 1 exit gate. Otherwise we would be proving correspondence to a grammar that cannot express the whole admitted Phase 1 semantic surface.

This pass resolves the identified gaps while preserving the existing competence rule:

> The grammar may expose a semantic choice, but parsing never proves that the choice is admissible.

## Reconciled forms

### 1. Refinement types

Core already admits checked refined values/types whose proposition may depend on a bound semantic value. Grammar v1 now has the canonical form:

```phil
{x : T | P}
```

The binder `x` is in scope only in `P`. Parsing establishes binder structure only. Elaboration/checking remains responsible for sort correctness, dependency restrictions, resource legality, and proof disposition.

Examples:

```phil
{x : U32 | x <= limit}
{payload : Bytes[n] | DigestMatches(id, payload)}
```

This does not introduce arbitrary type-level computation or quantifiers. It exposes the already-admitted quantifier-free dependent refinement fragment.

### 2. Explicit propositional transport

Non-definitional equality is not an implicit coercion. When a value must cross such an equality boundary, source can now state the choice explicitly:

```phil
transport value to TargetType using equality_evidence
```

The evidence expression must elaborate to evidence competent for the exact equality/transport relation required by the source and target types. The parser does not infer symmetry, transitivity, succession, subject correspondence, or proof competence.

`accept value as T` remains distinct: it asks the checker to establish ordinary admissibility/refinement at `T`; it does not name evidence for a non-definitional equality transport.

### 3. Native finite-collection relations

The built-in refinement theory already contains finite membership and disjointness predicates. Grammar v1 now exposes them as infix proposition relations:

```phil
x in xs
left disjoint right
```

They have proposition-atom precedence alongside equality/order comparisons. They are native checked predicates, not aliases for opaque claim families named `Member` or `Disjoint`.

Collection sort/element compatibility is still a semantic check.

### 4. Term-level `offer`

Grammar v1 already had `offer` in session expressions, and the Phase 0 surface/parser already had term-level external-choice handling, but `offer` was accidentally omitted from `primary_expression` in the canonical EBNF.

The canonical term form is now:

```phil
offer endpoint {
    Label(args...) => { ... }
    Other => { ... }
}
```

This is a grammar repair, not a new protocol operation.

### 5. Branch-sensitive callable residues

ADR-005/ADR-015 and the Phase 1 source contract require callable interfaces to preserve branch-sensitive success/failure resource outcomes. A flat `outcomes { ... };` declaration alone cannot state the post-state for each outcome.

Grammar v1 therefore now permits outcome residue blocks inside callable contracts:

```phil
callable Store(x : OwnedBytes[n]) -> Result {
    outcomes { Stored, StoreFailure };

    outcome Stored {
        state (id : ContentId);
        callee preserve;
        ensures StoredAt(id);
    }

    outcome StoreFailure {
        state (x : OwnedBytes[n]);
        callee preserve;
    }
}
```

The `state (...)` telescope describes the explicit post-outcome resource/value slots exposed by that branch. The semantic checker determines exact structural mode, subject continuity/succession, and whether those slots satisfy the governing resource contract.

An `outcome T { ... }` block does not silently add `T` to the public outcome set. It must correspond to an outcome admitted by the stabilized callable interface. Missing, duplicate, or conflicting branch facts are semantic errors.

Global callable clauses remain useful when one fact applies uniformly to every outcome. Outcome-local facts are used when the semantic contract is branch-sensitive; conflicting global and outcome-local claims must reject rather than acquire an implementation-order meaning.

### 6. Exact `ReplaceCallee` successor surface

The Core callee transition `ReplaceCallee` identifies an exact successor callable interface and, where applicable, successor state. Bare syntax such as `callee replace;` cannot express that commitment.

Grammar v1 now spells replacement as:

```phil
callee replace with NextCallable[args...] state next_state;
```

The `state ...` suffix is optional when the successor callable contract has no explicit state index or the exact state is otherwise not part of the transition.

`preserve` and `consume` remain parameterless:

```phil
callee preserve;
callee consume;
```

The same callee-transition syntax is available in an outcome residue block, allowing different legal callable ownership transitions on different public outcomes when the contract actually declares them.

## Things deliberately not added

This pass does **not** add surface annotations for unrestricted/affine/linear structural mode. Phase 1 already commits to deriving mode from owned contents and declared contracts where the result is deterministic.

It does **not** add explicit `toNat` source syntax merely because Core has a refinement-term coercion node. Canonical lossless coercion insertion remains an elaboration/focusing responsibility where the target sort uniquely determines it.

It does **not** add special syntax for finite-sequence/set/stable-identity runtime types. Those can remain ordinary declared/prelude types while their refinement-visible sorts are established by elaboration.

It does **not** add user-written quantifiers, algebraic effect handlers, general subtyping/coercion syntax, unrestricted existentials, or arbitrary type-level computation.

It does **not** claim that the current Haskell parser implements these forms. That is intentionally left to SURF-002 through SURF-006 and the canonical front-end tranche.

## Conformance impact

SURF-002 positive Grammar-v1 production coverage must include at least:

- a refinement type whose proposition uses its binder;
- explicit transport with a named equality-evidence expression;
- membership and disjointness propositions;
- term-level `offer`;
- a callable with outcome-specific state/residue clauses; and
- a `replace` callee transition naming its exact successor contract/state.

SURF-003 malformed-syntax coverage should include incomplete refinement/transport/outcome-residue forms.

SURF-004 lexical-priority coverage automatically gains the new literal keywords introduced by the canonical EBNF.

SURF-005 determinate-interpretation analysis must cover the new brace-delimited refinement and outcome forms and the relation operators, rather than relying on parser alternative order.

Semantic conformance remains owned by the corresponding Core/resource/callable/refinement cases; grammar tests establish syntax only.

## Exit condition for this reconciliation slice

This reconciliation slice is complete when:

1. `grammar/phase1-surface.ebnf` contains the forms above;
2. the mechanically derived proof-facing grammar remains deterministic and warning-clean;
3. the Phase 1 surface-grammar documentation records the forms and their competence boundaries; and
4. no claim is made that the old Phase 0 Haskell parser already implements the revised Grammar v1.
