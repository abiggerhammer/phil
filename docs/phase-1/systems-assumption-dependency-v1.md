# Phase 1 Systems assumption dependency v1

Status: bounded executable conformance slice for `SYS-013`.

## Governing rule

An assumption is a named semantic dependency, not a comment that may disappear when a fact is lowered or an assurance representation is erased.

For every source fact, semantically significant Systems mechanism, or erasure that inherits assumption `A`, the StageContract must retain:

1. the exact identity of `A`;
2. one explicit validity-scope revision for `A`;
3. the forward relation from the consumer to `A`; and
4. the reverse relation from `A` back to that exact consumer.

The bounded invariant is therefore:

```text
consumer -> assumption@scope
assumption -> exact consumers
```

Both directions must agree exactly. A fact cannot remain meaningful "under assumption A" while its disposition drops `A`, and an erasure cannot make the assumption dependencies of its discharge disappear.

## Relation to SYS-012

`Phil.Systems.AssumptionDependency` layers directly over the checked SYS-012 evidence-erasure stage. The SYS-012 verifier runs first.

The predecessor already establishes exact source facts, exact semantic subjects, exact evidence transfer, exact discharge evidence, last semantic use, and successor-carriage rules. SYS-013 adds the missing dependency graph: representation erasure may remove a proof/check/typestate carrier, but not the assumptions under which its semantic discharge is valid.

## Inherited dependencies

The bounded checker derives required assumptions only from explicit lower-stage relations:

- `Phase1FactAssumptionDependent` wrappers on source-fact dispositions;
- `systemsJustificationAssumptionRefs` on target mechanisms; and
- for each erasure, the assumptions inherited by the exact source fact being erased.

It does not search ambient configuration or invent assumptions to repair an incomplete StageContract.

This is deliberately important: SYS-013 checks preservation of already explicit semantic dependencies. Deciding whether a new target fact requires a new assumption belongs to realization/strengthening policy, not to this checker.

## Assumption registry and validity scope

Every inherited assumption appears exactly once in the SYS-013 assumption registry. Each registry entry binds:

```text
StageAssumptionKey
AssumptionValidityScopeRevision
```

The scope revision is identity-bearing and nonempty. Every forward consumer edge must carry exactly the registry scope for that assumption. A consumer cannot silently widen, narrow, replace, or forget the scope by reusing only the assumption name.

The registry domain must equal the exact inherited-assumption set. Missing entries are laundering; extra entries are undeclared/invented assumption dependencies.

Phase 1 may later replace the bounded scope revision with a richer canonical `ValidityScope` object while preserving this identity and equality discipline.

## Forward dependency relation

The checker derives the exact set of assumption-bearing consumers from the verified lower stage. The supplied forward map must have exactly that domain.

For each consumer, the assumption-key set must equal the inherited set and every edge must carry the exact registered validity-scope revision.

This catches three distinct failures:

- a fact disposition drops an assumption;
- a target mechanism's reverse justification drops an assumption; or
- an erasure records successful discharge but drops an assumption on which the discharged fact still depends.

## Reverse dependency relation

The reverse relation is not optional audit metadata. It is recomputed from the required forward dependency graph and compared exactly with the supplied reverse map.

For each assumption, the reverse set identifies every fact, mechanism, and erasure that still depends on it. Omitting one consumer is a verification failure even if the consumer's own forward edge is present.

This gives StageContract the inspection property required by the governing specification:

```text
for a consumer: which assumptions does it depend on?
for an assumption: which consumers depend on it?
```

## Witness pressure

### Framed upload

The current generic Phase-1 upload accounting carries no `Phase1FactAssumptionDependent` or mechanism-assumption references, so the SYS-013 registry and dependency maps are empty and verify successfully. The legacy Phase-0 StageContract prose assumption is not promoted automatically into a Phase-1 semantic dependency; ambient prose is not an exact dependency edge.

### Steve

Steve's provider qualification path explicitly propagates four assumptions into its Phase-1 fact dispositions and Systems justifications. The SYS-013 witness therefore exercises a nontrivial graph in which:

- every affected source fact retains the assumption set;
- every affected Systems mechanism retains the assumption set;
- the SYS-012 digest-proof erasure inherits the source fact's assumptions;
- all consumers use exact assumption validity-scope revisions; and
- every assumption has the exact reverse consumer set.

## Conformance corpus

The dedicated corpus covers:

1. SYS-012 upload predecessor regression;
2. SYS-012 Steve predecessor regression;
3. upload with no inherited assumptions;
4. complete Steve bidirectional assumption lineage;
5. missing assumption on a source-fact disposition;
6. missing assumption on a Systems mechanism justification;
7. missing assumption on an erasure;
8. mismatched validity scope on a consumer edge;
9. missing reverse consumer;
10. missing inherited assumption in the registry;
11. invented assumption in the registry;
12. empty assumption validity scope; and
13. deterministic dependency-stage identity under map/set reordering.

## Deterministic identity

The SYS-013 revision binds:

- the exact SYS-012 stage revision;
- assumption registry keys and validity-scope revisions;
- the complete forward consumer dependency graph; and
- the complete reverse dependency graph.

Semantically unordered maps and sets are canonicalized, so enumeration order cannot change the stage identity.

## Deferred

This slice intentionally does not yet implement:

- target strengthening and derived obligations (`SYS-014`);
- creation/admission policy for new target assumptions;
- final integration with a richer assurance-ledger `Assumption` node format;
- runtime carrier many-to-many relations;
- full staging/cost accounting;
- next-stage ABI/deployment requirements; or
- final compact semantic digests.

SYS-014 can now rely on an important invariant: if strengthening or realization introduces a dependency on an assumption, that dependency cannot subsequently disappear while the strengthened fact or mechanism remains live.
