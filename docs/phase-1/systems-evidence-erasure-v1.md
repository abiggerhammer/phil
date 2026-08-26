# Phase 1 Systems evidence erasure v1

Status: bounded executable conformance slice for `SYS-012`.

## Governing rule

Proof terms, typestate wrappers, validation markers, dynamic checks, and other assurance representations may disappear only after the relevant semantic responsibility has been discharged and the StageContract can account for every semantic consequence that remains live.

Erasure therefore requires more than a lowering decision saying that a proof value is unused.  The bounded SYS-012 relation records:

1. the exact source fact being discharged;
2. the exact stable semantic subject to which that fact applies;
3. the exact representation being erased;
4. one or more accepted discharge-evidence references on that exact subject;
5. the exact last semantic use of the erased representation;
6. an explicit no-later-consumer basis;
7. an exact successor invariant/control fact when a later semantic consumer remains; and
8. explicit runtime-residue and cost-change revisions when those categories change.

The governing distinction is:

```text
representation no longer needed
    !=
semantic responsibility no longer live
```

A backend optimizer, zero-sized proof object, dead SSA value, or convention that proof terms erase does not establish the right-hand side.

## Relation to existing erasure machinery

The frozen Systems IR already contains `OpEraseFact`, `FactErased`, lowering action `Erase`, assurance uses, and checks that an erase decision is tied to selected evidence/use data.  Those checks are necessary but not sufficient for SYS-012: they do not by themselves establish that the erased representation has reached its last semantic use or that no later consumer silently depends on it.

`Phil.Systems.EvidenceErasure` adds that semantic-consumer closure above the checked SYS-011 evidence/subject layer.  The SYS-011 verifier therefore runs first, so an erasure cannot repair an invalid subject transfer.

## Exact subject and source fact

Each `ErasureJustification` names one exact `SourceFactKey` and one exact `SourceSubjectKey`.

For this bounded slice, the source fact identifier must also occur in the exact subject correspondence's evidence-reference set.  This makes the evidence subject mechanically checkable and prevents an erasure justification from borrowing an identically named or otherwise unrelated fact from another semantic subject.

The source fact must also occur in the underlying generic Phase-1 StageContract source-fact set.  SYS-012 therefore refines an existing cross-stage responsibility rather than inventing a new fact at the erasure layer.

## Accepted discharge evidence

`erasureDischargeEvidenceRefs` is nonempty.  Every named discharge evidence reference must belong to the exact semantic subject selected by the erasure justification.

This bounded rule intentionally uses the already checked subject/evidence registry rather than introducing another evidence namespace.  Later assurance layers may admit richer proof objects, but they must preserve the same exact-subject discipline.

An empty discharge set is the direct `SYS-012` negative case.

## Last semantic use and later consumers

The erasure justification names an exact `SemanticUseKey` for the last semantic use of the erased representation and a nonempty `NoLaterConsumerRevision` identifying the checked consumer-closure basis.

The bundle also records every modeled semantic consumer after the proposed erasure that remains relevant to an erased fact.  A later consumer has only two accepted semantic shapes:

```text
ConsumerNeedsErasedRepresentation
ConsumerUsesSuccessorInvariant exact_revision
```

The first shape is always a rejection.  It demonstrates that the proof/check/typestate representation is still semantically live even if a backend data-flow pass would otherwise delete it.

The second shape is accepted only when the erasure justification itself names exactly the same successor invariant/control-fact revision.  A missing or merely similar successor invariant is rejected.

Thus a live consequence may survive representation erasure, but its new carrier remains explicit.

## Witness pressure

### Framed upload

The upload fixture treats `payload.exact_receive` on `upload.payload.server` as the exact semantic fact whose receive-validation marker is proposed for erasure.

The negative fixture removes the discharge evidence and is rejected.  The positive fixture supplies exact `payload.exact_receive` discharge evidence and an explicit consumer-closure basis.

This fixture exercises the StageContract erasure relation; it does not change the frozen Phase-0 upload executable artifact.

### Steve

The Steve fixture treats `steve.digest.stable-subject` on `steve.bytes.candidate` as the exact semantic fact whose proof marker is proposed for erasure.

The corpus exercises:

- missing discharge evidence;
- accepted erasure after exact discharge;
- a later consumer that still needs the erased representation;
- a later consumer carried by an exact successor invariant; and
- rejection when the later consumer cites the wrong successor invariant.

A second Steve fact is used only to pressure deterministic stage identity under map ordering.

## Runtime residue and cost

SYS-012 records optional exact runtime-residue and erasure-cost change revisions because proof erasure is not permission to erase runtime or cost accounting.

This slice checks that a supplied revision is nonempty and identity-bearing.  Full quantitative cost attribution remains a later Systems tranche, as do carrier-site multiplicity and complete runtime-enforcement coverage.

## Conformance corpus

The dedicated corpus covers:

1. SYS-011 predecessor regression;
2. upload erasure without discharge rejection;
3. Steve erasure without discharge rejection;
4. accepted exact upload erasure after discharge;
5. accepted exact Steve erasure after discharge;
6. rejection of a later consumer that still needs the erased representation;
7. acceptance when an exact successor invariant carries the live consequence;
8. rejection of a mismatched successor invariant;
9. rejection of discharge evidence belonging to another semantic subject;
10. rejection when the source fact is not evidence for the exact semantic subject;
11. rejection of an empty no-later-consumer basis; and
12. deterministic erasure-stage identity under map ordering.

## Deterministic identity

The SYS-012 stage revision binds:

- the exact SYS-011 evidence-transfer stage revision;
- the exact set of erasure justifications; and
- the exact set of modeled later semantic consumers.

Semantically unordered maps and evidence sets are canonicalized before identity derivation.  Enumeration order therefore cannot change the stage revision.

## Deferred

This slice intentionally does not yet implement:

- assumption-dependency laundering rejection (`SYS-013`);
- target strengthening and derived realization obligations (`SYS-014`);
- runtime-site/carrier many-to-many relations;
- full staging-copy authority/failure/subject-transfer/cost accounting;
- next-stage ABI requirements;
- arbitrary consumer-graph synthesis from optimized backend IR; or
- final compact semantic digests.

SYS-013 should build directly on this relation: erasure may remove a representation, but it may not erase the assumptions or validity scopes on which its discharge evidence depends.
