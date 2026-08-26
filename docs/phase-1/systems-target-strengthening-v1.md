# Phase 1 Systems target strengthening v1

Status: bounded executable conformance slice for `SYS-014`.

## Governing rule

A target or realization may require a fact stronger or more concrete than the source semantics established. Lowering may choose that representation fact, but it may not silently attribute the stronger fact to source assurance.

The bounded SYS-014 rule is:

> Every exact target precondition introduced by a lowering decision must appear in the StageContract strengthening relation, and every part not already established by exact source assurance must become an explicit derived obligation.

In the current IR, `loweringTargetPreconditions` is the explicit vocabulary for such target-introduced facts. SYS-014 therefore derives its input domain mechanically from those fields rather than asking the lowering producer to declare a second independent list.

## Relation to SYS-013

`Phil.Systems.TargetStrengthening` layers directly over the checked SYS-013 assumption-dependency stage. The SYS-013 verifier runs first.

This ordering matters. Target strengthening may eventually introduce new target assumptions, but an assumption is not a substitute for a missing obligation. SYS-014 does not manufacture assumptions from failed proof attempts or target folklore. If later realization policy admits a new assumption, SYS-013's dependency discipline ensures that the assumption cannot subsequently disappear from a live fact or mechanism.

## Exact target-precondition identity

The predecessor Systems IR already records target preconditions on exact `LoweringDecision`s. The bounded SYS-014 identity is therefore:

```text
TargetPreconditionRef {
    decision
    requirement
}
```

The decision identity and requirement text are both identity-bearing. A requirement attached to one lowering choice cannot be discharged by silently moving an obligation from another choice.

The supplied strengthening map must have exactly the mechanically derived target-precondition domain. Missing entries are silent strengthening; extra entries invent target requirements that the lower artifact did not declare.

## Source assurance is not retroactive

A strengthening relation may cite only exact source obligation revisions already attached to the same lowering decision. This is deliberately restrictive: an unrelated proof elsewhere in the source artifact cannot be cited merely because it sounds relevant.

For the current Steve pressure case, the host ABI requirement has no source obligation revision at all. Consequently it must have a derived obligation. Attempting to relabel the newly derived target obligation itself as source assurance is rejected because that revision is not present in the lowering decision's source-assurance set.

A later richer StageContract may replace this bounded relation with an explicit checked entailment/evidence relation. The invariant remains that target-specific facts are never retroactively credited to a theorem or source obligation that did not establish them.

## Derived-obligation schema

SYS-014 materializes the governing contract's bounded `DerivedObligation` shape:

```text
DerivedObligation {
    obligation_revision
    introduced_by_refs[]
    semantic_subjects[]
    proposition_or_refinement_statement
    acceptance_rule
}
```

The current disposition of the obligation is intentionally outside this slice. Stage-contract closure answers whether the obligation was created and related correctly; assurance-manifest closure later decides whether the requested build policy accepts its proof, runtime enforcement, assumption/export boundary, or other permitted disposition.

Every derived obligation has:

1. a nonempty exact revision;
2. the exact set of target preconditions that introduced it;
3. the exact union of semantic subjects named by those strengthenings;
4. a nonempty proposition/refinement statement; and
5. a nonempty acceptance rule.

The registry domain must equal the exact set of derived-obligation revisions named by the strengthening relations.

## Bidirectional agreement with the lower IR

SYS-014 does not merely add a parallel StageContract object. It checks agreement with both existing lower-IR hooks:

```text
LoweringDecision.loweringDerivedObligations
StageContract.stageDerivedObligations
```

For every lowering decision, the exact set of derived obligations named by its target-precondition relations must equal `loweringDerivedObligations`.

Across the whole artifact, the exact derived-obligation registry domain must equal `stageDerivedObligations`.

This prevents a lowering producer from writing a plausible derived-obligation record while the executable lowering ledger or predecessor StageContract tells a different story.

## Witness pressure

### Framed upload

The frozen Phase 0 upload Systems artifact has no `loweringTargetPreconditions`, and SYS-014 does not invent any. Its strengthening and derived-obligation maps are empty and verify successfully.

### Steve

Steve now exercises one conventional-host realization fact. Its provider-facing semantic byte slice is target-abstract, while the selected host realization represents that slice through a pointer/length ABI. The lowering ledger therefore records the target precondition:

```text
host BlobProvider byte-slice ABI preserves pointer/length pairing and length range
```

Source assurance does not establish that host ABI property. The lowering decision and StageContract consequently name the derived obligation:

```text
obligation.phase1.steve.host-abi.v1
```

The SYS-014 witness binds that obligation to the exact lowering decision, semantic byte-slice subject, proposition statement, and certified-release acceptance rule.

This is deliberately a small pressure case. It proves that ordinary target strengthening has somewhere explicit to go without requiring Phase 1 to solve all ABI or layout questions now.

## Conformance corpus

The dedicated corpus covers:

1. SYS-013 upload predecessor regression;
2. SYS-013 Steve predecessor regression;
3. upload with no target strengthening;
4. Steve host-ABI strengthening with an exact derived obligation;
5. omitted target-strengthening relation;
6. stronger target fact with no derived obligation;
7. attempt to relabel the target obligation as source assurance;
8. omitted derived-obligation registry entry;
9. incorrect reverse `introduced_by` relation;
10. incorrect semantic-subject relation;
11. empty derived-obligation statement;
12. empty acceptance rule;
13. disagreement between the lowering decision's derived set and the StageContract strengthening relation; and
14. deterministic stage identity under semantically irrelevant map enumeration order.

## Deterministic identity

The SYS-014 stage revision binds:

- the exact SYS-013 stage revision;
- every exact target-precondition reference;
- semantic subjects and exact source-assurance references;
- the exact derived-obligation revision for each strengthening; and
- every derived obligation's introducers, subjects, statement, and acceptance rule.

Semantically unordered maps and sets are canonicalized. Enumeration order cannot change the revision.

## Deferred

This slice intentionally does not yet implement:

- a richer general `ArchitectureRealization` target-fact schema;
- arbitrary theorem proving for source-to-target entailment;
- new target-assumption admission policy;
- final assurance disposition/manifest closure for derived obligations;
- runtime-site/claim multiplicity (`SYS-015`);
- primitive reuse across semantic sites (`SYS-016`);
- internal staging-effect accounting (`SYS-017`);
- complete target-cost accounting (`SYS-018`);
- next-stage ABI/deployment export (`SYS-019`);
- final Systems/StageContract canonical revision closure (`SYS-020`); or
- actual multi-target/heterogeneous realization.

SYS-014 establishes the prerequisite invariant for those later slices: a target may strengthen representation facts, but the semantic debt created by that strengthening must be named exactly where it is introduced.
