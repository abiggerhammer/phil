# Phase 1 Systems runtime claim binding v1

Status: bounded executable conformance slice for `SYS-015`.

## Governing rule

Runtime assurance is not one-site/one-claim by construction.

A conforming StageContract must permit both:

```text
one runtime site -> several exact claims
one exact claim  -> several cooperating runtime sites
```

without collapsing claim identity into site identity and without charging one physical site once per claim that cites it.

The bounded SYS-015 rule is therefore:

> Every modeled runtime site has at least one exact claim binding; every claim names the exact set of sites that jointly support it; the reverse site-to-claim relation agrees exactly; and physical cost identity remains site-owned even when several claims reference it.

## Relation to SYS-014

`Phil.Systems.RuntimeClaimBinding` layers directly over the checked SYS-014 target-strengthening stage. The SYS-014 verifier runs first.

This matters because a runtime claim cannot repair a missing target-strengthening obligation. SYS-015 only accounts for which already-modeled runtime sites participate in which exact claims. Whether the claim is adequately discharged by static evidence, runtime enforcement, ADR-017 carriers, assumptions, exports, or later deployment qualification remains a separate assurance-closure question.

## Exact runtime-site occurrence identity

The existing Systems IR stores a `RuntimeSiteRef` on runtime-bearing operations and terminators, but a reusable site descriptor alone is not an occurrence identity. SYS-015 therefore derives one exact logical occurrence key from the verified Systems graph:

```text
RuntimeSiteKey {
    function
    block
    slot = operation(index) | terminator
}
```

The derived `RuntimeSiteBinding` also retains the exact existing `RuntimeSiteRef`:

```text
kind
obligation revision
evidence entry
cost ref
```

The supplied site registry must equal this mechanically derived registry exactly. A site cannot be invented, moved, or retargeted merely by reusing an equal runtime descriptor.

## Claim identity and source basis

A `RuntimeClaim` has its own exact revision, distinct from runtime-site identity. It records:

```text
RuntimeClaim {
    claim_revision
    source_obligation_revisions[]
    source_fact_refs[]
    semantic_subjects[]
}
```

For this bounded slice, the exact source obligations of a claim must equal the set of native obligation revisions carried by its bound runtime sites. The source-fact set is then derived from the predecessor StageContract's exact fact revisions and compared exactly with the supplied claim.

This prevents a multi-site claim from silently dropping one site's obligation, and prevents a site from being cited for an unrelated source obligation merely because the runtime primitive looks useful.

Semantic subject refinement remains governed by the already-landed SYS-004/SYS-011 subject-correlation and transfer layers; SYS-015 preserves subject references without replacing those competence boundaries.

## Bidirectional site/claim relation

The forward relation is explicit:

```text
claim -> exact runtime sites
```

The reverse relation is independently materialized and checked:

```text
runtime site -> exact claims
```

The reverse map is recomputed from the forward claim bindings and compared exactly. Every modeled runtime site must occur in that relation with at least one claim.

Consequently:

- one site may appear in several forward claim bindings;
- one claim may contain several site keys;
- omitting one site from a composite claim is a StageContract failure;
- omitting one claim from a site's reverse set is a StageContract failure; and
- a runtime site with no claim is a StageContract closure failure.

No one-to-one cardinality assumption is present in the representation.

## Physical cost identity is not claim identity

SYS-015 introduces only the minimum cost structure required by its governing case. Every exact runtime site receives one deterministic `PhysicalRuntimeCostIdentity`, derived from:

```text
runtime site occurrence + existing runtime cost ref
```

The stage contains one site-indexed physical-cost registry entry per runtime site.

A `RuntimeClaimBinding` may reference the cost identities of all sites supporting that claim, but those are references to shared physical cost identities. Claims do not own cost entries. Thus two claims sharing one runtime site both point to the same physical cost identity while the registry still contains one physical entry.

This is intentionally weaker than the complete ADR-011 cost-attribution model. SYS-018 will decide how shared primitives, transfers, staging, synchronization, and other physical mechanisms are charged and aggregated. SYS-015 establishes the prerequisite identity discipline: claim multiplicity alone cannot multiply physical work.

## Witness pressure

### Framed upload

The upload witness already contains several exact `RuntimeSiteRef` occurrences. SYS-015 derives native one-obligation claims for all of them, then adds one composite claim:

```text
claim.phase1.upload.payload-integrity-chain.v1
```

The composite claim is supported jointly by the exact payload `ExactReceiveBoundary` site and the exact `DigestBoundary` site.

This one witness exercises both cardinalities:

```text
payload-integrity claim -> receive site + digest site

digest site -> native digest claim + payload-integrity claim
receive site -> native receive claim + payload-integrity claim
```

The composite claim's source obligations and source facts are derived from those exact site revisions. Its physical cost set contains the two existing site-owned cost identities; it creates no new per-claim charges.

### Steve

Steve's current bounded Systems witness has no `RuntimeSiteRef` occurrences. It therefore traverses the exact same SYS-015 schema with empty site/claim/cost relations and verifies successfully. SYS-015 does not invent runtime assurance machinery merely to make both witnesses nonempty.

Later Steve runtime-enforcement/carrier work may populate this relation without changing the cardinality or identity rules established here.

## Conformance corpus

The dedicated corpus covers:

1. SYS-014 upload predecessor regression;
2. SYS-014 Steve predecessor regression;
3. positive upload many-to-many closure;
4. positive Steve empty closure;
5. one claim bound to several sites;
6. one site supporting several claims;
7. omission of one site from a multi-site claim;
8. an unclaimed modeled runtime site;
9. reverse site-to-claim omission;
10. claim-local invented/duplicated cost identity;
11. physical cost registry omission;
12. duplicate physical cost alias for one site;
13. claim reference to an unknown site;
14. source-fact basis mismatch;
15. source-obligation/site mismatch;
16. tampered site registry versus the exact Systems graph; and
17. deterministic stage identity under semantically irrelevant map/set enumeration order.

## Deterministic identity

The SYS-015 stage revision binds:

- the exact SYS-014 stage revision;
- every exact runtime-site occurrence and descriptor;
- every exact claim revision and source basis;
- the complete forward claim-to-site relation;
- the complete reverse site-to-claim relation; and
- the exact site-owned physical cost registry.

Semantically unordered maps and sets are canonicalized, so enumeration order does not change the stage identity.

## Deferred

This slice intentionally does not yet implement:

- reusable primitive identity across distinct semantic sites (`SYS-016`);
- target-inserted staging effects and their authority/failure/subject-transfer account (`SYS-017`);
- complete ADR-011 cost attribution and shared-mechanism charging (`SYS-018`);
- next-stage ABI/deployment requirements (`SYS-019`);
- final deterministic Systems/StageContract revision closure (`SYS-020`);
- ADR-017 carrier adequacy and coverage; or
- final assurance-manifest acceptance of composite runtime claims.

SYS-015 establishes the cardinality invariant those slices need: runtime sites, assurance claims, semantic subjects, and physical costs are separate identities connected by explicit relations rather than inferred from accidental one-to-one structure.
