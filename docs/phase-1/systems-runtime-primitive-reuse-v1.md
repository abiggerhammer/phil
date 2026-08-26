# Phase 1 Systems primitive reuse v1

Status: bounded executable conformance slice for `SYS-016`.

## Governing rule

A target may realize several distinct semantic runtime sites with the same implementation primitive or profile. Reuse is legal only if it does not collapse the semantic identities attached to those sites.

The bounded SYS-016 rule is:

> Reusing one exact runtime primitive/profile across distinct runtime-site occurrences must preserve each site's exact site identity, claim identities, semantic-subject basis, and site-owned physical cost identity. The forward site-to-profile and reverse profile-to-sites relations must agree exactly.

This is deliberately different from saying that equal-looking runtime sites are the same site. A reusable primitive is an implementation fact; site, claim, subject, and physical-cost identities remain semantic/accounting facts.

## Relation to SYS-015

`Phil.Systems.RuntimePrimitiveReuse` layers directly over the checked SYS-015 runtime claim/site graph. The SYS-015 verifier runs first.

SYS-015 already establishes:

- exact runtime-site occurrence identity;
- exact claim identity and source-fact basis;
- exact claim-to-site and site-to-claim closure; and
- one physical cost identity per exact runtime site.

SYS-016 asks what happens when multiple such sites select the same reusable lower-stage mechanism.

## Bounded primitive/profile identity

The current Systems IR already carries one exact reusable lower-stage mechanism token on every `RuntimeSiteRef`:

```text
runtimeSiteCostRef
```

For this bounded slice, SYS-016 interprets that existing token as the implementation-family/profile key:

```text
RuntimePrimitiveProfileRef(runtimeSiteCostRef)
```

This does **not** identify the profile with physical cost identity. SYS-015 deliberately derives physical cost identity from:

```text
exact runtime-site occurrence + runtimeSiteCostRef
```

so two sites may share the same profile token while retaining different physical cost identities.

A later richer realization schema may split mechanism/profile and cost-model references into separate first-class fields. The invariant established here survives that refinement: a reusable implementation reference must never become a license to merge semantic/accounting identities.

## Exact per-site projection

For every SYS-015 runtime site, SYS-016 derives:

```text
RuntimePrimitiveSiteBinding {
    exact_site
    primitive_profile
    exact_claims[]
    semantic_subject_refs[]
    physical_cost_identity
}
```

The site registry domain must equal the exact SYS-015 site domain.

The expected claims come from SYS-015's exact reverse site-to-claim relation.

The bounded semantic-subject basis retains:

- every explicit `RuntimeClaim.semantic_subjects` entry; and
- every exact source-fact reference carried by each claim.

The source-fact fallback is intentional. Some existing native one-obligation claims predate explicit claim-level subject labels, but their exact semantic source-fact identities are already present. Reusing a primitive may not erase those distinctions merely because the current claim object has no richer subject label yet.

## Bidirectional primitive reuse

The forward relation is one profile on each exact site binding:

```text
site -> primitive/profile
```

The reverse relation is independently materialized and checked:

```text
primitive/profile -> exact sites
```

Several sites may appear in the same reverse set. A site may not disappear from that set, move to another profile, or be duplicated under an invented profile alias.

## Physical cost remains site-owned

When a profile is shared across multiple sites, SYS-016 explicitly checks that the number of distinct physical cost identities equals the number of exact sites in that shared-profile group.

Thus:

```text
same primitive/profile
!= same runtime site
!= same physical cost identity
```

This remains weaker than SYS-018. SYS-016 does not yet compute aggregate cost or decide when two site-owned charges correspond to one lower physical mechanism. It establishes only the non-collapse invariant required before full cost attribution can safely reason about sharing.

## Witness pressure

### Framed upload

The frozen upload Systems artifact already contains a genuine primitive-reuse case:

```text
Hello recognition site -> upload.runtime.frame_receive
Begin recognition site -> upload.runtime.frame_receive
```

Both sites use the same lower-stage frame-receive mechanism/profile token.

They nevertheless retain distinct:

- `RuntimeSiteKey` occurrences;
- source obligation revisions and native runtime claims;
- semantic source-fact subjects (`hello.complete_recognition` versus `begin.complete_recognition`); and
- site-owned `PhysicalRuntimeCostIdentity` values.

No new backend mechanism is invented for SYS-016; the witness is already present in the frozen Phase 0 upload artifact.

### Steve

Steve currently has no modeled `RuntimeSiteRef` occurrences, so it traverses the same SYS-016 schema with empty site/profile relations and verifies successfully. No runtime mechanism is invented merely to make the second witness nonempty.

## Conformance corpus

The dedicated corpus covers:

1. SYS-015 upload predecessor regression;
2. SYS-015 Steve predecessor regression;
3. positive upload primitive-reuse closure;
4. positive Steve empty closure;
5. one frame-receive primitive reused across at least two exact sites;
6. distinct site identities under reuse;
7. distinct claim identities under reuse;
8. distinct semantic-subject identities under reuse;
9. distinct site-owned physical cost identities under reuse;
10. site-registry omission;
11. empty primitive/profile identity;
12. silent primitive/profile relabeling;
13. claim-identity collapse across reused sites;
14. semantic-subject collapse across reused sites;
15. physical-cost identity collapse across reused sites;
16. reverse profile-to-site omission;
17. invented reverse primitive/profile alias; and
18. deterministic stage identity under semantically irrelevant map/set enumeration order.

## Deterministic identity

The SYS-016 stage revision binds:

- the exact SYS-015 stage revision;
- every exact site-to-profile binding;
- every site's exact claims;
- every site's bounded semantic-subject basis;
- every site's exact physical cost identity; and
- the complete reverse profile-to-sites relation.

Semantically unordered maps and sets are canonicalized.

## Deferred

This slice intentionally does not yet implement:

- target-inserted staging effects and their authority/failure/subject-transfer account (`SYS-017`);
- complete ADR-011 cost attribution or shared-mechanism charging (`SYS-018`);
- next-stage ABI/deployment requirements (`SYS-019`);
- final deterministic Systems/StageContract revision closure (`SYS-020`);
- a richer first-class target primitive/profile schema; or
- ADR-017 runtime carrier adequacy and coverage.

SYS-016 establishes the identity discipline those slices need: implementation reuse is permitted, but semantic identity never follows implementation coincidence by accident.
