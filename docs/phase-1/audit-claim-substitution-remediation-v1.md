# Phase 1 audit remediation: transparent-claim substitution

Finding: `PHIL-AUD-CLAIM-SUBSTITUTION-001`

Audit event: `PHIL-AUDIT-20260921-TYPE-DEFINEDNESS-CLAIM-INSTANTIATION`

Original audited source: `a9f2c745686d8ae1b923e21045554f4864956e76` (`phil-v0.1.0-phase1`)

## Root cause

Transparent claim application instantiated formals with a left fold of ordinary single-name substitution. Each later substitution therefore traversed the result of the previous one, including caller terms that had already been inserted into the claim body.

For the valid declaration

```text
Same(p : Bool, q : Bool) = (p == q)
```

and a caller variable also named `q`, `Same(q, true)` was transformed as:

```text
p == q
q == q
true == true
```

instead of preserving the caller dependency as `q == true`. Normalization could then turn the altered proposition into `Truth` and let the ordinary focusing/discharge consumer treat it as definitionally established.

## Repair

Transparent claims now instantiate all formals in one traversal of the original body. The substitution map is consulted only for variables encountered in that original body. A replacement term is returned verbatim and is never traversed again by another formal replacement.

This preserves caller terms even when their free names collide with later formal spellings. It also preserves the existing arity, sort/coercion, opaque-claim, recursion, normalization, and focusing behavior.

## Permanent replay

`test/Phase1AuditClaimSubstitutionMain.hs` covers:

- C01 the original caller/formal collision and exact `q == true` result;
- C02 the collision cannot become `FocusByDefinition`;
- C03 the ordinary obligation consumer cannot statically discharge the altered claim;
- C04 formal alpha-renaming preserves the instantiated proposition;
- C05 a nested caller term survives a later formal collision;
- C06 repeated identical actuals still normalize definitionally;
- C07 arity rejection remains unchanged;
- C08 argument-sort rejection remains unchanged; and
- C09 opaque claims retain their supplied actuals and explicit-mechanism boundary.

The dedicated workflow strict-typechecks the repaired module and replay under `-Wall -Werror`, executes the replay, and reruns the existing focusing and discharge suites.

## Assurance boundary

This closes only simultaneous caller-preserving instantiation of transparent claim bodies and its exposed focusing/discharge consumer path. It does not close `PHIL-AUD-TYPE-DEFINEDNESS-001`, prove the separate Grammar-v1 source bridge, change opaque claim semantics, establish solver correctness, alter proof correspondence, or extend native/LLVM assurance. The frozen-source finding remains distinct from later proof/refinement work.
