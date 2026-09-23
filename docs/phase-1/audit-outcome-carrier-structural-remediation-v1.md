# PHIL-AUD-OUTCOME-CARRIER-STRUCTURAL-001 remediation

This remediation closes the implementation-side structural carrier defect recorded by the Phase 1 defensive audit for the public supplied-contract Surface checker.

## Finding

A branch-dispatched callable was represented as an unrestricted `CallableDecision` scalar even when eliminating that result was responsible for transferring a restricted payload, applying branch-specific resource residue, enforcing residual obligations, or resolving non-continuing caller control. Because a stored unrestricted decision could be read repeatedly or dropped, one invocation result could expose owning payloads more than once or hide responsibilities by never entering an outcome arm.

The bug is at the result carrier boundary. Individual callable arms already check payload modes, branch-local completion, occurrence-scoped facts/residual obligations, branch resource residue, and terminal/fatal control when the arm is entered.

A later source-derived audit follow-up found one remaining consumer asymmetry: named bindings and expression discard used the effective carrier mode, but a callable receiving another callable's result directly as an anonymous argument compared only the raw `ScalarValue` mode. That allowed an owning or obligation-bearing `invoke Worker(...)` result to satisfy an unrestricted `CallableDecision` parameter even though the equivalent `let d = invoke Worker(...); invoke InspectDecision(d)` form was rejected.

## Repair

`Phil.Surface.Check.Support` derives the effective structural mode of a callable decision from the responsibilities retained in its `DecisionShape` and exports that single calculation for all relevant consumers.

A callable decision carrier is:

- **linear** when any outcome returns a linear payload, carries a residual obligation, carries occurrence resource residue, or has declared close/fatal caller control;
- **affine** when no linear responsibility exists but at least one outcome returns an affine payload; and
- **unrestricted** only when all outcomes are continuing, all payloads are unrestricted, and there are no residual obligations or occurrence resource residues.

The effective mode is applied when deciding whether an expression result may be discarded, when the value is installed as a named binding, and when `evalCallable` checks the structural mode of a scalar argument. Anonymous and named consumers therefore see the same responsibility-bearing contract instead of depending on an optional `let` binding. Existing variable movement supplies named one-use behavior: a linear/affine carrier is consumed by its first read, an alias receives the same restricted mode, and final linear-completion checks reject an abandoned linear carrier.

This preserves the supported direct-once and stored-once decision forms (`decide invoke ...` and `let d = invoke ...; decide d ...`). Ordinary Boolean decisions and responsibility-free callable decisions remain unrestricted.

## Permanent replay

`test/Phase1AuditOutcomeCarrierStructuralMain.hs` preserves the audit corpus:

- R01–R04: repeat, alias, discard, and abandon a carrier whose outcomes return a linear owner;
- R05–R06: discard or abandon a carrier whose outcomes retain residual obligations;
- R07–R08: direct anonymous callable arguments cannot erase owning-payload or residual-obligation responsibility;
- C01–C03: direct-once, stored-once, and next-consumer ownership transfer remain accepted;
- C04–C07: existing local linearity, exhaustiveness, and binder-arity rejection remains unchanged;
- C08: an ordinary unrestricted Boolean decision remains reusable;
- C09–C16: residual-obligation installation/discharge, occurrence isolation, early return, local fact scope, and nested-path controls remain unchanged;
- C17–C18: the equivalent named owner/obligation carriers receive the same structural-mode diagnostic as the direct anonymous boundary;
- C19: a pure unrestricted Boolean decision remains a valid anonymous unrestricted argument; and
- C20: ordinary callable argument type mismatch remains distinct from structural-mode rejection.

The dedicated workflow typechecks both `Support` and `Engine`, replays this permanent corpus, and replays the existing CALL-019 branch resource, installation, proof-binding, and Surface decision-bridge controls.

## Assurance boundary

This repair establishes structural use-count discipline for the public supplied-contract Surface result carrier and makes the direct callable-argument consumer use the same effective mode as named bindings and discard. It does not establish the semantic truth of supplied callable contracts, caller-resource relations, fact/obligation propositions, or callee lifecycle premises. It does not extend the enriched compiler bridge beyond its existing correlation contract, prove implementation/proof correspondence, or claim native/LLVM behavior. LLVM remains inside the Phase 1 trusted computing base.

The repair is intentionally local to carrier structural mode. It does not close delayed-evidence subject-identity work, O01 durable residual-subject interpretation, or refinement/proof-thread work.
