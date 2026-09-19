# PHIL-P1-REVIEW-R06 proof boundary

This slice certifies Astra Review R06: the optional `using` operand of term-level `receive_exact` and `select` is evaluated **before** the later `on` endpoint operand.

R06 is an aggregate boundary over the already-certified `PHIL-EXEC-ORDER-001` source-order authority. That predecessor already establishes that strict children execute left-to-right and that a stopping child suppresses all later children. R06 contributes the form-specific child plans:

- `receive_exact amount using evidence on endpoint` → amount, evidence, endpoint;
- `receive_exact amount on endpoint` → amount, endpoint;
- `select Branch(args...) using evidence on endpoint` → branch arguments, evidence, endpoint; and
- `select Branch(args...) on endpoint` → branch arguments, endpoint.

The proof then derives the key fail-closed consequence from the existing strict-child authority: if the `using` operand terminates, the later `on` operand contributes no execution events.

For `select`, the normalized proof treats the already source-ordered branch-argument trace as one prefix summary. Ordering inside that argument prefix remains owned by `PHIL-EXEC-ORDER-001`; R06 certifies the placement of the optional `using` operand between that prefix and the endpoint.

The concrete Haskell correspondence is `Phil.Surface.GrammarV1.SequentialExecution.executeExpression`:

- `GrammarV1ReceiveExactExpression amount endpoint evidence` traverses `[amount] <> maybe [] pure evidence <> [endpoint]`;
- `GrammarV1SelectExpression branch endpoint boundary` traverses branch arguments, then optional boundary/evidence, then endpoint; and
- `executeExpressions` stops immediately when a child returns non-continuing control.

The permanent six-case R06 regression parses real source and checks started/completed child-call order for both forms, with and without `using`, plus terminal-`using` suppression of the endpoint.

Concrete parser/AST constructor layout, `Located` identity, event rendering, terminal-evidence lookup, Haskell list traversal, GHC/runtime correctness, and Rocq/toolchain correctness remain explicit implementation boundaries.
