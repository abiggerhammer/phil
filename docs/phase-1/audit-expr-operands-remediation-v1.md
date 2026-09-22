# PHIL-AUD-EXPR-OPERANDS-001 remediation

## Audit identity

- Finding: `PHIL-AUD-EXPR-OPERANDS-001`
- Event: `PHIL-AUDIT-20260921-EXPR-CONSTRUCT`
- Original review snapshot: `1d6f8463942253664bed5b911ffa3170ab928069`
- Producer/checker boundary: `Phil.Surface.Check.Support.inferReadOnlyScalar`
- Public consumers: `checkSurfaceComponent` and
  `Phil.Verification.verifySurfaceApplication`

This slice repairs the operational Surface checker only. It does not promote any
proof or Certified status, and it does not address the separate constructor-
schema finding from the same audit tranche.

## Root cause

The parser retained both children and the operator of every binary expression,
but `inferReadOnlyScalar` previously matched:

`BinaryExpression _ _ _`

and returned a synthetic unrestricted Nat expression without visiting either
child.

That let invalid source disappear inside arithmetic:

- unknown or consumed names were never looked up;
- Boolean and other non-Nat operands were not rejected;
- unsupported/effectful calls were never visited; and
- the operator's competence boundary was not checked.

The public intrinsic verification route delegates to the same Surface checker,
so it did not add an independent operand traversal.

## Repair

Binary-expression read-only inference now recursively infers both operands
before producing a Nat expression.

Each child must be:

- an integer literal;
- a value with refinement sort `Nat`; or
- a fixed-width `UInt`, which is already the established implicit
  UInt-to-Nat arithmetic coercion.

Every other child rejects with `TypeMismatch`, while lookup of an unknown or
already-consumed variable retains the existing `StructuralUse` failure.

The repair is intentionally read-only: it does not execute an effectful child in
order to make arithmetic valid. Unsupported calls therefore reject instead of
being silently skipped.

The existing Phase-0 multiplication competence boundary is retained: one side
must be an integer literal, so symbolic-by-symbolic multiplication remains
fail-closed.

## Permanent regression

`test/Phase1AuditExprOperandsMain.hs` uses the ordinary common Phase-0
environment and drives each source through both:

- `parseSurfaceFile` → `checkSurfaceComponent`; and
- `verifySurfaceApplication`.

The two public results must agree on acceptance or rejection class.

Astra's e01–e11 corpus is reproduced exactly:

- e01 literal addition accepts;
- e02 bound `U32` plus literal accepts;
- e03 direct unknown name rejects;
- e04 unknown left operand rejects;
- e05 unknown right operand rejects;
- e06 nested unknown operand rejects;
- e07 Boolean arithmetic rejects;
- e08 undeclared call child rejects;
- e09 direct undeclared call remains rejected;
- e10 already-consumed operand rejects; and
- e11 effectful call child rejects rather than being silently skipped.

One additional compatibility control checks that symbolic `U32 * U32`
multiplication remains outside the Phase-0 arithmetic fragment.

The dedicated workflow also replays the established intrinsic-invalidity and
Surface conformance suites.

## Assurance boundary

A green exact-head replay closes the implementation/public-consumer remediation
for binary operand checking only.

This slice does not claim:

- execution semantics or arithmetic result computation;
- support for effectful arithmetic operands;
- constructor/schema validation;
- proof of the checker implementation;
- native lowering acceptance; or
- any Certified-ledger promotion.

The Rocq/proof lane and final frozen-snapshot delta review remain separate.
