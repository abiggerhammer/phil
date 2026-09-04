# Phase 1 surface determinacy: static-argument parenthesis soundness v1

This slice closes the parenthesis-led `static_argument` overlap for `PHIL-SURFACE-DETERM-001`.

The certified resolver distinguishes the two alternatives that can begin with `(`:

- branch 0: `nonreference_type_expression`, which can begin with `(` only through `tuple_type`; and
- branch 2: `static_value_expression`, which can begin with `(` only through the parenthesized `static_nonreference_primary_expression`.

For the type branch, an ordinary `tuple_type` derivation exposes

```text
( type_expression , ...
```

and the parenthesis-neutral semantic foundation proves the consumed `type_expression` prefix leaves the scanner at depth zero. The following comma therefore commits branch 0.

For the value branch, the proof follows the ordinary grammar derivation through `static_additive_expression`, `static_multiplicative_expression`, and `static_postfix_expression`. A leading `(` rules out the qualified-name postfix branch and then rules out the literal/integer static-primary branches, leaving exactly

```text
( static_value_expression )
```

The consumed inner static value is parenthesis-neutral at depth zero, so the matching close commits branch 2.

Together with the `primary_expression` commitment proof, this closes the balanced-parenthesis comma/close structural resolver family. The remaining structural family is proposition-atom relation commitment.
