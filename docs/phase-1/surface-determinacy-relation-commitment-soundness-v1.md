# Phase 1 surface determinacy: relation commitment soundness v1

This tranche closes the final structural resolver family for `PHIL-SURFACE-DETERM-001`: the `proposition_atom` overlap between relation propositions and grouping, Boolean literals, or claim applications.

## Resolver boundary repair

`relation_commit_scan` searches for a top-level relation operator after a shared proposition-atom prefix. It must stop when the current proposition atom has ended; otherwise tokens belonging to the enclosing grammar can be mistaken for part of the candidate relation.

The original hand-written boundary set covered `and`, `or`, `;`, `,`, `=>`, and `}`. The grammar-derived FOLLOW surface exposes three additional depth-zero continuations:

- `then`, after `when proposition` in session syntax;
- `within`, after `assume proposition`;
- `{`, when a proposition is immediately followed by a block, such as loop invariants and join conditions.

The `{` case is especially important because treating it first as a delimiter opener would make the scanner enter the following block instead of stopping at the completed proposition.

The repaired scanner therefore checks a proposition boundary at depth zero before delimiter-opening logic. At positive depth, delimiters retain their normal nesting behavior.

## Machine-checked continuation coverage

The proof defines the exact computed `FOLLOW(proposition_atom)` set from `phase1_surface_follow_facts` and checks that every member either:

- is EOF;
- is a certified proposition boundary; or
- is a closing delimiter that stops a depth-zero relation scan.

`phase1_surface_proposition_atom_follow_stops_relation_scan` is computed with `vm_compute`; it is the certificate that the resolver boundary policy covers the actual grammar rather than a manually selected subset.

## Relation branch

A `relation_proposition` has the exact shape:

```text
additive_expression relation_operator additive_expression
```

The relation-neutral semantic foundation proves that the first `additive_expression` consumes a depth-zero neutral prefix. The `relation_operator` derivation is then proved to consume exactly one of the eight relation-operator literals. The structural scanner theorem therefore forces `proposition_atom_decision` to choose alternative 0.

## Nonrelation branches

For grouping, `true`, `false`, and `claim_application`, the ordinary branch derivation is combined with an accepting `proposition_atom` continuation. The computed FOLLOW certificate makes the continuation scan false, so the resolver commits respectively to alternatives 1, 2, 3, and 4.

The grouping proof additionally uses delimiter balance for the inner `proposition`, entered at parenthesis depth one. The claim proof uses the relation-neutral certificate for the complete `claim_application` prefix and the qualified-name proof to establish its leading `IDENTIFIER` token.

## Consequence

After this tranche, all four structural resolver families have ordinary-derivation semantic soundness:

1. qualified-name pattern vs record pattern;
2. balanced-parenthesis comma vs close;
3. brace colon vs effect-set commitment;
4. proposition relation-operator commitment.

The remaining work for `PHIL-SURFACE-DETERM-001` is the final mutual induction showing that every ordinary complete Grammar-v1 derivation follows `phase1_surface_predictive_oracle`, followed by the already-proved same-oracle functionality theorem.
