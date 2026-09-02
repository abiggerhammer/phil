# Phase 1 surface determinacy: simple resolver tranche

This tranche continues `PHIL-SURFACE-DETERM-001` after the exact overlap-completeness proof in #572.

## Proof boundary

`proof/Phil/Surface/GrammarDeterminacySimpleResolvers.v` binds two reusable resolver families to seven exact sites in the generated 15-site certificate:

- two reserved-keyword versus `<IDENTIFIER>` alternative overlaps (`declaration` and `generic_requirement`); and
- five comma-list repetition overlaps (`case_pattern`, `construct_expression`, `record_decl`, `record_pattern`, and record-style `variant_payload`).

The concrete-token proof model already separates grammar literals (`TLiteral`) from lexical classes (`TLexical`). This is the admitted lexical boundary used by the resolver proof; correspondence from source bytes and the Haskell lexer to that model remains owned by `PHIL-SURFACE-GRAMMAR-CORR-001`.

The resolver is path- and input-indexed, matching the oracle interface established by #554. It does not inspect Haskell parser ordering or recovery behavior.

## What is proved here

The proof mechanically checks that the exact certificate contains 2 keyword sites, 5 trailing-comma sites, and therefore exactly 7 sites handled by this tranche. It then defines deterministic decisions for those families:

- `provider IDENTIFIER` commits the provider-contract branch while `provider implementation` commits the provider-implementation branch;
- `boundary IDENTIFIER` commits the ordinary boundary requirement while `boundary representation` commits the representation requirement; and
- at each certified comma repetition, comma followed by `<IDENTIFIER>` continues the list, while `}` or comma followed by `}` stops the repetition so the optional trailing comma/closing delimiter can consume the remainder.

## Remaining work

This does not discharge `PHIL-SURFACE-DETERM-001`.

Eight certified sites remain: identifier/record-pattern commitment, expression and static-argument parenthesis/brace commitment, and the four proposition-atom relation/parenthesized/literal/claim overlaps. Those need structural/complete-operand resolver lemmas. After all 15 sites have resolvers, a final bridge must extend the resolver to every non-overlap grammar choice, prove every ordinary `Phase1CompleteDerivation` is resolved by that one oracle, and compose with #554's `same_oracle_has_one_complete_parse`.
