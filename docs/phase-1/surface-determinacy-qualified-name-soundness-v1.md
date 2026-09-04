# Phase 1 surface determinacy: qualified-name soundness

This slice continues `PHIL-SURFACE-DETERM-001` after the global delimiter-balance proof.

It connects the qualified-name structural scanner to ordinary Grammar-v1 derivations:

- a derived `qualified_name` consumes exactly one `IDENTIFIER` followed by zero or more `.` `IDENTIFIER` pairs;
- the repetition spelling is proved for arbitrary derivations rather than parser examples; and
- any ordinary `record_pattern` derivation therefore presents the structural pattern resolver with a maximal qualified-name prefix followed by `{`, forcing `ChooseAlternative 2`.

The token-level commitment theorem itself was established by the structural-scanner tranche. This proof supplies the missing semantic bridge from arbitrary grammar derivations to that scanner theorem.

The remaining pattern direction is the plain-identifier branch: accepting continuation must rule out a following `.` or `{` when the ordinary derivation chose the identifier alternative. The parenthesis and proposition structural families still require their respective top-level neutral-prefix arguments.
