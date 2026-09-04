# Phase 1 surface determinacy — refinement brace soundness v1

This slice continues `PHIL-SURFACE-DETERM-001` after the pattern structural resolver proof.

It proves that every ordinary Grammar-v1 derivation of `refinement_type` exposes the exact structural prefix

```text
{ IDENTIFIER :
```

and therefore forces the certified `static_argument` structural resolver to choose alternative 0 (`nonreference_type_expression`).

The proof is implementation-independent. It uses only:

- the generated `refinement_type` rule table entry;
- ordinary `Derives` sequence structure;
- exact literal and identifier consumption lemmas; and
- the existing scanner theorem `static_argument_brace_colon_tail_commits_refinement`.

No parser behavior or example corpus is assumed.

This closes the refinement-type side of the brace-led `static_argument` overlap. The complementary `effect_set_literal` side remains a successor semantic slice; the parenthesis and proposition-relation structural families also remain open.
