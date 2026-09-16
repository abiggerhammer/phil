# Phase 1 surface parser AST session correspondence v1

This slice continues `PHIL-SURFACE-GRAMMAR-CORR-001` after the effect-set correspondence slice.

The preceding converse-side slices establish the certified source spine, declaration choice, type-alias shell, generic parameters and requirements, static-reference/static-value structure, recursive type payloads, ordinary expression structure, proposition structure, and effect-set structure. The next shared unresolved syntax family is `session_expression`.

This slice closes the reusable session-expression structure:

- exact `session_expression` choice between nonreference session syntax and a static reference;
- all seven `nonreference_session_expression` alternatives: send, receive, select, offer, end, recursive, and continue;
- exact send/receive message parameter names and type payloads;
- exact optional `using` boundary references and `when` proposition guards;
- recursive continuation structure;
- exact select/offer branch order and labels;
- preservation of omitted branch parameters versus explicitly present empty `()` parameter lists;
- exact nonempty branch parameter lists, optional boundary annotations, optional guards, and continuations; and
- full accepted-corpus comparison for both role sessions of every protocol declaration.

Term-parameter type payloads reuse #887's recursive type-payload correspondence; guard propositions reuse #891; boundary/session references reuse #883. This slice therefore does not create a second interpretation for those shared forms.

## Evidence boundary

The type-payload representation still records the expression/proposition-bearing subpayloads at the #887 boundary; #889/#891 establish those sublanguages independently, but a later integration slice must compose them into one fully recursive type value. Static references likewise retain #883's shallow static-argument payload boundary. The 27 command-expression payload bodies remain opaque through #889, and most declaration bodies remain untranslated.

Accordingly `PHIL-SURFACE-GRAMMAR-CORR-001` remains **Active / Tested**, and `PHIL-ASSURE-IMPL-CORR-001` is not promoted. After session structure, the next useful integration step is to close the remaining nested static/type payload seams before the command-expression and remaining declaration-family translations consume them.
