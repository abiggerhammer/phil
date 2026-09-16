# Phase 1 Grammar-v1 protocol declaration correspondence

This slice extends `PHIL-SURFACE-GRAMMAR-CORR-001` from the declaration families already closed through #911 to `protocol_decl`.

The correspondence preserves the exact protocol name, ordered generic parameters, ordered generic requirements, and the grammar-mandated pair of ordered role-session declarations. Each role preserves its exact identifier and delegates its full `session_expression` payload to the session correspondence landed in #895.

The session layer already distinguishes static session references from nonreference sessions and preserves send/receive parameters, optional `using` boundaries, optional `when` guards, select/offer branch order, omitted versus explicit-empty branch parameters, recursive binders, continuations, and terminal labels. Nested type, proposition, and static-reference payloads continue to reuse their previously landed correspondence layers; #903 remains the deep static-argument closure authority.

The permanent gate includes minimal, rich, static-reference, Unicode, mixed-declaration, and adversarial role-session controls, then compares every accepted parser-corpus fixture through both the certified recognizer tree and the production parser AST.

After this slice, 13 of 15 declaration families have direct body correspondence. Only `architecture_decl` and `program_decl` remain before the certified-tree to production-AST declaration translation is total.

This remains **Active / Tested** evidence for `PHIL-SURFACE-GRAMMAR-CORR-001`. It does not by itself promote `PHIL-ASSURE-IMPL-CORR-001` to Implementation Refined; the remaining declaration families must still be closed and the final cumulative correspondence boundary re-audited.
