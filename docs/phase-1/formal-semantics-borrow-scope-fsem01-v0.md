# FSEM-01 — Phase 1 borrow-scope judgment boundary and executable controls

> **Status: proposed review slice, not a new normative typing rule or a global
> soundness theorem.** The Phase 1 language authority remains the accepted
> contracts, grammar and their checked evidence. The FSEM-00
> [judgment inventory](formal-semantics-judgment-inventory-v0.md) identifies
> the wider obligations.

## Exact question

Can a source binder introduced by \`borrow owner as view { body }\` be
referenced **after the loan's lexical region** without confusing that failure
with an unrelated result-type mismatch?

The [worked examples draft](typing-rules-worked-examples-draft-v1.md) contains
a \`ReadId\` negative returning \`view\` where \`U64\` is expected. That is
pedagogically useful but ambiguous as an isolated diagnostic: both loan escape
and result-type checking could reject it.

This slice pairs two *Grammar-v1 parsed function source strings*, each declaring
the **same \`U8\` return type**, differing in exactly one identifier.

**Positive, scoped owner use:**

~~~phil
fn borrow_return(owner : U8) -> U8 satisfies C {
  borrow owner as view { view; };
  return owner;
}
~~~

**Negative, closed-region view use:**

~~~phil
fn borrow_return(owner : U8) -> U8 satisfies C {
  borrow owner as view { view; };
  return view;
}
~~~

The scoped binder checker accepts the first return occurrence as the original
\`owner\` binder. In the second, the borrow checker has already left the child
lexical region: direct resolution of the \`view\` return reports
\`GrammarV1BinderNotInScope\`. This makes the *local-name visibility* distinction
testable without changing the function's declared result type.

### Concrete executable test

[\`test/Phase1GrammarV1BorrowViewScopeMain.hs\`](../../test/Phase1GrammarV1BorrowViewScopeMain.hs)
contains \`borrowViewNotReturnedAfterScope\`. It:

1. Parses both complete Grammar-v1 function declarations.
2. Derives owner semantic identity from the same declaration lineage.
3. Runs \`grammarV1CheckedBorrowViewInScope\` on each borrow.
4. Extracts the exact following return expression from the parsed source.
5. Requires the positive return to resolve to the owner, and the negative
   return spelling to be \`view\` with no local occurrence.
6. Requires \`grammarV1ResolveLocal\` to return
   \`GrammarV1BinderNotInScope\` for that negative occurrence.

**Important limitation:** this is a **real executable parsed-source
lexical-scope conformance test**, not a demonstrated full Phase 1 checker
\`BorrowEscape\` class. The lexical resolver can return \`Nothing\` for names
that are not *local*, because static/global name resolution is a separate
competence boundary. This test explicitly validates the local binder's
identity and lifetime; the full source-level rejection and diagnostic path
must still be tied to the chosen Phase 1 root checking judgment.

A separate **Phase 0** conformance test already exists:
[\`test/Phase1AuditBorrowScopeMain.hs\`](../../test/Phase1AuditBorrowScopeMain.hs)
uses \`Phil.Surface.Check.checkSurfaceComponent\` with a **Phase 0
environment**, and verifies \`BorrowEscape\` for direct returned views and
tuple-contained views, as well as structural use errors. Its name starts
\`Phase1Audit\` but that does **not** make the exercised checker a normative
Phase 1 Grammar-v1 source checker. Treat it as evidence of the intended
safety property in a different surface-checker boundary.

## Proposed FSEM-R01 judgment interface (not adopted)

Let \`R = (Γ, A, Δ, Loans)\` be a checker state, \`o\` an active owner,
\`v\` a fresh borrow-view binder, and \`ρ\` its lexical region.

~~~text
  owner(o, R)           permitted-borrow-mode(o, R)
  fresh-local(v, R)     scope(v) = ρ
  Σ ; R + loan(o,v,ρ) ⊢ body ⇐ T ⊣ Rbody ▷ Φ
  no-owner-move-while-loaned(o, Rbody)
  no-escaping-view-identity(v, body-result, Rbody)
  loan-closed(ρ, Rbody)
  ------------------------------------------------------ BORROW-SCOPE (proposed)
  Σ ; R ⊢ borrow o as v {body} ⇐ T ⊣ Rafter ▷ Φ
~~~

All helper predicates above are *proposed placeholders*. In particular,
\`no-escaping-view-identity\` requires an exact definition over the elaborated
term and captured values, not a name-spelling test. Ownership and linear
conservation across \`Rafter\` also require precise state transition rules.
No theorem for this composite rule is claimed.

The narrow **actual** local-scope observation checked in this PR is:

~~~text
  resolveLocal(afterBorrowScope, "owner") = ownerBinder
  resolveLocal(afterBorrowScope, "view")  = BinderNotInScope
~~~

It is essential not to turn that observation into a global type-safety proof
or an assertion that every source form has already been handled.

## Existing mechanized and implementation boundaries

| Evidence | What it establishes | What remains |
| --- | --- | --- |
| [\`Context.v\`](../../proof/Phil/Core/Context.v) — \`consumeLinear_success_exact\` | Exact consumption in an extensional resource-map model | Correct translation of every concrete source borrow/move into this model |
| [\`ResourceScope.v\`](../../proof/Phil/Core/ResourceScope.v) — \`scoped_loan_cannot_cross_continuing_boundary\` | Live scoped loans cannot be accepted by the *specified* continuing projection relation | Extraction of every source borrow/branch/loop boundary and proof of correspondence |
| [\`BinderScope.hs\`](../../src/Phil/Surface/GrammarV1/BinderScope.hs) and [\`BorrowViewScope.hs\`](../../src/Phil/Surface/GrammarV1/BorrowViewScope.hs) | Concrete lexical binder identity and child-region handling | End-to-end binding, type, ownership and error classification over supported Phase 1 source |
| [Phase 1 borrow-view tests](../../test/Phase1GrammarV1BorrowViewScopeMain.hs) | Scoped visibility, identity and the new matched-return-type control | Complete program checker rejection on the exact negative |
| [Phase 0 audit borrow-scope tests](../../test/Phase1AuditBorrowScopeMain.hs) | Executable \`BorrowEscape\`/structural error classification in the Phase 0 checker | A separate Phase 1 Grammar-v1 diagnostic/correspondence argument |

## Open formalization/verification tasks

1. Define an accepted exact owner/loan/result state judgment, including
   aggregate views, alias escapes, move restrictions, terminal failure paths
   and legal affine disposal.
2. Connect Grammar-v1 local resolution to the full Phase 1 source checker,
   with a **diagnostically isolated** negative that fails by escaped loan,
   rather than by a missing global definition or an expected-type mismatch.
3. State the precise relation between concrete source names/identities and
   proof-side owners/loan sets. Discharge the extraction and preservation
   obligation, not just the local model theorem.
4. Extend executable controls across branch joins, loop backedges, returned
   aggregates and callable capture where those constructs are admitted.
5. Adopt the finalized judgment through the semantic-authority review
   process and register any real discharged theorem/evidence in the Logic
   Ledger and Conformance Matrix.

**No semantics have been widened and no new normative theorem is asserted by
this document.** The next FSEM-01 slice should focus on the full source
error path and exact loan-state correspondence, with all assumptions explicit.
