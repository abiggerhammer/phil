# PHIL-AUD-SESSION-TYPE-SORT-001 remediation

## Audit identity

- Finding: `PHIL-AUD-SESSION-TYPE-SORT-001`
- Event: `PHIL-AUDIT-20260921-SESSION-TYPE-COVERAGE`
- Original frozen source: `a9f2c745686d8ae1b923e21045554f4864956e76`
- Affected public Core boundary: `Phil.Core.Value.checkValue` / ascription
- Missing producer check: `Phil.Core.SortCheck.checkTypeSorts`

This slice repairs recursive type-sort validation. It does not close the separate
`PHIL-AUD-TYPE-DEFINEDNESS-001` prerequisite-preservation finding.

## Root cause

`checkValueInternal` checks the expected annotation with `checkTypeSorts` before
value synthesis and type equality. The old sorter validated Bytes indexes, Proof
propositions, product elements, refinement bases and annotated opaque sorts, but
stopped at `TyEndpoint`.

Endpoint equality can later normalize nested message types. An ill-sorted term
such as `RefScale 0 (RefBool True)` therefore could disappear to `0` before
any sort checker visited it, making a malformed annotation compare equal to a
well-sorted endpoint.

## Repair

`checkTypeSorts` now uses a lexical logical scope distinct from resource
ownership and recursively validates:

- endpoint send/receive message types;
- select/offer branch payload types;
- endpoint continuations;
- pending-receive continuations;
- refinement predicates under their own value binder;
- existing product, Proof, Bytes and annotated-sort children.

Session message/payload binders are added only for their continuations. They are
not visible in their own message type. Each branch starts from the same outer
scope, so branch-local binders do not leak to siblings.

The logical scope does not mutate `CheckState`, consume resources, or reinsert
consumed owners. Refinement terms resolve lexical binders first and fall back to
the existing resource context for ordinary free variables.

Recursive sessions are traversed once through their finite syntax. `Rec` does
not trigger unfolding, and `SessionVar` is a leaf for this sort-formation pass.

For `TyPendingRecv`, the pending binder is known to represent the grammar frame
from the receive-frame path, so its continuation is checked under
`TyFrame pendingGrammar`.

## Permanent replay

`test/Phase1AuditSessionTypeSortMain.hs` reproduces Astra's S01-S08:

- malformed receive payload;
- malformed ascription;
- malformed send payload;
- malformed branch payload;
- malformed later-continuation payload;
- malformed nested refinement predicate;
- out-of-range UInt literal hidden by `toNat`; and
- malformed Proof payload predicate.

The controls retain:

- direct malformed term/Bytes/Proof rejection;
- valid normalization;
- dependent session binders;
- alpha-renamed dependent binders;
- guarded recursive equality/unfolding;
- ordinary payload/outcome mismatches;
- borrowed and unknown resource rejection; and
- well-sorted but uninhabited refinement types.

The dedicated workflow also replays the existing sort-check, value and
refinement-evidence suites.

## Assurance boundary

A green exact-head replay closes only the recursive original-annotation
sort-validation slice.

This repair does not establish or change:

- natural-subtraction definedness prerequisites;
- `PHIL-AUD-TYPE-DEFINEDNESS-001`;
- raw product-contained recursive-session substitution outside Message
  competence;
- `PHIL-AUD-SESSION-CONTINUATION-BINDING-001`;
- proof correspondence;
- native lowering; or
- Certified-ledger status.
