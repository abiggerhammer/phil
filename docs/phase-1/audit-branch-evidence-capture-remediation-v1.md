# PHIL-AUD-BRANCH-EVIDENCE-CAPTURE-001 remediation

## Audit identity

- Finding: `PHIL-AUD-BRANCH-EVIDENCE-CAPTURE-001`
- Event: `PHIL-AUDIT-20260922-BRANCH-EVIDENCE-SCOPE`
- Original frozen source: `a9f2c745686d8ae1b923e21045554f4864956e76`
- Public implementation boundary: `Phil.Surface.Check.Engine.pruneScopedPath`
- Proof-side groundwork: merged PR #1286, `Phil.Surface.BranchEvidenceSupport`

This slice repairs the concrete Surface producer/consumer path. It does not
promote proof or Certified status by itself.

## Root cause

Scoped branch checking correctly removed branch-local bindings after a branch
body completed, but it pruned only the state. The value escaping the branch was
left unchanged.

A proof such as `Proof[x == true]` could therefore leave a branch after local
`x` had been removed. Reusing the spelling `x` later created a fresh binding
that the old proof could accidentally match.

The original proof is valid when produced. The defect is loss of subject support
across scope exit and later spelling reuse.

## Repair

Before branch-local bindings are removed, `pruneScopedPath` now computes the
free logical subjects required by the escaping runtime value.

The support walk is binder-aware:

- refinement binders scope over their predicates, not their base types;
- send/receive message binders scope over their continuations, not their own
  message types;
- branch payload binders scope only over that branch continuation;
- recursive session variables are not confused with term subjects;
- tuples are checked element-by-element; and
- record field aliases and selected provenance-bearing shapes contribute their
  logical subjects.

If an escaping value depends on a local binding that is about to disappear, the
scope exit rejects with `TypeMismatch`. Closed values and values whose free
subjects remain in the outer scope continue unchanged.

The check does not restore consumed resources, rename subjects textually, or
ban source spelling reuse globally.

## Permanent replay

`test/Phase1AuditBranchEvidenceCaptureMain.hs` reproduces Astra's source cases:

- R01 flat escaping proof;
- R02 tuple-carried proof;
- R03 nested decision;
- R04 offer-local proof;
- C01-C10 positive and negative controls.

It also retains Astra's K01-K07 Core controls for resource joins, affine
intersection, active loans, per-path residual preservation, guarded recursion,
and the legitimate true/false refinement producer contrast.

The dedicated workflow builds the full Haskell substrate, strict-typechecks the
repair and replay under `-Wall -Werror`, runs the new audit corpus, and replays
the existing Surface conformance, value and refinement-evidence suites.

## Assurance boundary

A green exact-head replay closes only the concrete branch-value subject-support
remediation.

This slice does not establish:

- general stable subject identity for every future representation;
- complete residual-obligation support correspondence at Surface joins;
- `PHIL-AUD-SESSION-CONTINUATION-BINDING-001`;
- remaining definedness/provenance findings;
- native lowering; or
- final frozen-snapshot / Certified-ledger closure.
