# PHIL-AUD-BRANCH-EVIDENCE-CAPTURE-001 remediation

## Audit identity

- Finding: `PHIL-AUD-BRANCH-EVIDENCE-CAPTURE-001`
- Original event: `PHIL-AUDIT-20260922-BRANCH-EVIDENCE-SCOPE`
- Delayed-evidence replay: `PHIL-AUDIT-20260923-SESSION-SCOPE-REPAIR-REPLAY`
- Original frozen source: `a9f2c745686d8ae1b923e21045554f4864956e76`
- Independent repair-review pin: `5f8e7e9fd540d8e66ee44b0d96dfe6c901001e50`
- Public implementation boundary: `Phil.Surface.Check.Engine.pruneScopedPath`
- Proof-side groundwork: merged PR #1286, `Phil.Surface.BranchEvidenceSupport`

This slice repairs the concrete Surface producer/consumer path. It does not
promote proof or Certified status by itself.

## Root cause

Scoped branch checking correctly removed branch-local bindings after a branch
body completed, but the original support walk covered only materialized runtime
values. An opaque `DecisionShape` was treated as having no support even when its
metadata retained logical subjects for a later branch elimination.

For example, `ValidationDecision claim context subject` can leave a branch while
`subject` is local. A later `accepted(e)` arm materializes
`TyValidated claim context subject`. If the old spelling is reused first, that
delayed evidence can otherwise be retargeted to a distinct binding.

This is the delayed-value manifestation of the existing
`PHIL-AUD-BRANCH-EVIDENCE-CAPTURE-001` root, not a separate finding.

## Repair

Before branch-local bindings are removed, `pruneScopedPath` computes the free
logical subjects required by the complete escaping runtime value, including
subjects retained by delayed decision metadata.

The support walk is binder-aware:

- refinement binders scope over their predicates, not their base types;
- send/receive message binders scope over their continuations, not their own
  message types;
- branch payload binders scope only over that branch continuation;
- recursive session variables are not confused with term subjects;
- tuples are checked element-by-element;
- record field aliases and selected provenance-bearing shapes contribute their
  logical subjects; and
- decision constructors contribute the support that their later eliminations
  can expose: validation context/subject identities, digest propositions,
  recognition provenance, provider/callable payload and proposition support,
  callable resource residue, and the fixed choose-supported proof subjects.

If an escaping value depends on a local binding that is about to disappear, the
scope exit rejects with `TypeMismatch`. Closed decisions and decisions whose
subjects remain in the outer scope continue unchanged.

The check does not restore consumed resources, rename subjects textually, ban
source spelling reuse globally, or reject all decisions/tuples/products.

## Permanent replay

`test/Phase1AuditBranchEvidenceCaptureMain.hs` retains the original remediation
corpus:

- R01 flat escaping proof;
- R02 tuple-carried proof;
- R03 nested decision;
- R04 offer-local proof;
- C01-C10 positive and negative controls; and
- K01-K07 Core controls for resource joins, affine intersection, active loans,
  per-path residual preservation, guarded recursion, and legitimate true/false
  refinement production.

`test/Phase1AuditBranchEvidenceDelayedMain.hs` adds the independently observed
delayed-decision route in required-correctness form:

- S01 rejects a validation decision that would outlive its branch-local subject;
- S02 rejects the same delayed support hidden in a tuple;
- S03 preserves a decision about a subject that genuinely survives the branch;
- S04 preserves exact rejection when valid evidence is offered for a different
  surviving subject;
- S05 preserves closed Boolean decisions; and
- S06 preserves ordinary source-spelling reuse when no retained support escapes.

The dedicated workflow builds the full Haskell substrate, strict-typechecks the
implementation and both replays under `-Wall -Werror`, runs both audit corpora,
and replays the existing Surface conformance, value and refinement-evidence
suites.

## Assurance boundary

A green exact-head replay closes only the concrete branch-value and delayed
branch-decision subject-support remediation.

This slice does not establish:

- general stable subject identity for every future representation;
- complete residual-obligation support correspondence at Surface joins;
- `D-RES-SUPPORT-01` durable post-consumption residual interpretation;
- `D-NUM-ENV-ADMISSION-01` / `D-NUM-RESULT-SUBJECT-01` production numeric
  adapters;
- native lowering; or
- final frozen-snapshot / Certified-ledger closure.
