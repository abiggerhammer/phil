# PHIL-AUD-REFINEMENT-CONSUMED-SUBJECT-001 remediation

## Finding

`PHIL-AUD-REFINEMENT-CONSUMED-SUBJECT-001` is a Phase 1 Core completeness defect recorded by `PHIL-AUDIT-20260921-REFINEMENT-VALUE-CORRESPONDENCE`.

When `checkValueInternal` checked an affine or linear value against `TyRefined`, it first checked the base type. That ordinary base check correctly consumed the resource. The refinement predicate was then instantiated with the retained logical subject term but sorted and discharged against the post-consumption resource context. A proposition such as `len(payload) = len(payload)` could therefore fail with `UnknownRefinementVariable payload` even though `payload` was the exact value just checked.

The resource transition itself was correct. The missing piece was keeping the checked value's subject available to the logical refinement phase without making the resource live again.

## Repair

The refinement path now separates two views after the base check:

- the **post-consumption state**, which remains authoritative for affine/linear ownership; and
- a **logical refinement state**, which restores only the checked value's `RefVar` subject binding from the incoming context while sorting/discharging its predicate.

Only that one subject binding is restored. Unrelated consumed resources and active loans are not restored. Ordinary successful discharge returns the post-consumption resource state unchanged.

Residual refinement checking uses the same logical subject view, but after emitting obligations it copies only the resulting residual-obligation map back onto the real post-consumption state. Residualization therefore cannot resurrect ownership.

## Permanent regression

`test/Phase1AuditRefinementConsumedSubjectMain.hs` records the implementation boundary directly:

- R01: a linear `Bytes[7]` subject can discharge a reflexive length refinement and is still consumed exactly once;
- R02: the same property holds for an affine subject;
- R03: explicit reusable proof evidence may refer to the consumed subject without restoring it;
- R04: evidence carried by an already-refined linear binding remains usable after base checking;
- R05: `VAscribe` composes with the same subject visibility and ownership transition;
- R06: residualization retains the exact subject in the emitted obligation while leaving ownership consumed;
- C01: subject-independent linear refinement still consumes once;
- C02: an actively borrowed owner still rejects before refinement checking;
- C03: unrestricted refinement subjects remain live;
- C04: malformed subject-dependent predicates still fail sort checking; and
- C05: an otherwise well-sorted opaque requirement reports missing evidence rather than a missing subject.

The dedicated workflow also replays the ordinary value suite, refinement-evidence suite, and the Core type-definedness audit controls under `-Wall -Werror`.

## Assurance boundary

This closes the Haskell Core value/refinement composition defect at the recorded implementation boundary. It does not change the proposition logic, evidence truth assumptions, resource-mode rules, Surface syntax, Rocq proofs or proof correspondence, native/LLVM realization, or Certified status. The repair deliberately preserves the existing rule that affine and linear owners are absent from the returned resource context after successful checking.