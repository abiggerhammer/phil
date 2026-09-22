# Phase 1 audit remediation — type definedness

Finding: `PHIL-AUD-TYPE-DEFINEDNESS-001`  
Audit event: `PHIL-AUDIT-20260921-TYPE-DEFINEDNESS-CLAIM-INSTANTIATION`

## Root cause

Two accepting paths could normalize away the syntax that generated Nat-subtraction definedness prerequisites before any consumer was required to check those prerequisites.

First, `canonicalizeProposition` returned only the normalized proposition and discarded `canonicalizeDetailed`'s side-condition list. A checked source refinement or Proof type such as `(3 - 5) == (3 - 5)` therefore became `Truth`, so the later value checker had no subtraction left from which to recover `5 <= 3`.

Second, non-refinement value checking validated type sorts and then compared types definitionally. `TyProof` propositions and `TyBytes` indices could therefore be normalized during equality without first discharging their definedness conditions; `Bytes[0 * (3 - 5)]` was the bounded audit witness.

## Repair

The public proposition canonicalizer now treats side conditions as part of the semantic precondition for normalization:

- a statically false prerequisite is rejected as `StaticallyFalseGoal`;
- if every prerequisite is statically true, ordinary canonicalization is retained;
- if a prerequisite is not statically decidable, the expanded proposition is retained rather than normalized away, so the accepting consumer can still derive and discharge the prerequisite.

The value boundary now discharges definedness prerequisites before definitional equality can erase them for `TyProof`, `TyBytes`, and recursively nested product/base types. The same check is applied when synthesizing a stored binding, before resource consumption. Refinement predicates remain on the existing binder-aware path: their base is checked first, the binder is instantiated with the concrete subject, and `dischargeProposition`/residualization checks the predicate's side conditions.

This keeps type definedness separate from inhabitance: `Proof[false]` and false refinements remain meaningful uninhabited types. The repair does not turn every proposition into a formation-time proof obligation, does not change Nat subtraction to truncation, and does not weaken sort checking.

## Permanent replay

`Phase1AuditTypeDefinednessCoreMain.hs` and `Phase1AuditTypeDefinednessSurfaceMain.hs` preserve the audit's regression/control corpus. The dedicated workflow runs the repaired cases and the existing value, refinement-evidence, focusing, discharge, and Surface conformance controls.

The key regression witnesses are:

- unsafe checked refinement source cannot canonicalize its false subtraction prerequisite away;
- the shape-matched safe `5 - 3` source still canonicalizes and accepts;
- direct `Proof[(3 - 5) == (3 - 5)]` ascription is rejected before definitional equality;
- `Bytes[0 * (3 - 5)]` is rejected before the zero scale can erase the invalid subtraction;
- symbolic subtraction remains residualizable rather than being blanket-rejected;
- the already-landed simultaneous transparent-claim substitution controls remain green.

## Assurance boundary

This remediation covers the implementation-side manifestations scoped by the audit event: Proof types, Bytes indices, primitive refinements, and recursive product/base checking at the value boundary. Dependent-session payload definedness and the separate nested-residual API/identity question remain broader follow-through; this change does not invent a universal residual-ID propagation rule for nested refinements.

The change does not establish Haskell/Rocq implementation correspondence, native/LLVM behavior, or proof completeness. Those remain in their existing lanes and assurance boundaries; LLVM remains inside the Phase 1 TCB.
