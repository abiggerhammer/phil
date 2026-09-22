# PHIL-AUD-ALPHA-SHADOW-001 remediation

## Finding

The Phase 1 audit found a soundness defect in the exposed Core definitional-equality boundary. `extendBinder` previously deleted a paired binder entry when either its left spelling or its right spelling was shadowed. If the other side of that pair was still live, its lexical identity was lost. `equalReferencedName` could then treat two formerly bound names as equally free merely because their source spellings matched.

The bounded counterexample compares two finite sessions whose final byte-length terms refer to different receive binders. The old paired environment loses both distinguishing `a` bindings after asymmetric shadowing and incorrectly reports the sessions equal. That result reaches `compareTypes`, `checkValue`, and `VAscribe` for endpoint values.

## Repair

`BinderEnv` now retains each side of a paired binder independently. Shadowing one spelling clears only that side of the older entry. An entry is removed only after both sides have been shadowed.

`equalReferencedName` therefore compares the positions of the surviving nearest bindings rather than allowing a one-sided live binder to disappear into the free-name case.

Fully shadowed entries are removed deliberately. This keeps the environment canonical when the same paired binder is encountered again and preserves the existing recursive-session seen-state termination strategy; simply retaining every historical pair would make the recurrence key grow without bound.

## Permanent replay

`test/Phase1AuditAlphaShadowMain.hs` carries Astra's A01-A08 obligations:

- the cross-shadow witness is not definitionally equal;
- endpoint comparison classifies it as incompatible;
- direct checking and ascription reject the retyping;
- legitimate nearest-binder shadowing remains alpha-equivalent;
- a real dependency mismatch remains unequal;
- ordinary alpha-renaming remains equal; and
- guarded recursive equality still compares a recursive session with one-step unfolding.

The audit driver imports only the exposed Core package modules. The dedicated workflow builds the full Haskell substrate, strict-typechecks the changed Core module, and runs the replay under `-Wall -Werror`.

## Assurance boundary

This closes only `PHIL-AUD-ALPHA-SHADOW-001` at the Core type/session equality and public value-checking/ascription boundary. It does not address the separate product definitional-equality completeness finding, refinement-subject visibility after consumption, Surface message-to-continuation binding, branch-evidence scope support, proof correspondence, native lowering, or final frozen-delta validation. No Certified status is promoted.
