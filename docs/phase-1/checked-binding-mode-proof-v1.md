# Checked Binding Mode proof v1

`PHIL-RES-BIND-MODE-001` closes the semantic gap between an already-checked
owning binding contract and concrete `ResourceContext` placement.

## Certified relation

`proof/Phil/Core/CheckedBindingMode.v` models the five ordinary binding origins
used by `Phil.Core.CheckedBindingMode` and a checked `(Ty, Mode)` contract.
A certified successful insertion requires all of the following:

1. the separately carried concrete type is exactly the checked type;
2. the separately carried concrete mode is exactly the checked mode; and
3. `Context.insertBinding` succeeds using the checked mode.

The existing `Context.insertBinding_success_exact` theorem then proves that the
new binding appears in exactly the checked unrestricted, affine, or linear zone
and in neither of the other two zones. Separate theorems show that a type
mismatch cannot certify, a mode mismatch cannot reclassify, and changing the
`BindingOrigin` cannot alter classification.

## Machine decision surface

`CheckedBindingModeImplementation.v` extracts a three-Boolean success gate:

- checked type matches;
- checked mode matches;
- context insertion accepts.

The extraction does not replace the detailed Haskell diagnostics. A production
binding must continue to run `Phil.Core.CheckedBindingMode.insertCheckedBinding`
first and may only add fail-closed rejection on kernel disagreement.

## Explicit boundaries

This proof does **not** derive a mode from an arbitrary Phil type. The competent
type/resource checker that constructs `CheckedTypeMode` remains the authority
for that prior semantic judgment. It also does not change duplicate-binding
semantics, prove Haskell `Eq` correctness, prove `Data.Map.Strict` correctness,
or certify every future source/elaboration binding site. Concrete Haskell/Rocq
representation correspondence, extraction/toolchain correctness, and production
binding of the exact extracted kernel remain separate obligations.
