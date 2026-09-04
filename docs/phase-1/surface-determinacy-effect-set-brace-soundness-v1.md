# Phase 1 surface determinacy: effect-set brace soundness v1

This slice continues `PHIL-SURFACE-DETERM-001` after the refinement-type brace commitment.

The brace-led `static_argument` overlap has two semantic sides:

- `refinement_type` begins `{ IDENTIFIER :` and commits static-argument branch 0;
- `effect_set_literal` begins either `{ }` or a nonempty effect expression and must commit branch 3.

`proof/Phil/Surface/GrammarDeterminacyEffectSetBraceSoundness.v` connects the second case to arbitrary ordinary Grammar-v1 derivations. It proves that a nonempty effect expression begins with a qualified static reference and classifies the token immediately after its first identifier as one of:

- `.` for a continued qualified name;
- `[` for static arguments;
- `(` for term arguments;
- `,` for another effect; or
- `}` for the end of the set.

None of those tokens is `:`, so the structural brace resolver cannot confuse a derived effect set with a refinement type. Empty `{}` is handled directly by the existing structural-scanner theorem.

The result is implementation-independent: it is derived from ordinary `Derives` evidence over the generated Grammar-v1 tree and then composed with the certified structural resolver.

After this slice, the remaining structural-overlap semantic families are parenthesis comma/close commitments and proposition-atom top-level relation commitments.
