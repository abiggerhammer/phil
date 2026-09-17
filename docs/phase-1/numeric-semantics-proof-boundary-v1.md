# PHIL-EXEC-ARITH-001 proof boundary

This slice certifies the Phase-1 exact numeric execution contract without claiming
that Rocq reimplements the concrete Haskell arithmetic or IEEE bit engine.

## Certified semantic surface

The proof records the following Phase-1 requirements.

- Plain fixed-width integer arithmetic is mathematical arithmetic.  A closed,
  correctly typed, exact, representable result may be established directly.
  A symbolic result remains an explicit proof obligation.  Wrong-width,
  mismatched, or out-of-range closed results reject rather than wrap,
  saturate, trap, or silently coerce.
- Checked fixed-width integer arithmetic exposes out-of-range behavior as an
  explicit typed-negative source outcome.  Invalid operands reject at the
  competence boundary.
- Signed division success requires a nonzero divisor, truncation toward zero,
  the paired remainder relation, and a representable exact result.  Signed
  right shift remains a different operation: arithmetic floor division by a
  power of two.
- F32/F64 execution retains exact source format/width identity,
  round-to-nearest-ties-to-even, gradual underflow, signed zero, NaN/Infinity,
  and rejects reassociation, contraction, flush-to-zero, and approximate
  arithmetic.
- Numeric-domain changes occur only through explicit conversion.  Partial
  conversion failures (including fractional/nonfinite float-to-integer and
  out-of-range conversions) remain explicit; no implicit coercion is created.
- Fixed-width shifts require a valid width, 0 <= count < width, in-range source
  operands, representable left-shift results, exact right-shift semantics, and
  no masked counts or discarded high bits.
- Target realization additionally rejects width/rounding drift, wrap,
  saturation, trap/poison substitution, ambient casts, float weakenings,
  signed-zero/NaN/Infinity erasure, loss of gradual underflow, and masked shifts.

## Production authorities retained

The concrete authorities remain:

- `Phil.Core.UIntArithmetic` and `Phil.Core.CheckedUIntArithmetic`;
- `Phil.Core.SIntArithmetic`;
- `Phil.Core.IntegerDivision`;
- `Phil.Core.FloatArithmetic`;
- `Phil.Core.NumericConversion`;
- `Phil.Core.IntegerShift`;
- the Grammar-v1 runtime/scalar/arithmetic/conversion bridges; and
- StageContract / realization checking for target preservation.

The Rocq finite correspondence layer does not replace concrete Integer
calculation, IEEE interchange-bit construction, decimal parsing/rounding,
Haskell Map/Set/Text representations, source elaboration, or target execution.

## Explicit boundaries / TCB

Still explicit:

- correctness of concrete Haskell Integer and Word64 operations used by the
  production implementation;
- the correspondence between Grammar-v1 checked terms and the concrete numeric
  authority selected for them;
- exact StageContract identity/serialization and target-profile facts;
- GHC/runtime correctness;
- Rocq/toolchain correctness; and
- backend/toolchain/target execution correctness beyond the checked realization
  relations.

Bitwise operations and wrapping/saturating arithmetic remain separately gated
features and are not introduced by this proof.
