# PHIL-P1-REVIEW-R09 proof boundary

This slice certifies Astra Review R09: floating-zero output must be classified as an exact conversion **only when the exact finite source value was zero**.

That distinction matters because two semantically different paths can produce the same target zero bit pattern:

- exact integer zero converted to F32/F64 is exact and yields positive zero;
- a nonzero value that rounds or underflows to zero is rounded, not exact.

The proof also records the separate floating-zero class conversion rule:

- positive zero converted across float widths remains exact positive zero;
- negative zero converted across float widths remains exact negative zero; and
- signed-zero sign drift is not an exact signed-zero conversion.

For ordinary nonzero finite conversions, precision continues to be controlled by exact rational equality between the rounded target value and the exact source value.

This slice composes with `PHIL-EXEC-ARITH-001`, which continues to own strict F32/F64 identity, round-to-nearest-ties-to-even, gradual underflow, and signed-zero semantics. R09 does not reimplement IEEE rounding; it certifies the conversion-result precision classification around zero.

The concrete Haskell correspondence is `Phil.Core.NumericConversion.convertFiniteToFloat`. After exact decimal rendering and strict target rounding, it classifies the result:

- `FloatFinite roundedValue` is exact iff `roundedValue == exactValue`;
- `FloatPositiveZero` and `FloatNegativeZero` are exact iff `exactValue == 0`;
- otherwise the finite conversion is rounded.

Float-to-float zero-class conversion is handled separately by `convertFloatClass`, which maps positive/negative zero to the same zero class in the target format and marks it `NumericConversionExact`.

The permanent R09 regression checks UInt and SInt zero into both F32/F64, a representative exact integer conversion, a representative rounded integer conversion, nonzero F64-subnormal underflow to F32 zero, and negative-zero width conversion with sign preservation. The dedicated gate also replays the full EXEC-020 numeric conversion regression.

Concrete rational/decimal rendering, exact IEEE bit construction, Haskell `Integer` and `Word64` behavior, GHC/runtime correctness, and Rocq/toolchain correctness remain explicit implementation boundaries.
