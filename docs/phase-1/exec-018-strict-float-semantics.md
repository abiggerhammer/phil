# EXEC-018 strict floating semantics

This note records the bounded Haskell semantic authority introduced for EXEC-018.

- `F32` and `F64` are distinct Phil semantic types with exact IEEE interchange bit patterns.
- Decimal literals are interpreted as exact rationals and rounded directly to the declared format using round-to-nearest, ties-to-even.
- Finite values, subnormals, infinities, NaNs, and signed zero are classified from exact bits; Haskell `Float` and `Double` are not semantic authorities.
- Ordinary `+`, `-`, `*`, and `/` use the declared strict floating contract, including explicit special-value behavior and gradual underflow.
- Comparisons preserve NaN unorderedness and signed-zero equality semantics.
- Realization requires exact storage width, round-to-nearest/ties-to-even, gradual underflow, and absence of silent reassociation, contraction, NaN/Inf assumptions, signed-zero weakening, flush-to-zero, or approximate arithmetic.

This Core authority is only the first half of EXEC-018. Grammar-v1 source composition is a separate follow-up slice, and the Matrix remains Planned until that composition lands.
