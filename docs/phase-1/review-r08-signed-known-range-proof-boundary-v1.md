# PHIL-P1-REVIEW-R08 proof boundary

This slice certifies Astra Review R08: every raw known fixed-width signed term must be range-valid **before** plain arithmetic or plain division may either establish a result or emit a residual proof obligation.

The central rule is a preflight boundary. For each raw signed operand/result, exact type identity and fixed-width signed range validity are checked before the checker inspects the known-vs-symbolic combination. Consequently:

- a malformed known left operand rejects immediately;
- a malformed known right operand rejects immediately;
- a malformed known result rejects immediately;
- a malformed known term cannot be converted into a proof obligation merely because another term is symbolic; and
- valid exact boundary values remain admissible.

The normalized signed range is the existing half-open fixed-width interval: positive width, value at or above the signed minimum, and value strictly below the exclusive maximum. The exact concrete I8 boundary cases `-128` and `127` remain executable correspondence tests.

This slice composes with `PHIL-EXEC-ARITH-001`, which already owns exact mathematical arithmetic, representability, and fail-closed rejection of out-of-range known results. R08 adds the missing ingress-order guarantee: raw known terms themselves are validated before residualization.

The concrete Haskell correspondence is direct:

- `checkPlainSIntArithmetic` validates width, then calls `checkTerm` on left, right, and result before entering the `knownValue` case that may return `PlainSIntArithmeticRequiresProof`;
- `checkPlainSIntDivision` follows the same pattern with `checkSIntTerm` before its `knownSInt` case may return `PlainSIntDivisionRequiresProof`;
- both term checkers reject `SIntKnown` values for which `sIntLiteralInRange` is false;
- checked signed division independently rejects malformed raw operand literals; and
- numeric conversion independently rejects malformed signed source values.

The permanent 11-case R08 regression pressures malformed left/right/result terms, malformed-known-before-proof behavior in both arithmetic and division, exact I8 minima/maxima, checked-division raw ingress, and conversion raw ingress. The dedicated gate also replays the existing signed arithmetic, integer-division, conversion, and shift controls.

Concrete Haskell `Integer` arithmetic, type/text representation, obligation construction, diagnostic ordering, GHC/runtime correctness, and Rocq/toolchain correctness remain explicit implementation boundaries.
