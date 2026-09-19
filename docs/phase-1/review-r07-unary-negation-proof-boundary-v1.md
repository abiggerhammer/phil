# PHIL-P1-REVIEW-R07 proof boundary

This slice certifies Astra Review R07: unary negation is an explicit source operator, not a sign folded into a numeric token and not a special case of binary subtraction.

The proof has two layers.

The syntax layer certifies that:

- `-` and the following decimal magnitude remain separate lexical units;
- a negative literal is represented by a unary-negation AST node over the positive magnitude;
- unary negation is available at unary precedence inside multiplicative expressions;
- repeated unary negation composes structurally; and
- binary subtraction remains a distinct AST constructor.

The numeric layer composes that source route with the already-certified `PHIL-EXEC-ARITH-001` authority:

- signed integer negation succeeds only when the exact result is representable, and rejects otherwise rather than wrapping;
- floating negation remains under the strict F32/F64 profile, including signed-zero preservation; and
- UInt negation has no success case and rejects rather than wrapping or silently coercing.

The concrete Haskell correspondence spans the existing production authorities:

- `Phil.Surface.GrammarV1.Lexer` emits `GrammarSymbol "-"` separately from `GrammarDecimalInteger`;
- `parseUnaryExpression` recursively builds `GrammarV1NegateExpression`, giving unary precedence and repeated-negation composition;
- the ordinary additive parser retains binary `GrammarV1Subtract`;
- `evaluateGrammarV1NumericExpression` recursively evaluates the operand and dispatches negation by exact semantic numeric domain;
- SInt negation checks `sIntLiteralInRange`;
- Float negation delegates to `negateFloatValue`; and
- UInt negation returns `GrammarV1NumericNegationUnsupported`.

The permanent R07 regression covers lexical separation, unary AST shape, the I8 minimum, variable and parenthesized negation, repeated negation, multiplicative precedence, floating signed zero, repeated floating zero, UInt rejection, and binary subtraction control. The dedicated gate also replays the signed-integer, float, and integer-division controls.

Concrete token spans, parser recursion implementation, contextual type selection, Haskell Integer/IEEE representation, decimal parsing, exact float bit construction, GHC/runtime correctness, and Rocq/toolchain correctness remain explicit implementation boundaries.
