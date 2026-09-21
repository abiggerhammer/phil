# R1 follow-up: concrete LLVM identifier encoding

## Audit source and scope

This implementation slice addresses the remaining R1 defect from **Phil Phase 1
follow-up audit — 2026-09-20 — 4cf858f**, after the cumulative provider repair
landed as PR #1247. The audit's executed counterexamples were accepted ordinary
source names whose concrete LLVM spellings either collided (`x'` versus
`x_`) or remained non-ASCII unquoted identifiers (`café`, `α`).

The earlier R1 proof and implementation correctly separated source-derived,
synthetic, and block-label namespaces. Its proof boundary explicitly excluded
concrete Text sanitization and LLVM toolchain behavior. This slice repairs that
implementation boundary without changing the theorem or claiming that a Haskell
encoding routine has become proof-certified.

## Encoding rule

Only the source-identifier component used by the ordinary runnable compiler is
changed. `sourceScalarValueId` now applies an injective ASCII encoding before
constructing the Systems `ValueId`:

- ASCII letters and digits keep their spelling;
- `_` becomes `__`;
- every other Unicode scalar value becomes `_u<decimal-code-point>_`.

Doubling underscore is important. It prevents a literal source spelling such as
`x_u39_` from impersonating the encoding of `x'`. The result contains only
ASCII letters, digits, and underscores, so the existing stable LLVM sanitizer
does not lose information in this source-derived component and cannot pass
Unicode through into an unquoted target identifier.

This deliberately does **not** globally rename runtime or linker-visible ABI
symbols. Existing runtime spelling remains under the already established ABI
mapping and tests.

## Concrete final check

`compileRunnableForTarget` now checks the rendered artifact before returning
it. For the currently supported runnable fragment (one function, no
parameters), it collects all function-local SSA definitions and block labels
from the actual emitted text and rejects:

- duplicate local definitions; or
- local names outside LLVM's unquoted ASCII identifier grammar.

This check is intentionally concrete and downstream of rendering. It prevents a
future regression in identity construction or sanitization from returning an
artifact with the same class of malformed local namespace even if abstract
identity checks still pass.

## Regression corpus

The permanent R1 corpus now covers:

- the original source/synthetic `return_value_0` pressure case;
- the original source/block `entry` case;
- `x'` versus `x_`;
- accepted `café` and `α` bindings;
- the escape-looking source spelling `x_u39_` versus encoded apostrophe;
- a source spelling resembling `synthetic_return_value_0`;
- duplicate-definition and ASCII-legality checks over the emitted text.

The existing ordinary runnable regression is retained.

The R1 workflow additionally resolves the project LLVM 18 assembler, compiles
the adversarial sources through the public `philc emit-llvm --target
x86_64-unknown-linux-gnu` command, and requires `llvm-as` to accept each
emitted artifact. This closes the gap between a Haskell string assertion and
the actual LLVM parser that the target profile declares.

## Assurance boundary

At authoring, the branch has not yet completed CI. No local GHC, Cabal, Rocq, or
LLVM execution is claimed here.

This is an implementation remediation. The existing R1 Rocq artifacts continue
to certify namespace separation at their documented abstraction boundary; they
are not relabeled as proofs of this concrete encoding routine. External ABI
mapping, GHC/runtime behavior, and LLVM 18 remain explicit trusted/tool
boundaries. R10/R16 and R17/R18 remain separate audit repairs.
