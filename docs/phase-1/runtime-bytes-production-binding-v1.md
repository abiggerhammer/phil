# Runtime Bytes production binding v1

The production decision kernel is `src/RuntimeBytesKernel.hs`, freshly extracted from `proof/Phil/Core/RuntimeBytesImplementationExtraction.v`.

Exact SHA-256:

`c8d05c29a23b66af9fa45b9d2f413d5b2f02ab904e80b04233ca05a49e261430`

`Phil.Core.Value` supplies concrete facts to the extracted kernel. For ordinary value checking, the kernel owns the order:

1. exact `Bytes[n]` to runtime-sized `Bytes` forgetting;
2. definitional equality;
3. nondefinitional same-family explicit transport;
4. incompatibility.

For runtime-sized `Bytes` to exact `Bytes[n]`, the kernel owns the order:

1. source is runtime-sized Bytes;
2. target is exact Bytes;
3. the value subject is visible;
4. exact length evidence was accepted.

After the Bytes-specific gate accepts, generic explicit transport remains checked by the existing extracted `ResourceLoopKernel`. Concrete type representation, equality facts, proposition construction/discharge, resource ownership mechanics, diagnostics, Rocq extraction, GHC, and runtime correctness remain explicit trusted/native boundaries.

The production-binding workflow regenerates the kernel, byte-compares it with `src/RuntimeBytesKernel.hs`, checks the pinned digest, runs direct extracted-kernel controls, typechecks the production authority under `-Wall -Werror`, and reruns the unchanged IO-BYTES pressure corpus.
