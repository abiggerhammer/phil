# Runtime Bytes implementation refinement v1

`PHIL-P1-IO-BYTES-001` is Certified by `proof/Phil/Core/RuntimeBytes.v` and its executable correspondence is defined by `proof/Phil/Core/RuntimeBytesImplementation.v`.

The owned executable surface has two decisions:

- `decideBytesCheckByFacts` orders exact-index forgetting, definitional equality, same-Bytes-family explicit transport, and incompatibility.
- `decideRuntimeBytesRefinementByFacts` orders runtime-source recognition, exact-target recognition, value-subject visibility, and accepted exact length evidence.

Production representation remains native. `Ty`, `RefTerm`, the source-unspellable runtime-size marker, proposition discharge, and resource-context operations are not extracted. Generic explicit state transport remains owned by the already production-bound `ResourceLoopKernel`.

Implementation refinement closes only when the freshly extracted `RuntimeBytesKernel.hs` is byte-identical to the checked-in production kernel and the production `Phil.Core.Value` path routes these Bytes-specific decisions through it while the unchanged IO-BYTES corpus remains green.
