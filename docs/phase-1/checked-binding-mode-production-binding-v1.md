# Checked Binding Mode production binding v1

`PHIL-RES-BIND-MODE-001` is Certified by `proof/Phil/Core/CheckedBindingMode.v` and its three-fact executable correspondence from #727.

This production binding preserves the existing `Phil.Core.CheckedBindingMode.insertCheckedBinding` competence order:

1. supplied type must equal the checked type;
2. supplied mode must equal the checked mode;
3. `Phil.Core.Context.insertBinding` must accept using the checked mode.

Only after those native checks succeed does production reflect the same three facts into the exact Rocq-extracted `CheckedBindingModeKernel.decideCheckedBindingModeByFacts`. The context fact is independently recomputed by rerunning `insertBinding` and requiring its returned `ResourceContext` to equal the native successor. Native diagnostics therefore retain precedence, while any native-success/kernel-reject disagreement fails closed as `CheckedBindingKernelDisagreement`.

`BindingOrigin` remains diagnostic/accounting metadata and does not enter the kernel decision. Exact zone placement remains inherited from the already proved `Context.insertBinding_success_exact` theorem.

The checked-in `generated/CheckedBindingModeKernel.hs` and `src/CheckedBindingModeKernel.hs` must be byte-identical to fresh Rocq 9.2 extraction from `CheckedBindingModeImplementationExtraction.v`. The production workflow checks the exact 463-byte file and SHA-256 `0a43d3a9d61b0887451b13ec3bb3410ccd898086321fc6d2ee026da11e86fbd9`.

## Retained boundaries

This binding does not prove the intrinsic/prelude type-to-mode table itself. The soundness of each type/resource contract's checked mode remains an imported checked fact. Concrete Haskell `Ty`/`Mode` equality, `ResourceContext`/`Map` representation, source elaboration preserving the checked type, Rocq extraction/toolchain correctness, GHC/runtime correctness, and the ordinary semantics of the concrete host containers remain explicit boundaries.
