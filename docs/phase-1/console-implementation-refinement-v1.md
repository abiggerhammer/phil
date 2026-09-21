# PHIL-P1-IO-CONSOLE-001 — implementation refinement staging

This slice stages mechanical implementation refinement for the already-Certified explicit Console semantics. It does not change production `Phil.IO.Console` behavior.

## Certified predecessor

`proof/Phil/Core/Console.v` already owns the semantic claims for:

- distinct console occurrence identity and input/output provider kind;
- legal operation/kind pairs;
- Linear stdin and Affine output default authority modes;
- bounded accepted line reads;
- explicit EOF/provider-failure read outcomes;
- exact successful-write observability;
- exact in-range partial-write progress on failure; and
- output-only flush/write semantics.

`ConsoleImplementation.v` owns the concrete finite decision order reflected by the current Haskell checker. This staging pass adds acceptance-iff-facts theorems for every extracted gate.

## Extracted decision surface

`ConsoleImplementationExtraction.v` extracts six executable functions into `ConsoleImplementationKernel.hs`:

1. occurrence non-emptiness;
2. provider-kind/operation compatibility;
3. read admission/order;
4. write admission/order;
5. successful-vs-partial write observable-length selection; and
6. flush admission/order.

The kernel takes only Boolean/finite facts already established by native production operations. It does not reimplement Text, Natural, authority-state lookup, provider identity, effects, diagnostics, or observed host I/O.

## Staging evidence

The permanent `Phase 1 IO Console Proofs` workflow now:

- compiles the Certified semantic proof and strengthened implementation proof under Rocq 9.2.0;
- freshly extracts `ConsoleImplementationKernel.hs`;
- records the exact extracted bytes with the proof artifact;
- compiles and runs 20 direct extracted-kernel controls under `-Wall -Werror`; and
- replays the unchanged Console provider and authority-possession corpora.

This staging PR deliberately does **not** check the kernel into `src/` or route production acceptance through it.

## Native / realization boundary

The following remain concrete implementation or realization facts:

- `Text` occurrence keys and their empty/equality behavior;
- concrete console interface revision strings;
- `Text.length` scalar counting and `Text.take` prefix construction;
- `Natural` representation;
- authority-state lookup and detailed authority diagnostics;
- effect/authority string encoding;
- accepted Haskell record reconstruction;
- POSIX/WASI/Windows handles and terminal behavior;
- text encoding, locale, line-ending conventions, buffering, and provider realization.

## Next tranche

Production binding will harvest the exact green extracted kernel, check byte-identical copies into `generated/` and `src/`, and wrap the existing Console checker native-first:

- preserve existing diagnostic order;
- reflect only native-success facts into the extracted kernel;
- reject any native-success/kernel-reject disagreement; and
- retain current concrete result construction unchanged.

Only that later fully green production-binding closeout can promote `PHIL-P1-IO-CONSOLE-001` from **Certified** to **Implementation Refined**.
