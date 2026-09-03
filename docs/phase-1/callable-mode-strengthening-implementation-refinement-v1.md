# Callable Mode Strengthening implementation refinement v1

`PHIL-CALL-MODE-STRENGTHEN-001` is already Certified by the Rocq model in `CallableModeStrengthening.v`. This staging tranche makes the representation-neutral decision seam executable without changing production Haskell behavior.

## Extracted seam

`CallableModeStrengtheningImplementation.v` owns two executable decisions.

For an explicit closure-mode declaration, `decideExplicitClosureModeByFacts` preserves the production rejection precedence:

1. weakening the capture-derived minimum rejects;
2. an explicit mode equal to the minimum accepts without inspecting strengthening authority;
3. strict strengthening without a justification rejects;
4. target-implementation-only reasons reject;
5. a justification bound to the wrong callable contract rejects;
6. an empty semantic justification rejects; and
7. an exact nonempty lifecycle or authority justification may admit strict strengthening.

`decideCheckedClosureModeShapeByFacts` postchecks that the Certified minimum, selected mode, and justification identities are preserved in the checked result. The Certified proof shows that valid derived and explicit declarations supply those exact shape facts.

## Explicit native boundary

This kernel does not own:

- closure capture discovery or the Certified predecessor that derives the capture minimum;
- concrete Haskell `Mode` representation or `modeRank`/`modeLe` correspondence;
- `InterfaceRevision` or `Text` equality;
- deciding whether a lifecycle/authority obligation is actually true or competent;
- source elaboration;
- diagnostic payload construction or ordering outside this decision seam;
- preservation of the concrete `ClosureCaptureSummary` field in the Haskell checked value; or
- Haskell/GHC/runtime correctness.

The extracted decision can later be used only as a fail-closed production gate: it may force rejection on disagreement, but it may not convert a native rejection into acceptance.

## Staging criterion

The staging workflow must freshly compile the Certified predecessor and implementation correspondence, extract `CallableModeStrengtheningKernel.hs`, strictly typecheck and execute the 14 direct kernel controls, strictly typecheck the unchanged production implementation, and rerun the unchanged eight-case CALL-017 corpus.

A green staging merge records executable correspondence evidence but leaves `PHIL-CALL-MODE-STRENGTHEN-001` at `Discharged / Certified`. Promotion to `Implementation Refined` requires a later exact-kernel production binding.
