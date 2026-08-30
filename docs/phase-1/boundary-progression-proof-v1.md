# Phase 1 typed boundary progression proof v1

Obligation: `PHIL-BND-PROGRESS-001`

This note records the bounded Rocq certification for BND-011. The proof is intentionally about **progression gates**, not transport implementation.

## Certified receive-side claims

Starting from an already-established parsed witness and boundary correspondence witness:

- typed receive progression can succeed only when the parsed grammar identity exactly matches the correspondence grammar identity;
- the parsed grammar-value identity must exactly match the correspondence source-value identity;
- the underlying certified receive/session step must itself advance;
- grammar or source-value mismatch cannot be laundered into a successful typed receive progression.

The establishment of the parsed witness already depends on framed, complete recognition (`PHIL-BND-COMPLETE-001`); this proof does not duplicate that predecessor theorem.

## Certified send-side claims

Starting from already-established qualified generated-encoding evidence:

- invalid, partial, or past-declared-frame emission classification cannot establish complete-emission evidence;
- complete emission evidence carries exactly the generated representation revision and exact output-owner identity;
- typed send progression can succeed only when generated evidence and completion evidence agree on both representation revision and output owner;
- the underlying certified protocol/session send step must itself advance;
- representation or owner mismatch cannot be laundered into successful typed send progression.

## Explicit residual boundary

This proof does **not** mechanize the concrete Haskell `Int` arithmetic that classifies transport extents, integer overflow behavior, byte-count observation, transport-provider completion truth, actual wire I/O, concrete `Name` / representation equality, error reconstruction, or Haskell implementation equivalence. Those remain provider/target or implementation-correspondence boundaries unless separately mechanized.

The semantic proof models completion classification as an already-observed disposition (`invalid`, `partial`, `complete`, or `past`). This is deliberate: BND-011 certifies that only the `complete` disposition may mint the evidence needed for send progression; it does not certify how a particular transport backend determines that disposition.

## Correspondence corpus

The dedicated workflow typechecks the unchanged production path `src/Phil/Core/BoundaryProgression.hs` and the unchanged `test/Phase1BoundaryProgressionMain.hs`, then reruns all four BND-011 cases:

1. exact mapped receive advances;
2. mismatched mapping rejects before receive progression;
3. partial transport emission rejects before send progression;
4. complete qualified emission advances send.
