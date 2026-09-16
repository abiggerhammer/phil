# FileSystem implementation refinement v1

`PHIL-P1-IO-FS-001` owns the semantic relationship between one checked FileSystem operation and the already-defined provider-relative Path / runtime-sized Bytes model.

## Certified seam

The Rocq model and executable correspondence certify the following FileSystem-owned facts:

- read admission is ordered by exact FileSystem occurrence, nonnegative caller bound, imported authority acceptance, then observed-outcome validation;
- successful reads require a semantic binding, exact returned bytes, and a binding length within the caller bound, in that order;
- `TooLarge` is admissible only when the semantic binding exists and exceeds the caller bound;
- `NotFound` is admissible only when the semantic binding is absent;
- other declared portable read negatives preserve FileSystem semantic state after the common preconditions;
- replace admission is ordered by exact FileSystem occurrence then imported authority acceptance;
- successful replace selects installation of the supplied binding; and
- failed replace selects exact preservation of the prior semantic state.

The production Haskell checker computes concrete facts and delegates the ordered verdict to the extracted `FileSystemKernel`.

## Imported predecessor boundaries

The following are deliberately imported rather than re-proved here:

- provider-relative Path identity and canonicality (`PHIL-P1-IO-PATH-001`);
- runtime-sized Bytes identity and length semantics (`PHIL-P1-IO-BYTES-001`);
- authority competence and possession checking;
- effect identity and occurrence indexing; and
- provider realization behavior outside the semantic state oracle.

## Native / realization boundary

The following remain native representation or realization facts:

- `Data.Map.Strict` representation and lookup/update correctness;
- Haskell `Int` representation and comparisons;
- concrete `RuntimeBytes` payload representation;
- the concrete authority checker and its detailed error payloads;
- typed diagnostic reconstruction;
- host filesystem calls and platform error translation;
- durability, crash consistency, fsync policy, atomic rename strategy, handles, directories, append, mmap, locks, and asynchronous I/O.

An extracted-kernel/native-fact disagreement fails closed as `FileSystemKernelInvariantViolation`; it never produces a checked FileSystem operation.
