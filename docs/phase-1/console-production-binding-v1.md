# PHIL-P1-IO-CONSOLE-001 — production binding

This closeout mechanically binds the already-Certified Console decision semantics to the existing production `Phil.IO.Console` APIs.

## Exact staged kernel

PR #1264 staged `ConsoleImplementationExtraction.v` and produced the exact green Rocq 9.2 extraction:

- file: `ConsoleImplementationKernel.hs`
- size: **3,231 bytes**
- SHA-256: `81c1216233a1d14390d1b78d469664bf6416dbf3e3fe6ed4e3bfffcc67104093`
- staging artifact: `rocq-console-proof`
- staging artifact ID: `10642532009`
- artifact digest: `sha256:4cf25dfb77de62c88ebb44b15d0c9cb35d451e929f84eb0bd05fc9738f2237f1`

`generated/ConsoleImplementationKernel.hs` and `src/ConsoleImplementationKernel.hs` are byte-identical copies of those extracted bytes. The production-binding workflow freshly re-extracts the kernel and refuses size, digest, or byte drift.

## Native-first production binding

The existing exported Console APIs retain their native competence and diagnostics.

### Occurrence construction

`consoleInputOccurrence` / `consoleOutputOccurrence` still reject an empty `Text` key first. Only native nonempty success is reflected into `decideConsoleOccurrenceByFacts`. Kernel disagreement can add rejection but cannot turn the native empty-key error into acceptance.

### Operation admission

`checkOperationKind` retains the exact existing provider-kind/operation diagnostic. Native legal cases are independently reflected as a Boolean compatibility fact and must be accepted by `decideConsoleOperationByFacts`. Because authority-capability construction and operation contracts both use `checkOperationKind`, they share the same production-bound gate.

### Reads

`checkConsoleReadLine` preserves this order:

1. native operation contract;
2. native authority possession/permission;
3. native successful-line length bound;
4. extracted read-decision agreement;
5. unchanged `CheckedConsoleRead` construction.

EOF and typed provider failures remain accepted outcomes after preconditions exactly as before.

### Writes

`checkConsoleWrite` preserves this order:

1. native operation contract;
2. native authority possession/permission;
3. native requested-length / failed-prefix range validation;
4. extracted success-vs-prefix selector agreement;
5. extracted write-decision agreement;
6. unchanged observable-prefix/result construction.

The kernel therefore cannot erase an impossible prefix or change the externally observable prefix chosen by production.

### Flush

`checkConsoleFlush` preserves native operation and authority checks before requiring extracted flush-decision agreement.

## Fail-closed disagreement

New `ConsoleCheckError` disagreement constructors are reachable only after the corresponding native layer has succeeded. They are not aliases for existing user errors and cannot upgrade native rejection.

## Permanent evidence

The production-binding workflow:

- freshly compiles/extracts the Certified Console proof chain under Rocq 9.2;
- requires the exact 3,231-byte / SHA-256 kernel;
- byte-compares fresh extraction against both checked-in copies;
- replays all 20 direct extracted-kernel controls;
- strict-typechecks and runs the production-binding harness;
- replays the unchanged Console provider corpus and authority-possession predecessor corpus; and
- records exact production identities as a retained artifact.

A fully green exact-head merge permits `PHIL-P1-IO-CONSOLE-001` to move from **Active / Certified** to **Discharged / Implementation Refined**.

## Retained boundaries

Concrete `Text`/Unicode scalar behavior, `Natural`, provider/effect identity encodings, authority-state correctness, host console handles, buffering, line endings, locale/text encoding, Rocq extraction/toolchain correctness, GHC/runtime correctness, and actual terminal/provider realization remain explicit native or TCB boundaries.
