# Console implementation refinement v1

This note records the semantic-certification boundary for `PHIL-P1-IO-CONSOLE-001`.

## Owned semantic surface

`proof/Phil/Core/Console.v` certifies the representation-neutral console facts reflected by `src/Phil/IO/Console.hs`:

- one console provider occurrence has exact occurrence identity and provider kind;
- input and output occurrences cannot collapse merely because a representation happens to coincide;
- input permits `read_line` only, while output permits `write` and `flush` only;
- the default authority mode reuses the existing structural algebra: input is `Linear`, output is `Affine`;
- an accepted line read is caller-bounded;
- EOF and typed portable read failures are ordinary accepted outcomes once operation/authority preconditions hold;
- a successful write makes the full request observable;
- a failed write carries an exact observable prefix whose length cannot exceed the request; and
- flush is an output-provider operation.

`proof/Phil/Core/ConsoleImplementation.v` mirrors the finite decision order used by production:

- occurrence construction rejects the empty key;
- operation-kind compatibility is checked before operation execution;
- read/write/flush kind legality precedes imported authority acceptance;
- line bounds are checked only for line outcomes;
- failed-write progress range is checked only for failed writes; and
- successful versus failed write selects full-request versus reported-prefix observability.

## Imported predecessors

This proof does not introduce a second authority or effect model. Authority possession and operation permission remain imported from the already-certified authority-possession path. Effect identity/permission remains an imported callable/effect predecessor. The structural `Mode` constructors come directly from `GenericStructural.v`.

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

The next implementation-refinement step may extract only the finite decision surface from `ConsoleImplementation.v` and production-bind those verdicts without moving the native boundaries above into the trusted semantic kernel.
