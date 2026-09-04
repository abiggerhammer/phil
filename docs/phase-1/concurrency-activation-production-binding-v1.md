# Phase 1 concurrency activation production binding v1

`PHIL-CONC-ACTIVATE-001` is Certified by `proof/Phil/Core/ConcurrencyActivation.v`. PR #685 staged a representation-neutral machine decision surface in `ConcurrencyActivationImplementation.v` and extracted it to Haskell. This production-binding slice composes the existing native activation and participant checkers with that exact extracted kernel rather than replacing their concrete validation or diagnostics.

## Exact kernel identity

The production kernel is the exact artifact extracted by the green #685 staging run:

- source: `proof/Phil/Core/ConcurrencyActivationImplementation.v`;
- extraction entrypoint: `proof/Phil/Core/ConcurrencyActivationImplementationExtraction.v`;
- extracted module: `ConcurrencyActivationKernel.hs`;
- SHA-256: `344a132a263ba0f0c2821f35e03257ea74c49ced652d28938d11accffe09c063`;
- size: 2066 bytes;
- trailing bytes: exactly two newline bytes.

The dedicated workflow freshly extracts the module with Rocq 9.2.0, checks its SHA-256 and size, and byte-compares it against both `generated/ConcurrencyActivationKernel.hs` and `src/ConcurrencyActivationKernel.hs`.

## Native-first activation binding

`activateProcessStateCertified` first calls the existing `activateProcessState`. Every native error therefore retains precedence and its exact diagnostic identity. Only native success is reflected into the kernel-facing facts.

Because `ProcessNetwork` constructors are public and the broader `PHIL-CONC-SEM-001` obligation is still Certified rather than implementation-refined, successful native activation is not treated as a proof that the `StaticPopulationValid` predecessor field is true. The production bridge independently checks the concrete population/activation facts required by `ActivationContextValid`:

- the input population is nonempty;
- the root identity is unchanged;
- pre/post population domains are exactly equal;
- each map key equals the contained `processOccurrenceKey` and is nonempty;
- each input occurrence is `NotActivated` and each output occurrence is `Active`;
- all static occurrence fields are preserved across activation;
- every binding has an explicit, non-ambient origin and names an activated process;
- every restricted binding has exactly the reflected restricted owner, and every reflected restricted owner is explained by such a binding;
- every direct-stateful binding has exactly the reflected process owner, and every reflected direct-stateful owner is explained by such a binding.

The leaf ownership gates and the complete seven-field activation-context gate are all evaluated. Any native-success/kernel-reject outcome fails closed with the reflected facts retained in the certification error.

## Native-first participant binding

`checkParticipantClassificationsCertified` first calls the existing `checkParticipantClassifications`. Duplicate, missing, unexpected, unknown, ambiguous, unactivated, inactive, and root-mismatch diagnostics therefore remain native authority.

On native success the bridge independently reflects:

- exact expected-role coverage and uniqueness;
- exact checked-role identity in every map entry;
- every internal participant naming an existing active process;
- every internal participant naming the exact static process target;
- absence of the concrete empty-role sentinel.

The normalized Rocq model represents the impossible empty role as key `0`. The concrete correspondence used here is `ProtocolRoleOccurrence (ProtocolInstanceRevision "") (ProtocolRoleKey "")`. This encoding choice is an explicit Haskell correspondence boundary, not a new theorem about protocol-role serialization.

External participant classification remains deliberately narrow: it does not acquire transport, BoundaryRepresentation, entry, authority, assurance, export, or realization competence.

## Certified composition

`certifyConcurrencyActivation` performs certified activation, then certified participant classification over the resulting active network, then evaluates `decideCertifiedConcurrencyActivationByFacts True True`. The outer gate therefore composes two independently checked successful components; it does not reconstruct either component from a single aggregate success bit.

The production harness includes native-diagnostic precedence cases, direct disagreement injection, a malformed map-key/occurrence-key case, an empty native population that reaches native success but fails the kernel gate, and an empty role sentinel that reaches native participant success but fails the kernel gate.

## Retained boundaries

This binding does not certify concrete `ProcessKey` persistence/serialization, source-to-architecture `ProcessOccurrence` extraction, source binding extraction, `Map`/`Set`/`Text` implementation correctness, unrestricted-wrapper graph traversal, protocol-role occurrence serialization, GHC correctness, or runtime correctness. Those remain explicit implementation/tooling assumptions or later refinement obligations.

It also does not promote the broader `PHIL-CONC-SEM-001` aggregate. That row remains Certified. A green exact-head merge of this production binding is sufficient only to promote `PHIL-CONC-ACTIVATE-001` to **Implementation Refined** and reconcile CONC-001, CONC-002, CONC-003, CONC-010, and CONC-011 with the exact production evidence.
