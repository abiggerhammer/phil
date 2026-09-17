# Phase 1 verification producer proof boundary v1

`PHIL-VERIFY-PRODUCER-001` certifies the proof-producer / competent-evidence-checker separation implemented by VER-003, VER-004, VER-005, and VER-011.

## Certified semantic boundary

The proof fixes the discharge target before proof search begins. A replaceable producer may propose a certificate or fail to produce one, but producer success is never proof authority by itself.

A proposal can become checked evidence only when all of the following hold:

- the proposal targets the exact already-fixed graph and obligation revision;
- the evidence format is the exact supported format;
- semantic subject identity matches exactly, modulo set-like ordering;
- semantic context identity matches exactly, modulo set-like ordering;
- the exact proposition matches the competent target; and
- the competent checker accepts the exact proposed certificate.

The checked evidence retains the exact discharge target, producer, checker, format, semantic subjects/contexts, proposition, and certificate.

## Producer failure is nonsemantic

Timeout, unknown, ordinary producer failure, refusal, and checker rejection remain unresolved proof attempts. They do not establish proposition falsehood and do not manufacture a runtime, assumption, export, or other assurance disposition.

A later producer may attempt the same exact discharge target.

## Evidence lineage does not re-key the target

The semantic target is only the exact graph revision plus exact obligation revision. Producer/checker/artifact metadata belongs to evidence lineage.

Changing a competent producer or accepted certificate may change evidence lineage, but does not change the already-fixed discharge-target identity. This is the normative form of VER-011.

## Imported boundaries

This proof imports:

- `PHIL-VERIFY-WORKFLOW-001` for the exact pre-existing verification target and canonical obligation graph;
- the Phil Core decision/certificate checker as the competent checker boundary; and
- the ordinary assurance/evidence representation for concrete artifact identity and validity metadata.

It does not re-prove proposition truth, certificate-checker internals, parser/surface semantics, or policy-controlled non-proof dispositions.

## Representation boundary

Concrete `Text`, `Digest`, `RevisionId`, proposition rendering, `DecisionCertificate`, `CheckState`, `SolverAssumption`, `Data.Map`/`Data.Set`, and Haskell list normalization remain representation/runtime boundaries. Rocq and GHC/toolchain correctness remain explicit TCB components.

## Production correspondence

`VerificationProducerImplementation.v` mirrors the finite production admission surface after concrete native facts have been established: exact target, format, subjects, contexts, proposition, and competent-checker acceptance. Producer identity is deliberately not an authority input.

The same implementation proof also classifies absence of an artifact and checker rejection as unresolved rather than accepted evidence.
