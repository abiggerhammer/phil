# Phase 1 generic checked-Core → Systems lowering

**Obligation:** `PHIL-SYS-GENERIC-001`  
**Governing decisions:** ADR-007, ADR-020  
**Implementation:** `src/Phil/Systems/GenericLowering.hs`

## Scope

This slice closes the missing **producer seam** between an exact checked
`ArchitectureInstance` plus target-abstract checked-Core execution facts and the
existing generic Phase-1 `SystemsArtifact` / `Phase1StageBundle` verifier.

It does not make concrete source parsing part of Systems. Grammar-v1 parsing,
declaration elaboration, and construction of the checked architecture/Core
input remain upstream semantic boundaries. The Systems producer must not repeat
or guess their work.

The central rule is:

> Lowering receives semantics; realization supplies representation.

The producer therefore has no upload/Steve discriminator and no program-name
dispatch. `coreProgramLabel` is diagnostic presentation and is excluded from
the checked-Core semantic form.

## Producer inputs

`lowerGenericSystems` receives exactly:

1. a `CheckedArchitectureInstance`, including its exact `InstanceRevision`;
2. a target-abstract `CoreSystemsProgram`;
3. an explicit `GenericRealizationContext`.

The checked-Core execution vocabulary names values, abstract operations,
control-flow blocks, terminal outcomes, and exact source facts. It cannot name a
runtime symbol, ABI/layout choice, target assumption, qualification, or cost.

The realization context supplies those downstream choices explicitly:

- abstract operation → selected runtime/provider operation;
- qualification references;
- realization assumptions;
- target preconditions and derived obligations;
- attributable cost class/shape;
- target-only representation/layout choices;
- exact realization and verifier-profile revisions.

Missing operation realizations reject rather than falling back to ambient
runtime lookup.

## Derived artifacts

For every accepted input, the generic producer derives:

- a `SystemsProgram`;
- a `LoweringLedger` with one exact decision for every realized Core operation
  plus every explicit target-only choice;
- a `StageContract` whose source facts come from the checked-Core semantic
  facts and whose assumptions/derived obligations come from the explicit
  realization choices;
- an `ArchitectureRealization` / `RealizationRevision`;
- a `Phase1StageBundle`.

The candidate bundle is then passed through the existing
`verifyPhase1StageBundle`. Producer success alone is not assurance authority.

The source-side identity includes the exact `InstanceRevision` and canonical
checked-Core semantic form. Presentation labels do not contribute. Realization
identity includes the explicit realization context, operation mappings,
qualifications, assumptions, cost shapes, and target choices.

## Witness migration in this slice

`Phil.Examples.Phase1.SystemsWitnesses` no longer hands a preconstructed
`SystemsArtifact` to the Phase-1 StageContract machinery.

The upload and Steve adapters instead provide:

- an exact checked architecture occurrence;
- their target-abstract checked-Core execution forms;
- explicit host realization contexts.

Both call the same `lowerGenericSystems` entry point.

Steve's provider qualifications remain witness evidence, not lowering rules.
The existing host pointer/length ABI strengthening remains an explicit
`RealizedTargetChoice` with decision `lower.steve.host-abi`, its target
precondition, cost classification, and derived obligation.

The previous hand-built Phase-0 upload Systems artifact and Steve-specific
`steveSystemsArtifact` are not inputs to this path.

## Focused conformance

`test/Phase1GenericSystemsLoweringMain.hs` checks that:

1. upload is produced and accepted through the generic producer/verifier;
2. Steve is produced and accepted through the same producer/verifier;
3. changing a declaration presentation name does not change
   `InstanceRevision`, Systems artifact revision, or StageContract revision;
4. one exact checked ArchitectureInstance can admit two explicit legal
   realizations with one source revision but distinct realization and Systems
   revisions;
5. a missing abstract-operation realization rejects exactly;
6. Steve's target-only ABI decision remains explicit in the generated lowering
   ledger.

The dedicated workflow strict-builds the producer, witness adapters, and focused
test with `-Wall -Werror`, then runs the test.

## Remaining certification boundary

This Haskell slice supplies the concrete producer that the Rocq
`PHIL-SYS-GENERIC-001` proof can model and certify. Until that correspondence
proof lands, the implementation remains executable evidence rather than a
Certified proof artifact.

Separately, the full Phase-1 witness integration obligation still owns the
end-to-end requirement that ordinary `.phil` source elaborate into these exact
checked Architecture/Core inputs through the shared parser/elaborator/checker
path. This Systems slice deliberately does not make a parser an authority for
lowering semantics.
