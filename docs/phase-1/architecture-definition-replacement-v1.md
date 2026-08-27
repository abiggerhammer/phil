# Phase 1 architecture definition replacement v1

This slice closes conformance case `ARCH-004` from ADR-019: an implementation/body/composition rewrite may change `DefinitionRevision` while preserving the public `InterfaceRevision`, provided the replacement still refines the unchanged public contract.

## Identity rule

`Phil.Core.Static` already separates public and private identity inputs:

- `InterfaceRevision` is derived only from checked public interface semantics;
- `DefinitionRevision` is derived from that exact interface revision plus checked definition semantics.

Therefore a replacement with the same stable `DeclarationKey` and unchanged checked public interface, but changed checked definition semantics, must preserve `InterfaceRevision` and change `DefinitionRevision`.

This slice does not add a second definition-identity algorithm.

## Refinement is checked by the competent layer

Revision separation does not make every body rewrite acceptable. A replacement is admissible only if the checker competent for its public contract accepts the new definition.

The executable pressure case uses Steve's already-general provider qualification machinery:

1. derive an original and replacement declaration identity from the same `DeclarationKey` and public interface;
2. bind the provider contract to that stable `InterfaceRevision`;
3. bind each implementation/qualification claim to its own declaration-derived `DefinitionRevision`;
4. require both implementations to pass `checkProviderSemanticQualification` against the same public contract.

The provider checker already checks exact contract revision, implementation revision, total operation correspondence, callable refinement, non-strengthening preconditions, outcome correspondence, and branch-sensitive resource residue. `ARCH-004` composes with that authority instead of duplicating it inside declaration identity.

## Executable cases

`test/Phase1ArchitectureDefinitionReplacementMain.hs` checks:

1. a definition/composition rewrite preserves `DeclarationKey` and `InterfaceRevision` while changing `DefinitionRevision`;
2. the original definition qualifies against the stable public provider contract;
3. the replacement definition, with its new `DefinitionRevision`, requalifies against the same contract;
4. the replacement qualification claim names the unchanged interface and new definition revision exactly;
5. a replacement that introduces a stronger caller precondition is rejected under the unchanged interface; and
6. changing the public contract remains an `InterfaceRevision` change, as a separation/non-vacuity control.

## Boundary

This closes `ARCH-004` only. It does not say that provider qualification is the only competent definition-refinement checker. Callable, protocol, generic, architecture-composition, and later data/boundary constructs retain their own semantic checking responsibilities.

`PHIL-ARCH-ID-001` therefore remains open after this slice until `ARCH-007` and the generalized declaration-identity proof are complete.
