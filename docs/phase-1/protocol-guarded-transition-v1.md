# Phase 1 protocol guarded-transition conformance v1

PROT-006 separates **structural session availability** from **semantic authority to take a guarded transition**.

A branch label or transition name identifies a structurally available protocol action. It does not, by itself, establish any proposition or transfer any proof authority.

## Layering

The implementation keeps the dependency direction explicit:

1. `Phil.Core.Protocol` checks exact protocol instance, role, current local session state, and ordinary session progression.
2. `Phil.Assurance.Verify` checks whether exact obligation revisions are discharged by competent evidence under the selected manifest and validity context.
3. `Phil.Assurance.ProtocolGuard` composes those relations for guarded transitions.

Core therefore does not depend on assurance and does not grow a protocol-local boolean guard mechanism.

## Exact guards

A `ProtocolTransitionGuard` consists of:

- its origin layer (`ProtocolDeclaredGuard` or `ArchitectureStrengtheningGuard`); and
- the exact `RevisionId` of the assurance obligation that must be discharged before the transition.

A guarded action is accepted only when:

- the assurance manifest verifies normally;
- every declared guard revision is present in that manifest;
- every declared guard revision is in the manifest's certification scope; and
- the underlying Core protocol action is structurally legal.

Because `verifyManifest` checks each certified obligation's exact acceptance rule, evidence attached to another obligation revision, evidence with the wrong role/kind, rejected evidence, stale validity scope, or otherwise incompetent evidence cannot authorize the guarded transition.

## Protocol guard versus architecture strengthening

Protocol-declared requirements and architecture refinements remain distinct obligations. An architecture may require an additional guard before permitting a structurally legal protocol transition, but satisfying the reusable protocol guard does not silently satisfy the architecture guard.

Both obligations compose conjunctively when both are declared.

Conversely, guard evidence cannot make a structurally illegal session action legal. After exact guards are discharged, the ordinary protocol/session checker still has final authority over the requested action and successor.

## Conformance corpus

`test/Phase1ProtocolGuardedTransitionMain.hs` checks nine cases:

1. a matching branch label does not transfer proof implicitly;
2. exact protocol-guard evidence admits the structurally legal transition;
3. evidence for another guard revision cannot substitute;
4. architecture strengthening requires its own exact obligation;
5. protocol and architecture guards compose conjunctively;
6. evidence with the wrong acceptance role cannot discharge the guard;
7. rejected evidence cannot authorize the transition;
8. duplicate guard requirements reject rather than being silently normalized; and
9. valid guard evidence cannot make an unknown/illegal session label legal.

This closes PROT-006 at the implementation/conformance level. Truth of the underlying evidence remains the responsibility of the assurance checker and its accepted evidence producers; the generalized protocol progression/guard theorem remains a separate Rocq obligation.
