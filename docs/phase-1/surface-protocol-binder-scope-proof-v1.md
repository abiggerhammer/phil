# PHIL-SURFACE-BINDER-SCOPE-001 — protocol message and branch-payload scope

This slice certifies the final named SURF-009 binder family: protocol message binders and select/offer branch payload binders.

## Message-binder lifetime

For a send/receive message parameter, production:

1. checks the parameter type before introducing that parameter;
2. allocates the message binder from the next declaration-wide ordinal;
3. makes that binder visible to its guard; and
4. keeps it active through the remainder of the same role continuation.

Therefore later message types/guards may depend on earlier message binders, while a message cannot depend on its own not-yet-bound name.

## Branch-payload lifetime

For a select/offer branch, production:

1. enters a fresh branch child scope;
2. checks payload parameter types left-to-right before each binder is introduced;
3. permits later payload types to depend on earlier payload binders;
4. rejects self/current/future payload references;
5. exposes the complete payload telescope to the branch guard and continuation;
6. permits nested message binders to extend the same child scope;
7. closes the entire child scope before the next sibling branch; and
8. retains the advanced declaration-wide ordinal, so same-spelled sibling payload/message binders receive fresh identities.

Each role is itself a child scope: all role-local names disappear before the next sibling role while the declaration-wide ordinal continues monotonically.

## Certified claims

The normalized Rocq proof establishes:

- message type-before-binding order;
- exact message semantic identity;
- message persistence through its role continuation;
- exact guard visibility of the generated message binder;
- payload telescope source order/count and exact ordinal advancement;
- earlier payload dependency and forward-reference classification;
- complete payload visibility in guard/continuation;
- branch-local disappearance before siblings;
- sibling freshness whenever a branch introduced at least one local binder;
- role-local disappearance before sibling roles; and
- alpha/source-span stability for message and payload binders.

## Existing authorities reused

`SurfaceBinderScopeCore` / `PHIL-EXEC-BIND-001` remain the individual binder identity/admission authority. `SurfaceLetPatternScope` supplies the common ordered declaration-root + ordinal allocator used for bounded telescopes.

Protocol guard proposition truth, Core focusing, session-template construction, duality, recursion validity, boundary semantics, and assurance obligations remain separate authorities.

## Concrete correspondence

`Phil.Surface.GrammarV1.ProtocolBinderScope` is the production lexical authority.

The permanent `Phase1GrammarV1ProtocolBinderScopeMain.hs` corpus covers:

- message binders persisting within one role and closing before sibling roles;
- branch payloads and nested message binders in disjoint sibling scopes;
- dependent branch payload types;
- branch-payload forward-reference rejection;
- active message/branch shadowing rejection;
- sequential duplicate message rejection;
- alpha-stable BinderKeys/Core names;
- guards materialized under generated semantic names;
- semantic dependent payload types;
- exact binder evidence consumed by semantic sessions; and
- sibling-local semantic branch state.

## SURF-009 status after this slice

After this family lands, every named binder family under `PHIL-SURFACE-BINDER-SCOPE-001` has a bounded Rocq slice:

- term parameters / lexical locals;
- generic-static binders;
- let/pattern binders;
- match/decide/offer arms;
- borrow views;
- join state;
- loop state;
- refinement binders; and
- protocol message/branch-payload binders.

A final aggregate/closeout theorem and production-binding inventory remains a separate step; this slice does not claim that aggregate closeout by itself.
