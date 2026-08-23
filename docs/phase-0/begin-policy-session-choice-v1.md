# Phase 0 BeginPolicy semantic choice v1

## Scope

This slice normalizes the source-level distinction between the local `BeginPolicy` validation result and the peer-visible `reject(reason)` / `proceed` session choice.

It is deliberately **semantic only**. No numeric rejection code, byte encoding, runtime ABI, buffering rule, or outer framing is selected here.

## Source semantics

The server source says:

```phil
decide validate BeginPolicy at policyContext on begin {
    rejected(reason) => {
        let session4 = select reject(reason) on session3
        close failure
    }

    accepted(beginPolicy) => {
        let session4 = select proceed on session3
            using beginPolicy
        ...
    }
}
```

The client source offers the dual protocol labels:

```phil
offer session2 {
    reject(reason) => { ... }
    proceed => { ... }
}
```

The validation result and the protocol label are not the same choice:

```text
accepted / rejected(reason)      local BeginPolicy validation
              |
              v
proceed / reject(reason)          peer-visible session choice
```

## Systems representation

The predecessor represented `BeginPolicy` as a payload-free `TermRuntimeCheck`, followed by generic `select reject` / `select proceed` operations. The client received an anonymous runtime Bool and branched on it. That shape lost the source-level rejection value.

The successor makes the validation operands explicit:

```text
server.policy_context : RuntimeInput[PolicyContext]
server.begin          : RuntimeRecord[Begin]
```

The recognized `Begin` record is materialized only after `OpCommitIngress` on the recognition-success path. `policyContext` is architecture-supplied and therefore has no producer inside `UploadServer`.

The local validation becomes:

```text
server.begin.commit:
  TermRuntimeChoice "validate BeginPolicy"
    inputs = [server.policy_context, server.begin]
    site   = Just <the exact predecessor BeginPolicy RuntimeSiteRef>
    arms = {
      accepted -> server.proceed
      rejected -> bind server.begin_reject_reason -> server.reject
    }
```

The rejection value is semantic and intentionally opaque:

```text
server.begin_reject_reason : RuntimeOpaque[ValidationReason[BeginPolicy]]
```

The exact predecessor `RuntimeSiteRef` is preserved. This is a representation change around the runtime validation boundary, not a replacement or discharge of the validation obligation.

## Server session choice

The server continuations contain semantic session selects:

```text
server.reject:
  OpSessionSelect server.transport "reject"
                  (Just server.begin_reject_reason)

server.proceed:
  OpSessionSelect server.transport "proceed" Nothing
```

`proceed` carries no runtime payload. The source `beginPolicy` evidence remains proof/authority information; it is not materialized as a protocol payload.

## Client session choice

The anonymous `client.begin_branch : Bool` and generic label-receive call are removed. The client instead offers:

```text
TermSessionOffer client.transport {
  reject  -> bind client.begin_reject_reason -> client.reject
  proceed -> client.proceed
}
```

with:

```text
client.begin_reject_reason : RuntimeOpaque[ValidationReason[BeginPolicy]]
```

The server and client reason values are deliberately distinct Systems identities. The protocol relates the semantic payload across the endpoint boundary; one SSA/value identity does not cross processes.

Both payload targets are dedicated single-predecessor blocks, so the branch-local values cannot be observed from the sibling arm.

## Assurance boundary

The lowering decision `lower.session.begin_policy_choice` records that:

- the exact retained `BeginPolicy` runtime site is unchanged;
- recognized `Begin` and `policyContext` are explicit validator operands;
- rejected validation binds a reason only on the rejected arm;
- `reject` carries exactly that server-side reason;
- `proceed` carries no payload;
- the client binds a distinct reason only on the `reject` arm;
- merged version-choice operand/session semantics remain valid.

The following remain residual target choices:

- physical `Begin` record representation;
- physical `PolicyContext` representation;
- rejection-reason representation and equivalence classes;
- rejection-reason wire code or serialization;
- selector/receiver runtime ABI;
- malformed-input behavior for any future wire profile;
- outer framing.

In particular, this slice must not invent a numeric rejection code merely because an earlier digest-mismatch profile happened to use one.

## LLVM boundary

The already-selected version-choice physical profile must remain fail-closed for these new semantic operations:

- the local payload-bearing `BeginPolicy` `TermRuntimeChoice` has no physical lowering yet;
- `reject(reason)` / `proceed` `OpSessionSelect`s have no physical lowering yet;
- the client `TermSessionOffer` has no physical lowering yet.

A later tranche will select a concrete reason representation and reject/proceed runtime/wire profile, with separate translation validation and proof obligations.
