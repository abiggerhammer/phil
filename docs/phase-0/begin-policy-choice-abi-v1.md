# Phase 0 BeginPolicy choice ABI v1

## Scope

This profile physically lowers the semantic `BeginPolicy` validation and its dual peer-visible `reject(reason)` / `proceed` choice introduced by the merged BeginPolicy Systems tranche.

It composes on top of `phil-runtime/phase0/version-session-choice-v1`. The existing version negotiation, payload/cancel choice, final response, storage, digest validation, exact receive, and recognized-record lowerings remain unchanged.

The profile is:

```text
phil-runtime/phase0/begin-policy-choice-v1
```

## Explicit validator operands

The source validation is:

```text
validate BeginPolicy(policyContext, begin) {
  accepted -> ...
  rejected(reason) -> ...
}
```

The target ABI makes both runtime operands explicit:

```llvm
declare i1 @phil_runtime_validate_begin_policy(ptr, ptr, ptr)
```

Arguments are, in order:

1. the exact `server.policy_context : RuntimeInput[PolicyContext]`, lowered as an explicit `UploadServer` pointer parameter;
2. the exact recognized `server.begin : RuntimeRecord[Begin]` pointer materialized by the predecessor recognized-record lowering;
3. a caller-owned pointer to an `i8` rejection-reason slot.

Return `true` means `accepted`. Return `false` means `rejected`, and the provider must initialize the reason slot before returning.

Ambient/current policy context, current Begin, last-validation-result, and last-rejection-reason state are forbidden.

Correct implementation of `BeginPolicy` itself remains an external runtime/provider obligation. Translation validation proves operand/control correspondence, not policy correctness.

## Rejection reason representation

At Systems, the rejection payload remains nominal and opaque:

```text
ValidationFailure[BeginPolicy]
```

The frozen Phase 0 client binds that value and immediately releases its owned payload and closes failure; it never branches on, compares, projects, stores, or otherwise observes the reason. The server uses the value only as the payload of `reject(reason)`.

For this exact closed program, all `BeginPolicy` rejection values are therefore equivalent at the peer-visible boundary. The translation verifier mechanically requires exactly one semantic use of the server reason—the `reject(reason)` forwarding use—and zero semantic uses of the client reason. Mutation regressions reject either premise drifting. This target profile chooses one canonical boundary code:

```text
0x01 = BeginPolicyRejected
```

All other reason codes are reserved in v1.

This is an exact-program observational quotient. It is **not** a claim that the abstract `ValidationFailure[BeginPolicy]` type has one inhabitant, and it does not prevent a runtime validator from retaining richer local diagnostics. A future program that inspects or distinguishes BeginPolicy failure reasons requires a richer target representation and a new profile.

## Server selectors

The semantic server operations lower to:

```llvm
declare void @phil_runtime_select_begin_policy_reject(ptr, i8)
declare void @phil_runtime_select_begin_policy_proceed(ptr)
```

Correspondence is exact:

```text
reject(server.begin_reject_reason)
  -> phil_runtime_select_begin_policy_reject(
       server.transport,
       server.begin_reject_reason)

proceed
  -> phil_runtime_select_begin_policy_proceed(server.transport)
```

The rejected-arm reason is loaded from the validator out-slot only after control enters the rejected binder block. The accepted path does not observe that slot.

Physical write failure remains a residual runtime assumption because source `select` has no failure edge.

## Client receiver

The semantic client offer lowers to:

```llvm
declare i1 @phil_runtime_receive_begin_policy_choice(ptr, ptr)
```

Arguments are the exact client transport and a caller-owned pointer to an `i8` rejection-reason slot.

Normal return mapping is:

```text
true  -> proceed
false -> reject(reason), with the reason slot initialized
```

The generated client loads the reason only in the dedicated `reject` binder block. The `proceed` path does not observe the slot.

## Canonical wire mapping

This profile defines the choice payload bytes, but not outer framing:

```text
proceed                         -> 01
reject(BeginPolicyRejected)     -> 00 01
```

Thus:

- `proceed` is exactly one octet;
- `reject` is exactly two octets;
- `0x00` is the reject tag;
- `0x01` is the proceed tag;
- rejection reason `0x01` is the sole canonical v1 BeginPolicy rejection class.

Tag EOF, reserved tags, truncated reject payloads, and reserved rejection reason codes must not return normally from the receiver. They do not map to an ordinary Phil `reject` or `proceed` branch because the source offer has no malformed-input arm.

## Assurance boundary

Translation-only `PHIL-LLVM-CERT-011` binds:

- exact BeginPolicy Systems source identity;
- exact canonical pre-optimization LLVM module and text;
- explicit policy-context and recognized-Begin validator operands;
- exact accepted/rejected control mapping;
- exact frozen-program reason-use premise for the target quotient;
- rejected-arm reason materialization;
- exact server reject/proceed selectors and transport operands;
- exact client receiver, branch mapping, and rejected-arm reason binding;
- target/tool/data-layout identities;
- the `begin-policy-choice-v1` ABI digest;
- preservation of the predecessor version-session-choice physical lowering;
- absence of generic/ambient BeginPolicy choice state.

It deliberately does not claim:

- correctness of the runtime BeginPolicy validator;
- semantic adequacy of the chosen observational quotient for any program other than this exact frozen candidate;
- concrete provider byte-I/O correctness;
- malformed-input non-return correctness;
- physical selector write success;
- LLVM implementation correctness;
- whole-program linking or native execution;
- outer framing.

Those remain explicit independent gates. A later proof harvest may promote the exact physical artifact to proof-bound certification without changing this target profile.
