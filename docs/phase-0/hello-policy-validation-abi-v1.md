# Phase 0 HelloPolicy validation ABI v1

## Scope

This target physically lowers the semantic HelloPolicy validation successor landed in PR #78. It composes on top of `phil-runtime/phase0/begin-policy-choice-v1` and selects only the runtime representation needed for the frozen Phase 0 program.

Target profile:

```text
phil-runtime/phase0/hello-policy-validation-v1
```

## Validator

The Systems choice

```text
validate HelloPolicy(server.policy_context, server.hello) {
  accepted -> server.version.choose
  rejected -> bind server.hello_reject_reason
              -> server.hello.policy_failure
}
```

lowers to:

```c
bool phil_runtime_validate_hello_policy(
    void *policy_context,
    void *hello_record,
    void **rejection_reason_out);
```

The first two arguments are the exact explicit `PolicyContext` input and recognized `Hello` record pointer. There is no ambient/current policy or Hello lookup.

On `true`, the reason slot is not observed. On `false`, the provider must write a non-null opaque reason handle that denotes the exact provider-side rejection detail for this validation.

## Reason representation

`ValidationReason[HelloPolicy]` is represented as an opaque provider pointer.

This target deliberately does **not** quotient the reason to an integer code. The source carries the rejected reason directly into `fail validation(reason)`, so preserving its identity is the conservative physical choice.

The runtime provider owns the pointed-to storage. The handle must remain valid through the immediately following fatal-effect call. No byte representation or peer protocol encoding is defined.

## Fatal validation effect

The rejected block binds the opaque pointer and calls:

```c
void phil_runtime_fail_hello_policy(
    void *transport,
    void *rejection_reason);
```

with the exact server transport and exact validator-produced reason handle. The component then terminates through Phil's existing `TermFatal -> LLVMReturn("fatal:...")` convention.

This profile does not define a peer wire message for HelloPolicy failure and does not select outer framing. Runtime/provider behavior associated with the local fatal effect and transport shutdown remains an external provider obligation.

## Translation certification

`PHIL-LLVM-CERT-012` is translation-only authority for the exact content-bound Systems/LLVM pair and this ABI. It establishes:

- explicit policy context and recognized Hello operands;
- exact retained HelloPolicy runtime site;
- accepted/rejected control mapping;
- rejected-only opaque reason binding;
- exact transport/reason fatal-effect call;
- preservation of the previously lowered BeginPolicy and version machinery;
- absence of ambient policy, Hello, and rejection-reason state.

It does not certify provider validation semantics, reason contents/lifetime, fatal-effect runtime semantics, external LLVM semantics, linking, or native execution.

## Runtime gate

The focused CI lane assembles the emitted module with LLVM 18, checks ABI compatibility against the C provider fixture, partially links the modules, and runs a native smoke program that verifies pointer identity from validator output through the fatal-effect input. A nullary/ambient provider fixture must be rejected by the ABI checker.
