# Phase 0 HelloPolicy validation semantics v1

## Scope

This slice corrects the remaining information loss at the Phase 0 `HelloPolicy` validation boundary. It is a Systems-semantic tranche only: no validator ABI, failure-reason representation, wire encoding, or fatal transport encoding is selected here.

The source semantics are:

```text
validate HelloPolicy at policyContext on hello {
  accepted(helloPolicy) -> choose_supported(...)
  rejected(reason)      -> fail validation(reason)
}
```

The historical Systems graph retained the success/failure control edge but represented the validator as an operand-free `TermRuntimeCheck []` and discarded the rejected `reason` before the terminal failure.

## Explicit subjects

The successor reuses identities already established by predecessor tranches:

```text
server.policy_context     : RuntimeInput[PolicyContext]
server.hello              : RuntimeRecord[Hello]
server.hello_reject_reason: RuntimeOpaque[ValidationReason[HelloPolicy]]
```

`server.hello` is the recognized record already materialized for version-choice operands. `server.policy_context` is the architecture-supplied input already introduced for BeginPolicy validation. Neither is rematerialized here.

The local runtime choice is:

```text
server.hello.commit:
  validate HelloPolicy(server.policy_context, server.hello) {
    accepted -> server.version.choose
    rejected -> bind server.hello_reject_reason
                -> server.hello.policy_failure
  }
```

The exact predecessor `ValidationBoundary "HelloPolicy"` `RuntimeSiteRef` is preserved.

## Rejected reason and terminal failure

The rejected reason has exactly one semantic use in the frozen candidate:

```text
fail validation HelloPolicy(
  server.transport,
  server.hello_reject_reason)
```

followed by the existing terminal class:

```text
fatal ValidationFailure[HelloPolicy]
```

This pairing preserves both the terminal failure classification and the branch-local rejection detail without pretending that the detail has a physical target representation.

The focused verifier requires the failure block to contain exactly that one reason-carrying semantic operation. Extra observations of the reason are rejected.

## Assurance and cost

The existing HelloPolicy runtime-enforcement revision/evidence and cost site remain unchanged. The new lowering decision classifies this as semantic materialization rather than a new runtime check:

- no additional dynamic validation is introduced;
- accepted/rejected control flow is unchanged;
- existing recognized-Hello and PolicyContext identities are reused;
- the rejection reason becomes explicit because it is present in source semantics;
- physical reason representation remains unresolved at this layer.

## Backend competence boundary

The current `begin-policy-choice-v1` LLVM target does not know how to lower the new HelloPolicy `TermRuntimeChoice`. Generic lowering therefore leaves the HelloPolicy choice as unjustified `LLVMUnreachable`, and normal LLVM verification rejects the artifact.

That fail-closed result is intentional. A successor backend tranche must explicitly select:

- the physical HelloPolicy validator signature and operand representation;
- the rejected-reason representation;
- the fatal failure transport/runtime ABI, if any;
- concrete runtime/provider obligations.

Until then, no translation certificate is claimed for this successor Systems artifact.
