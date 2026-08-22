# Recognized-record ABI v1: runtime symbol identity amendment

## Status

Normative amendment to `recognized-record-abi-v1.md` before implementation of the first recognized-record LLVM candidate.

The opaque-record representation, `{ i8, ptr }` recognition result, fail-closed status handling, typed field-accessor convention, and exact-receive scalar dependency from recognized-record ABI v1 are unchanged.

This amendment changes only how ordinary runtime primitive symbols are identified.

## Motivation

The Steve Systems generalization handoff requires one physical runtime mechanism to be able to justify multiple exact assurance claims without duplicating the physical operation. In particular, one digest validation may support more than one retained-runtime obligation while still executing exactly once and incurring exactly one physical cost.

An LLVM symbol convention of the form:

```llvm
@phil_runtime_<evidence-entry-id>
```

incorrectly couples physical runtime function identity to one logical assurance claim. It would force a shared physical site either to:

- choose one claim arbitrarily as the ABI name;
- acquire multiple aliases whose names suggest multiple physical mechanisms; or
- duplicate the runtime call and therefore falsify the cost model.

None is acceptable.

## Decision

Runtime primitive symbols identify the **physical operation family and ABI signature**, not an assurance revision or evidence entry.

Assurance claim identity belongs to the Systems/LLVM verification relation for a particular call site. It does not participate in the linker-visible runtime symbol name.

A physical call site may therefore carry one or more exact assurance claims while remaining one call to one runtime primitive.

For the recognized-record vertical slice, examples become:

```llvm
%r = call { i8, ptr } @phil_runtime_recognize_Begin()
%status = extractvalue { i8, ptr } %r, 0
%server_begin = extractvalue { i8, ptr } %r, 1
%ok = icmp eq i8 %status, 1
```

and:

```llvm
%recv_ok = call i1 @phil_runtime_receive_exact_u64(
  i64 %server_begin_length)
```

The exact spelling of these two example symbols may be refined by a canonical runtime-symbol builder, but the following is normative:

- the symbol is derived from the physical primitive/operation identity and its ABI-relevant type shape;
- it is **not** derived from `RevisionId`, `EvidenceEntryId`, `AssuranceUseId`, or the cardinality/order of the claim set;
- changing which assurance claims a verified call site carries does not, by itself, change the runtime function symbol;
- changing the physical ABI signature does require a distinct symbol/profile identity as specified by the runtime ABI.

Field-accessor symbols remain semantic-schema-specific as already specified by recognized-record ABI v1:

```llvm
@phil_record_Begin_get_length(ptr)
```

That is not assurance coupling: `Begin.length` is the semantic operation being performed.

## Physical site identity

A linker symbol names an implementation entry point, not a dynamic/program physical site.

Two call instructions to the same primitive are two physical call sites even when they invoke the same symbol. Conversely, one call instruction carrying multiple assurance claims is still one physical site.

The generalized Systems representation should therefore model physical-site identity independently of both:

- runtime function symbol identity; and
- individual assurance claim identity.

The Steve handoff's intended shape—one physical site with a nonempty exact claim set—is compatible with this ABI rule.

## Translation-validation consequence

The LLVM preservation checker must eventually validate two related but distinct properties:

1. **physical operation preservation** — the source physical runtime site maps to exactly one corresponding LLVM call site with the expected primitive/signature and cost identity;
2. **claim-set preservation** — every exact `(revision, evidence, subject...)` binding attached to that Systems site survives in the LLVM-side verification metadata/relation, without manufacturing extra calls.

The verifier must reject a lowering that preserves all claim metadata but duplicates the physical call, or preserves the call while dropping/mutating a claim binding.

The current Phase 0 singleton runtime sites remain valid special cases after the generalized claim-set representation lands.

## Runtime ABI descriptor

The `phil-runtime/phase0/recognized-record-v1` ABI descriptor/digest must include the rule:

> Runtime primitive symbols are derived from physical operation/signature identity and never from assurance evidence/revision/use identity.

It must also include the canonical symbol/signature entries used by the recognized-record candidate, including recognition and exact receive.

This is part of ABI v1 rather than an ABI v2 change because no recognized-record-v1 implementation or certification artifact exists yet; this amendment closes an ambiguity in the design before that first artifact is created.

## Adversarial checks

The implementation/generalization work should reject at least:

- changing a physical primitive symbol solely because a second assurance claim is attached;
- encoding an evidence/revision/use ID into a runtime primitive symbol;
- splitting one multi-claim Systems physical site into one LLVM call per claim;
- collapsing two distinct Systems physical sites merely because they call the same primitive symbol;
- dropping one claim while preserving the physical call;
- inventing a claim because another claim at the same site shares the same runtime symbol or cost reference;
- changing the primitive ABI signature without changing the bound runtime ABI identity.

## Consequence for the next slice

The recognized-record implementation should emit a physical-operation-oriented sequence such as:

```text
Systems recognition site + exact claim set
  -> call @phil_runtime_recognize_Begin
  -> opaque Begin record handle
  -> call @phil_record_Begin_get_length
  -> i64 begin.length
  -> call @phil_runtime_receive_exact_u64(i64 begin.length)
```

Assurance identities remain explicit and content-bound in the verification artifacts, but they do not leak into runtime linker symbol identity.
