# Phase 0 Recognized-Record ABI v1

## Status

Implementation decision for the next Phase 0 LLVM candidate.

This document chooses a concrete target/runtime representation for recognized semantic records without making that representation part of Phil source semantics. It is deliberately target-profile-specific: other backends, including GPU and NPU targets, may select different physical representations while preserving the same Systems-level semantic record and field-projection obligations.

## Decision

For the Phase 0 x86_64 LLVM target, a successfully recognized semantic record is represented at the runtime boundary by an **opaque runtime-owned pointer handle**.

Generated Phil LLVM may:

- receive such a handle from the recognition runtime boundary;
- carry it through SSA/control flow;
- pass it back to ABI functions that are declared to accept that record kind;
- project declared scalar fields through typed accessor functions.

Generated Phil LLVM may **not**:

- dereference the handle directly;
- compute offsets into it;
- cast it to a concrete `%Grammar` struct;
- infer the recognizer's storage layout;
- free or otherwise mutate the record through the handle;
- attach optimizer-strengthening pointer attributes merely because the source value is a recognized record.

The handle therefore makes the runtime ABI concrete while keeping recognition implementation, storage, and record layout replaceable.

## Recognition result ABI

A recognition boundary that materializes a semantic record returns a fully defined aggregate:

```llvm
{ i8, ptr }
```

The elements are:

1. `i8 status` — `1` means complete recognition succeeded and `0` means recognition failed;
2. `ptr record` — opaque handle to the recognized semantic record.

Values other than `0` and `1` are reserved. Generated Phil code checks for **exactly** `1`, so an out-of-contract status follows the failure branch rather than being interpreted as success.

This shape is intentionally compatible with the x86_64 SysV lowering of a C-like runtime result such as:

```c
struct phil_recognition_result {
    uint8_t status;
    void *record;
};
```

The ABI commitment is the target-level `{ i8, ptr }` signature and its semantics, not the spelling of a particular runtime implementation language.

For example, the Phase 0 `Begin` recognition boundary is lowered structurally as:

```llvm
%phil_recognition_result_server_version =
  call { i8, ptr } @phil_runtime_<begin-recognition-evidence>()
%phil_recognition_status_server_version =
  extractvalue { i8, ptr } %phil_recognition_result_server_version, 0
%server_begin =
  extractvalue { i8, ptr } %phil_recognition_result_server_version, 1
%phil_recognition_ok_server_version =
  icmp eq i8 %phil_recognition_status_server_version, 1
br i1 %phil_recognition_ok_server_version,
   label %server_begin_commit,
   label %server_begin_recognition_failure
```

The runtime must return a defined pointer value on both outcomes. The Phase 0 ABI uses `null` for the record element on recognition failure. On recognition success the returned handle denotes the recognized `ValueOf[G]` for that recognition event.

Phil-generated LLVM only uses the record handle on the success-dominated path. We intentionally do **not** encode the success contract as LLVM `nonnull`, `dereferenceable`, `align`, `noundef`, or similar attributes in v1. The runtime ABI contract is part of the target/runtime TCB; optimizer-strengthening facts require their own evidence before they may become LLVM assumptions.

## Record lifetime

The handle is runtime-owned. Its validity follows the semantic lifetime of the corresponding recognized Phil value, not an assumed concrete relationship to the input frame buffer.

The runtime is free to implement the record as, for example:

- a separately allocated semantic object;
- a compact runtime-owned descriptor;
- a view backed by retained recognized-frame storage;
- another representation hidden behind the handle.

Those choices are not observable to generated Phil code and are not frozen by this ABI.

The runtime must keep the handle valid for every dynamic path on which the corresponding Phil semantic value remains live. Generated code does not call `free` on a recognized-record handle in v1. A later lifetime-lowering slice may make destruction explicit when Systems-level liveness is available at the backend boundary.

## Typed scalar field projection ABI

A declared scalar field is projected by passing the exact record handle to a grammar/field-specific accessor.

For `Begin.length : U64`:

```llvm
declare i64 @phil_record_Begin_get_length(ptr)

%server_begin_length =
  call i64 @phil_record_Begin_get_length(ptr %server_begin)
```

The accessor's result type is determined by the checked semantic schema, not by runtime convention:

- `Bool` -> `i1`
- `U16` -> `i16`
- `U32` -> `i32`
- `U64` -> `i64`
- more generally, `UInt[n]` -> `iN` when that scalar width is admitted by the target profile.

Non-scalar projections are outside recognized-record ABI v1.

Accessor symbols are generated from the grammar and field identities under the target ABI's canonical symbol encoding. The ABI builder must reject symbol collisions rather than silently alias two semantic fields.

## Exact-receive data dependency

The point of materializing `Begin.length` is not merely to produce an SSA value; the value must be the value consumed by the exact-receive runtime boundary.

For the Phase 0 candidate, the existing evidence-specific exact-receive boundary therefore becomes a typed call with the projected length as an explicit argument:

```llvm
declare i1 @phil_runtime_<payload-exact-receive-evidence>(i64)

%phil_runtime_cond_server_payload =
  call i1 @phil_runtime_<payload-exact-receive-evidence>(
    i64 %server_begin_length)
br i1 %phil_runtime_cond_server_payload,
   label %server_digest,
   label %server_early_eof
```

This is intentionally still a narrow vertical slice. Transport and payload-owner values are not yet assigned their final physical ABI in this decision. What becomes concrete here is the source-level dependency:

```text
recognized Begin
  -> Begin.length : U64
  -> LLVM i64 SSA value
  -> exact-receive runtime argument
```

The runtime boundary may not substitute another length or recover the length from ambient state.

## Systems-level representation requirements

The physical pointer handle is not a new Phil source concept. Systems IR must retain enough identity to validate the lowering independently:

- the recognized semantic record has role `RuntimeRecord "Begin"` (or the corresponding grammar identity);
- the record value is tied to the exact recognition boundary that produced it;
- the record value exists only on the recognition-success path;
- the field projection names the exact record `ValueId`, grammar, field, output `ValueId`, and scalar type;
- the projection output is defined exactly once and dominates every use;
- `TermReceiveExact` consumes that exact typed scalar value.

A lowering that changes any of those identities is not equivalent merely because the resulting LLVM is well typed.

## No ambient current-record state

The runtime ABI must not expose a nullary operation such as:

```llvm
call i64 @phil_current_Begin_length()
```

That design was rejected because it hides the source data dependency in ambient runtime state. It is hostile to:

- reentrancy;
- concurrency;
- independent translation validation;
- provenance tracking;
- future offload/accelerator targets;
- replacement of the recognizer/runtime implementation.

The record handle is therefore always an explicit SSA operand of a field accessor.

## No concrete LLVM struct layout yet

The Phase 0 ABI does not emit:

```llvm
%Begin = type { i64, ... }
```

and does not lower `begin.length` to `getelementptr`/`load` from a fixed offset.

A by-value or concrete in-memory struct would prematurely make all of the following target ABI commitments:

- field ordering;
- padding;
- alignment;
- representation of enums and opaque fields;
- ownership/lifetime of nested values;
- eager versus lazy materialization;
- compatibility requirements for foreign recognizer implementations.

None of those decisions is required to make `begin.length` a real typed LLVM value. The opaque handle/accessor ABI gives us the needed executable dataflow without overconstraining the recognizer.

A later specialization pass may replace a verified accessor with a direct load or `extractvalue` when a target-specific layout decision and the required aliasing/alignment/provenance evidence exist. Such a replacement is an optimization/lowering decision, not a change to source semantics.

## Why not an integer handle?

An integer handle was considered and rejected for the Phase 0 host target. It would force every runtime implementation either to maintain a handle table or to introduce integer/pointer conversion semantics without buying us additional semantic isolation.

The opaque `ptr` already gives the C/LLVM runtime boundary a natural implementation handle while withholding all layout knowledge from generated code.

This is not a universal Phil rule. A GPU, NPU, sandbox, capability machine, or distributed target may reasonably choose an index, capability, address-space-qualified pointer, descriptor tuple, or other representation. That target must bind its own runtime ABI profile and prove/validate the same Systems-level semantic relations.

## Definedness and optimizer discipline

Recognized-record ABI v1 deliberately emits no pointer-strengthening attributes by default. In particular, it does not infer:

- `nonnull`
- `noundef`
- `dereferenceable`
- `dereferenceable_or_null`
- `align`
- `noalias`
- `nocapture`
- `readonly` / `readnone`
- `inbounds`
- `llvm.assume`

from Phil recognition, linearity, validation, or field typing alone.

This follows the existing LLVM trust-boundary rule: a source-language fact is not automatically an LLVM optimizer fact. If one of these attributes becomes useful, its exact LLVM precondition must be represented by an invariant/evidence edge whose validity scope covers the emitted use.

The record handle itself is never dereferenced by generated LLVM in v1, so the generated program does not need to rely on pointer layout, alignment, or pointee provenance to project a field.

## Runtime ABI identity

This representation must use a new runtime ABI profile rather than reusing the existing Phase 0 `reference-v1` identity.

Working profile name:

```text
phil-runtime/phase0/recognized-record-v1
```

Its digest should be derived from a canonical ABI descriptor that includes at least:

- recognition result shape `{ i8, ptr }`;
- recognition status `0 = failure`, `1 = success`, other values reserved/fail-closed;
- failure record value `null`;
- opaque/runtime-owned record handle semantics;
- typed scalar accessor convention;
- canonical accessor symbol rule;
- exact-receive scalar-argument convention;
- absence of default pointer-strengthening attributes;
- target triple/data-layout profile to which the ABI applies.

Changing any of those items requires a different ABI digest/profile revision.

## Certification boundary

`PHIL-LLVM-CERT-001` binds the exact existing Phase 0 Systems/LLVM pair and runtime ABI `phil-runtime/phase0/reference-v1`.

The recognized-record ABI candidate therefore requires:

1. a new Systems artifact that makes the recognized record and projection operand explicit;
2. a new LLVM target profile carrying the recognized-record ABI digest;
3. translation validation for the exact Systems -> LLVM candidate;
4. LLVM 18 acceptance of the exact emitted text;
5. a fresh certification revision for that exact source/target/profile tuple.

The old certificate must remain valid for its old artifact; it must not be silently retargeted.

## Required adversarial checks

The implementation slice should reject at least:

- recognition returns/binds a record of the wrong grammar;
- a projection uses a record from a different recognition event;
- a projection names the wrong field;
- a projection uses the wrong scalar result type;
- a record handle is used on a path not dominated by recognition success;
- the projection output is redefined;
- exact receive consumes a different scalar value;
- LLVM accessor input drifts to another record SSA value;
- LLVM accessor return width drifts from the Systems scalar type;
- the accessor is replaced by a nullary ambient-state call;
- recognition status is treated as success for a value other than exactly `1`;
- the runtime ABI digest/profile is changed without changing the target identity;
- pointer-strengthening attributes appear without explicit authority.

## Consequence

The first non-toy data dependency can now have a precise physical form without turning parser layout into language semantics:

```text
recognize Begin
  -> opaque %server_begin : ptr
  -> phil_record_Begin_get_length(%server_begin)
  -> %server_begin_length : i64
  -> receive_exact(%server_begin_length)
```

That is the Phase 0 recognized-record ABI v1.