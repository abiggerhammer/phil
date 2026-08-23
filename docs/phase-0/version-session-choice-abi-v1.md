# Phase 0 version/unsupported choice ABI v1

## Scope

This profile physically lowers the semantic `unsupported` / `version(selected)` choice introduced by the Systems version-choice slice. It also materializes the previously implicit operands of the local `choose_supported(serverSupported, hello.versions)` computation so that the selected `UInt16` has a real target-level producer.

The profile is:

```text
phil-runtime/phase0/version-session-choice-v1
```

It is layered on the payload/cancel physical profile and preserves that profile's transport, final-response, storage, digest, exact-receive, and recognized-record decisions.

## Systems prerequisite

The source architecture supplies:

```text
serverSupported : SupportedVersions
```

as an unrestricted initial binding. It is therefore represented as an explicit Systems runtime input, never as ambient runtime state:

```text
server.supported_versions : RuntimeInput[SupportedVersions]
```

Recognition of `Hello` is materialized explicitly:

```text
server.hello : RuntimeRecord[Hello]
server.hello_versions : RuntimeOpaque[VersionSet]
```

with provenance:

```text
recognized Hello
    -> server.hello
    -> project Hello.versions
    -> server.hello_versions
```

The local choice then has explicit operands:

```text
TermRuntimeChoice choose_supported
  [server.supported_versions, server.hello_versions]
  {
    none -> server.unsupported
    some -> bind server.selected_version : UInt16 -> server.version
  }
```

The existing local-choice invariant continues to bind the exact `none` / `some(selected_version)` result shape; this successor adds explicit operand identity without reinterpreting the local choice as peer/session state.

## Target ABI

```llvm
declare ptr  @phil_record_Hello_get_versions(ptr)
declare i1   @phil_runtime_choose_supported(ptr, ptr, ptr)
declare void @phil_runtime_select_unsupported(ptr)
declare void @phil_runtime_select_version(ptr, i16)
declare i1   @phil_runtime_receive_version_choice(ptr, ptr)
```

### `serverSupported`

`UploadServer` receives `server.supported_versions` as an explicit pointer parameter. The physical representation behind that pointer is runtime-provider-defined for this profile; ambient lookup is forbidden.

### `Hello.versions`

`phil_record_Hello_get_versions` takes the exact recognized `Hello` record pointer and returns an opaque pointer to the offered-version set. No copy is implied by the ABI.

### `choose_supported`

```text
phil_runtime_choose_supported(
  server_supported,
  offered_versions,
  selected_version_out
) -> i1
```

`true` means `some`; the runtime initializes the `i16` output slot with a version that is a member of both input sets. `false` means `none`; generated code does not observe the output slot on that branch.

The provider obligation is semantic, not merely representational:

```text
true  => selected ∈ serverSupported ∩ hello.versions
false => serverSupported ∩ hello.versions = ∅
```

The target does not impose a tie-breaking policy when more than one common version exists.

## Wire representation

Canonical mapping:

```text
unsupported       -> 00
version(0x1234)   -> 01 12 34
```

The selected version is encoded as an unsigned 16-bit integer in big-endian byte order.

Thus:

```text
unsupported = exactly 1 octet
version(v)  = exactly 3 octets: 0x01 || u16be(v)
```

The profile does not define an outer frame around this choice.

## Outgoing primitives

The two source labels use distinct primitives so the payload-free `unsupported` branch never carries a dummy `UInt16`:

```text
phil_runtime_select_unsupported(transport)
phil_runtime_select_version(transport, selected_version)
```

Both receive the exact server transport operand. Physical write failure is a residual runtime assumption because the source `select` has no failure edge; a conforming runtime must not return normally after an unrecoverable write failure.

## Incoming primitive

```text
phil_runtime_receive_version_choice(transport, selected_version_out) -> i1
```

Behavior:

```text
00       -> false / unsupported; output slot is not observed
01 hi lo -> true  / version; output := (hi << 8) | lo
```

The runtime must not return normally for:

- EOF before the tag;
- a reserved tag;
- `0x01` followed by fewer than two payload octets.

No malformed-input branch is invented in the Phil CFG.

## Ambient state prohibition

The generated artifact must not depend on ambient/current variables or nullary runtime accessors for:

- supported versions;
- offered versions;
- selected version;
- session label;
- transport.

All of those identities are explicit operands or branch-local outputs.

## Assurance boundary

`PHIL-LLVM-CERT-010` is initially translation-only. It binds the exact Systems artifact, pre-optimization LLVM module/text, target/tool/layout, and this ABI descriptor.

It justifies the translation facts: explicit source operands, exact chooser SSA flow, exact server selectors, exact client receiver/payload binding, preservation of predecessor physical lowerings, and absence of generic/ambient version-choice state.

It does **not** prove the runtime provider's set-selection semantics, opaque version-set representation, concrete byte I/O, malformed-input termination behavior, physical write success, LLVM implementation correctness, whole-program linking, or native execution. Those remain independent gates until a later proof-bound certification tranche closes them to the extent selected by the assurance manifest.

## Native CI fixture

The Phase 0 fixture checks:

- `Hello.versions` projection identity;
- a `some` case where the selected value belongs to both sets;
- a disjoint `none` case that leaves the output sentinel unobserved/unchanged;
- `unsupported -> 00`;
- `version(0x1234) -> 01 12 34`;
- decoding of both labels;
- reserved tag, tag EOF, and truncated version payload abort;
- simulated selector write failure abort;
- exact LLVM function signatures through `check_runtime_abi.py --partial`;
- canonical generated LLVM acceptance by LLVM 18;
- LLVM type-link compatibility between the generated module and the focused provider definitions.
