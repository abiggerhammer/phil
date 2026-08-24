# Phase 0 shared control codec v1

## Scope

This profile closes the concrete `Hello`/`Begin` wire-codec gap between the landed client control-send and server framed-ingress boundaries. It extends `storage-failure-detail-v1`; no Systems semantics are changed.

The runtime profile is:

```text
phil-runtime/phase0/control-codec-v1
```

The LLVM control operations remain the explicit primitives already selected by the predecessor profiles. This profile fixes what those primitives mean on the wire and supplies one shared native provider used by both client serialization and server framing/recognition.

## Frame envelope

Every Phase 0 control frame is:

```text
offset  size  field
0       4     magic = 50 48 49 4c  (ASCII "PHIL")
4       1     codec version = 01
5       1     message tag
6       2     payload length, unsigned big-endian
8       N     payload bytes
```

Message tags are:

```text
01  Hello
02  Begin
```

The payload length is the exact number of bytes after the eight-byte header and is limited to `0..65535` by representation.

`receive_frame_Hello` and `receive_frame_Begin` validate magic, codec version, expected message tag, declared length, and completeness before returning. A framing violation has no source recovery edge and therefore must not return normally.

Multiple frames may be concatenated on one transport. A pending ingress identifies exactly one frame. `commit_ingress_G` advances the transport by exactly that frame; recognition failure destroys the exact pending/frame pair without advancing it.

## Hello payload

`Hello.versions` is encoded as:

```text
u16be count
count * u16be version
```

Rules:

- `count > 0`;
- the payload length is exactly `2 + 2*count`;
- versions are strictly increasing, so a set has one canonical byte representation;
- each version is the existing Phase 0 physical `u16` version value.

A frame-valid Hello whose payload violates these rules reaches the grammar-specific recognition-failure edge with a `RecognitionReason[Hello]`; it is not treated as a framing failure.

## Begin payload

`Begin` is encoded as:

```text
u64be length
u8    kind_length
bytes kind[kind_length]
u8    digest_alg
bytes digest[32]
```

Rules:

- `kind_length` is `1..255`;
- kind bytes are opaque and uninterpreted by the codec; this selects a concrete byte representation without inventing a compiler-level `PayloadKind` enum;
- `digest_alg = 01` denotes SHA-256;
- SHA-256 digest bytes are exactly 32 octets;
- there are no trailing bytes.

The payload length is therefore exactly `42 + kind_length`.

A frame-valid Begin with an invalid kind length, unsupported digest algorithm, wrong payload size, or trailing bytes reaches `RecognitionReason[Begin]`.

## Integer representation

All multibyte integers in this codec are unsigned network order (big-endian):

- frame payload length: `u16be`;
- Hello version count: `u16be`;
- Hello versions: `u16be`;
- Begin payload length: `u64be`.

No host-layout structs are serialized.

## Handle boundary

Compiler-visible runtime handles remain opaque:

- `VersionSet`;
- `PayloadKind`;
- `SHA256Digest`;
- recognized `Hello`/`Begin` records;
- recognition reasons;
- transport, pending, and frame owners.

The shared codec provider owns their native representation. Only the canonical bytes above cross the control-wire boundary.

The codec does not weaken the existing identity contracts: the exact VersionSet passed to `send_hello` is serialized, the exact Begin length/kind/digest operands are serialized, and the server recognizer materializes record/reason handles from the exact received frame.

## Native fixture gate

The runtime gate checks byte-for-byte fixtures for both record types, client-to-server round trips over a shared in-memory transport, concatenated frame commit boundaries, framing rejection, and grammar-specific recognition failure for malformed-but-framed payloads.

The same C implementation defines the client serializer and server frame/recognition primitives. There is no independently maintained encoder/decoder pair.

## Competence boundary

This profile closes the Phase 0 concrete control codec/framing obligation. It does not claim:

- correctness of the external SHA-256 computation primitive beyond the existing provider obligation;
- operating-system socket I/O;
- the source-to-Systems projection bridge;
- the final integrated native upload demonstrator.

Those latter two are the remaining Phase 0 convergence tasks.
