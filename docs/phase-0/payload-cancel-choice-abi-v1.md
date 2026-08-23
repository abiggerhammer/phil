# Phase 0 payload/cancel choice ABI v1

This profile physically lowers the semantic `payload` / `cancel` session choice materialized in Systems by PR #62.

It is deliberately narrow. It fixes the exact Phase 0 representation for this one payload-free choice without defining a general session-label wire format or outer frame envelope.

## Runtime ABI

Generated LLVM uses two explicit transport-bound primitives:

```llvm
declare void @phil_runtime_select_payload_cancel(ptr, i8)
declare i1 @phil_runtime_receive_payload_cancel(ptr)
```

No ambient current transport, current session label, or last-choice state is permitted.

## Canonical wire representation

The choice occupies exactly one octet:

| Semantic label | Octet | Receiver result |
| --- | ---: | --- |
| `cancel` | `0x00` | `false` |
| `payload` | `0x01` | `true` |

All other octets are reserved in v1.

The client lowering supplies only the two canonical constants. The runtime selector writes exactly that one octet to the exact client transport.

The server runtime receiver reads one octet from the exact server transport, validates it, and only then returns a Boolean suitable for target control flow. `true` therefore means the already-validated semantic `payload` branch; `false` means the already-validated semantic `cancel` branch.

Early EOF and reserved octets are malformed protocol input. The runtime must not return normally in either case, and generated code must not invent a Phil CFG edge for them.

## Control-flow correspondence

The source/local decision remains distinct from protocol choice:

```text
should_cancel_upload() : Bool
       |
       +-- true  --> select cancel  --0x00--> peer cancel continuation
       |
       +-- false --> select payload --0x01--> peer payload continuation
```

The Boolean result of `should_cancel_upload()` is not itself protocol data. Only the subsequent explicit `OpSessionSelect` becomes a wire label.

On the server, the semantic Systems offer

```text
TermSessionOffer server.transport {
  "payload" -> server.payload
  "cancel"  -> server.cancel
}
```

lowers to one validated runtime receive and target branch. The runtime Boolean is therefore a target representation of this exact two-label choice, not a replacement for the Systems-level label identities.

## Failure and framing boundaries

The Phase 0 source language provides no failure edge for `select payload` or `select cancel`. Physical write failure is therefore a residual runtime assumption in this profile; it is not silently translated into either semantic branch.

This profile does not define outer framing. The one-octet choice representation is the complete representation of this session action itself. A future shared transport/framing profile may embed this octet in a larger frame without changing the semantic label mapping.

## Assurance scope

`PHIL-LLVM-CERT-009` is translation-only authority. It may establish:

- exact client and server transport identity;
- `payload -> 0x01` and `cancel -> 0x00` in generated LLVM;
- exact server continuation mapping after validated receive;
- elimination of the previous generic select/receive-label calls;
- absence of ambient choice state;
- preservation of the local `should_cancel_upload` branch;
- preservation of the already-lowered final accepted/rejected response boundary.

It does not prove runtime I/O implementation correctness, malformed-input non-return, physical write success, LLVM 18 correctness, linking, or native execution. Those remain explicit runtime/toolchain gates.
