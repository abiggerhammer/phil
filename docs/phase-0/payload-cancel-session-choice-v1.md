# Phase 0 payload/cancel semantic session choice v1

Status: Systems candidate

This slice normalizes the label-only `payload` / `cancel` choice using the semantic session-choice representation introduced for the final response.

## Systems representation

The locally choosing endpoint uses:

```text
OpSessionSelect transport label maybePayload decision
```

For Phase 0:

```text
client.cancel:
  OpSessionSelect client.transport "cancel" Nothing

client.payload:
  OpSessionSelect client.transport "payload" Nothing
```

The peer-facing server side uses:

```text
TermSessionOffer server.transport {
  "payload" -> (Nothing, server.payload)
  "cancel"  -> (Nothing, server.cancel)
}
```

The old representation is removed from the successor candidate:

```text
server.payload_choice : Bool
receive payload/cancel label -> server.payload_choice
TermBranch server.payload_choice ...
```

No numeric discriminator, wire byte, packet layout, or runtime decoder is chosen in this slice.

## Local computation remains local computation

`should_cancel_upload()` is not a session action. Its result remains:

```text
client.should_cancel : Bool
TermBranch client.should_cancel client.cancel client.payload
```

That local Boolean decides which protocol label the client subsequently selects. Keeping these two levels separate prevents a local implementation decision from being confused with peer-visible protocol state.

## Generic verification

The Systems verifier requires every `OpSessionSelect` to have:

- an existing exact `TransportHandle`;
- a non-empty semantic label;
- an existing payload value when a payload is present;
- a selected lowering decision.

The Phase 0 witness additionally checks the exact duality:

- client `select payload` ↔ server `payload` arm;
- client `select cancel` ↔ server `cancel` arm;
- both use the exact component transport;
- neither arm carries a payload;
- the legacy anonymous server discriminator and generic label-receive operation are absent;
- the final `accepted(id)` / `rejected(reason)` session choice remains unchanged.

## Backend competence boundary

This is deliberately a Systems-only normalization. Generic LLVM lowering maps an unlowered `OpSessionSelect` to an accidental-poison marker, which the LLVM verifier rejects. `TermSessionOffer` already fails closed as unjustified unreachable in generic lowering.

A successor target slice must explicitly choose and validate the physical payload/cancel select/offer representation before LLVM certification can succeed.
