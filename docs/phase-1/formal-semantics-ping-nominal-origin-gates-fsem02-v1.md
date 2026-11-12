# FSEM-02: source-derived Ping nominal Send/Receive gates

**Status: bounded, non-normative production/Core and conditional-model conformance.**
Follows protected merged #1738; #1613 remains open.

The independently parsed and checked complete Grammar-v1
`test/fixtures/fsem02-protocol-progression-v1/accepted.phil`
supplies two exact source binder identities and the Client Send and
Server Receive projections for Ping. The independently instantiated
binary family supplies the exact protocol instance revision.

```text
source Ping ; matched syntactic Send|Receive head ; liveInstance != expected
  => rejected(ProtocolInstanceMismatch endpoint expected actual)
source Ping ; matched head ; matching instance ; liveRole != expected
  => rejected(ProtocolRoleMismatch endpoint expected actual)
source Ping ; matched head ; instance AND role mismatched
  => rejected(ProtocolInstanceMismatch endpoint expected actual) first
source Ping ; matching head, instance and role
  => exact predecessor consumed; exact End Done successor linearly typed
```

`test/Phase1FSEM02ProtocolProgressionMain.hs` exercises **both**
production `ProtocolSendRequest` and `ProtocolReceiveRequest`
against three independent negative contexts and a matching positive
control, requiring exact native constructors and identity payloads,
rather than treating arbitrary failures as successful rejection. The
contexts preserve the same real source binder and projected local
Session head. The original parsed stale-close negative retains the
exact `GrammarV1ComponentSendCloseCloseMismatch` rejection class.

`proof/Phil/Core/FSEM02PingNominalOriginGates.v` models the
independently supplied nominal equality gate and conditionally proves
wrong-instance/wrong-role rejection, matching-identity delegation,
linear predecessor consumption and exact successor type for Send
and Receive, and no successor success under wrong instance. It
reuses `FSEM02ProtocolHeadProgression.v` and `SessionStep.v`.
`ConcurrencySemantics.v` remains a separately admitted rendezvous
model, not an extracted executable source semantics.

**External premises:** protocol instance admission, correct role
projection, activated endpoint occurrences, message/payload authority,
scheduler/rendezvous, terminal disposal, selected architecture root,
and assurance. Same local head does not prove nominal authority.
This slice does not prove global Haskell-to-Rocq refinement,
parser correctness, source program-wide certification or normative
graduation. No TCB, EBNF, branch rules or proof gates are changed.
