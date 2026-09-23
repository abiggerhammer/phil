# Phase 1 audit remediation: recognition continuation binding

Stable finding: `PHIL-AUD-SESSION-CONTINUATION-BINDING-001`  
Audit extension: `PHIL-AUDIT-20260921-RECOGNITION-REENTRY`  
Original frozen source: `a9f2c745686d8ae1b923e21045554f4864956e76`

## Finding extension

The ordinary `send`, `receive`, `select`, and `offer` continuation-instantiation gap
was repaired separately. The recognition-backed ingress path remained intentionally
outside that repair.

For `receive_frame`, Core records the protocol message binder in `PendingRecvSpec`.
Recognition then proves provenance for the particular pending owner, grammar, and
frame. Before this remediation, `commitReceive` consumed that pending capability and
installed `pendingContinuation` unchanged. Surface could therefore bind the recognized
semantic value under a new source name while the continuation still referred to the
old formal binder. An unrelated ambient value with that spelling could satisfy the
continuation, while the genuine recognized value could fail to do so.

## Repair

Recognition now assigns each successful parsed witness a stable logical occurrence
term derived from its checked provenance tuple: pending owner, grammar, frame, and
trusted parsed-value identity. The term is logical identity only; it is not a runtime
handle or a newly live resource.

`commitReceive` now reuses the binder-aware `instantiateMessageStep` mechanism from
the ordinary session repair. After the pending capability and witness have passed the
existing owner/grammar/frame checks, the receive-frame formal binder is instantiated
with that recognized occurrence before the successor endpoint is returned.

Surface preserves the same occurrence identity through `parsed.value`. Record-field
aliases from a nonlegacy parsed witness are rooted at the recognized occurrence.
`shapeForBinding` already preserves existing field aliases, so source bindings such as
`got = parsed.value` and later unrestricted aliases remain presentations of the same
logical occurrence rather than creating new identities.

This deliberately does not identify the continuation with a source spelling. In
particular, an ambient `begin.length` is distinct from the recognized frame even when
both values have grammar `Begin`.

## Permanent replay

`test/Phase1AuditRecognitionContinuationBindingMain.hs` covers the public parser,
checker, and intrinsic-verification route plus the Core commit boundary:

- S01: `got = parsed.value`; a continuation using `got.length` is accepted;
- S02: an unrelated ambient `begin.length` cannot satisfy that continuation;
- S03: the conventional source name `begin` is accepted when it denotes the actual
  parsed value rather than an ambient value;
- S04: a continuation independent of the received frame remains unchanged;
- S05: a second unrestricted alias of the parsed value retains the occurrence;
- R01/R02: recursive re-entry allocates a fresh recognized occurrence, accepting the
  second frame's own dependency and rejecting reuse of the first frame's dependency;
- C01: Core `commitReceive` installs the dependent continuation instantiated with the
  provenance-derived occurrence; and
- C02: Core leaves an independent continuation unchanged.

The dedicated workflow also replays the ordinary session-continuation remediation,
recognition-grammar remediation, and existing Surface/value/refinement controls.

## Assurance boundary

This closes the finite Haskell implementation/public-consumer recognition/commit
extension of `PHIL-AUD-SESSION-CONTINUATION-BINDING-001`: the checked recognized frame
occurrence now determines both the source-visible record aliases and the successor
session dependency.

Resource ownership is unchanged. The pending capability is still consumed once;
recognition's existing owner/grammar/frame provenance checks remain authoritative; no
owner or payload is restored or duplicated. The logical occurrence term has no
resource-zone entry.

`instantiateMessageStep` still fails closed where a Phase 1 type constructor requires
a name-only substitution that cannot represent the opaque recognized occurrence.
Broader nested dependent-message expressiveness remains the separate
`D-MSG-NESTED-01` coverage obligation rather than being silently approximated here.

This remediation does not alter Rocq proofs or proof correspondence, recognizer/native
ABI behavior, LLVM lowering, runtime byte parsing, or Certified status.
