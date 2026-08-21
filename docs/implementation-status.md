# Phil Core implementation status

This file tracks the executable checker against the accepted Phase 0 Core judgments. It is intentionally stricter than a conventional roadmap: an item is either implemented in the checker, represented only as a design document, or not started.

## Implemented in the bootstrap slice

- `Γ` unrestricted bindings remain reusable.
- `A` affine bindings may be consumed at most once.
- `Δ` linear bindings are consumed exactly once along complete continuing paths.
- Shared-loan state is checker bookkeeping attached to owners in `A` or `Δ`, not a fourth structural zone.
- An owner cannot be consumed while a shared loan is live.
- A loan must end before the owner can be consumed.
- Continuing branch joins require identical linear residue.
- Affine residue is conservatively forgotten when a capability is absent from any continuing branch.
- Complete-component checks can reject leftover linear resources and escaping loans.
- Obligation IDs are unique within a checking state; re-emitting the identical obligation is idempotent, while reusing an ID for a different obligation is rejected.

## Implemented in the session-progression slice

- Session heads represent `!`, `?`, `⊕`, `&`, `end[o]`, guarded recursion, and recursion variables.
- `⊕`/`&` branches carry an optional payload binder/type as required by ADR-003 rather than only a label and continuation.
- A successful structural session step consumes the current linear endpoint and creates at most one explicitly fresh successor endpoint at the declared continuation.
- Send and ordinary non-grammar receive expose their declared message binder/type to the next checker layer.
- Internal selection and external offer reject the wrong polarity and reject undeclared labels.
- Branch selection exposes the branch payload specification and exact continuation.
- Declared close consumes an `end[o]` endpoint only when the requested outcome exactly matches.
- Guarded recursive heads are unfolded only enough to expose a communication head; unguarded self-recursion and unbound session variables are rejected.
- Structural duality is executable and involutive over the represented session forms.

The generic session API deliberately refuses grammar-backed receive progression. `Frame[G]` receive semantics belong to the recognition-gated ingress layer below rather than to ordinary `receiveEndpoint`.

## Implemented in the process/control slice

- Process paths carry one of `Continue`, `Return`, `Closed`, or `Failed` together with their checker state.
- Sequential composition advances only `Continue` paths. `Return`, `Closed`, and `Failed` paths do not execute later statements.
- `Return` preserves its residual affine/linear resources for the eventual return/interface boundary but cannot let a shared loan escape.
- `Closed` and `Failed` are terminal: they are accepted only after all linear resources and active loans on that path have been explicitly discharged.
- Local branch checking preserves separate path results internally rather than collapsing mixed `Return`/`Continue`/terminal outcomes into a single invented state.
- Continuing branch paths are checked with the existing structural join rule: linear residue must match, unrestricted residue must match, and affine residue is conservatively weakened.
- Terminal `Closed`/`Failed` paths are excluded from the continuing resource join and therefore do not manufacture dummy endpoints merely to rejoin control flow.
- Mixed `Return`/`Continue` branches preserve the return path's residual resources while independently normalizing the continuing path residue.
- Branch-local residual obligations remain path-sensitive across exclusive branches. The process layer does not turn obligations from mutually exclusive arms into unconditional obligations.

This path-set representation is an internal checker device for preserving the normative per-path judgment. Later return-value/interface checking may validate and reconcile `Return` paths without changing the rule that declared/fatal terminal paths carry no continuing linear residue.

## Implemented in the recognition-gated receive slice

- Grammar-backed session messages have an explicit `TyFrame GrammarId` representation rather than relying on opaque type-name strings.
- `receiveFrame` consumes `Endpoint[?(x : Frame[G]).S]` and produces a unique linear `TyPendingRecv` owner containing source-endpoint identity, grammar identity, frame identity, binder, and continuation.
- No semantic successor endpoint exists while the pending receive is unresolved.
- Generic `receiveEndpoint` rejects both direct and refined `Frame[G]` receives, closing the structural bypass around recognition gating.
- External-choice payloads that are grammar-backed fail closed until an equivalent pending-state protocol is implemented for that shape.
- A pending owner may be inspected only through a scoped shared raw-view loan. The loan blocks both `commitReceive` and fatal pending destruction.
- Raw-view tokens become unusable for recognition after the shared loan ends.
- Trusted recognition success constructs an opaque `ParsedWitness` carrying pending-owner, grammar, frame, and semantic-value identity. Its constructor and provenance fields cannot be rewritten outside `Phil.Core.Recognition`.
- Trusted recognition failure carries matching pending-owner, grammar, frame, and failure detail but constructs no parsed witness.
- `commitReceive` requires parsed evidence matching the exact pending owner, grammar, and frame; consumes the pending owner; and creates exactly the declared successor endpoint.
- `commitReceive` refuses to reuse either the pending identity or the already-consumed source endpoint identity.
- Recognition failure may consume the pending owner only after the raw loan ends and only with matching failure provenance; it creates no successor endpoint.
- An unresolved `PendingRecv` remains an ordinary live linear resource and therefore prevents component completion.

The trusted-recognition result functions model the assurance boundary where a Phil-generated recognizer or audited extension reports success/failure. This slice does not pretend to implement a grammar runtime: complete consumption, determinism, and byte-to-value interpretation remain responsibilities of that trusted recognizer boundary and later executable grammar tooling.

## Next checker slices

1. Bidirectional value checking and explicit definitional/propositional equality boundary.
2. Refinements, evidence matching, explicit transport, and stable residual obligation generation.
3. Deterministic focusing/elaboration rules.
4. Parser and surface-to-Core elaboration.
5. Conformance harness over the accepted/rejected `.phil` corpus.
6. Assurance-ledger handoff and manifest verification.

## Explicit current non-goals

The checker still does not claim source-level Phil conformance. In particular it does not parse Phil syntax, project dependent session types from a global protocol, perform dependent value substitution, execute grammar recognizers, solve refinements, validate return values against a provider signature, validate the upload protocol end-to-end, or lower to systems/LLVM IR. Transport-acquisition failure for `receiveFrame` is still represented by the accepted primitive contract rather than simulated inside the structural checker.
