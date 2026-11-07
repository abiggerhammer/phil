# FSEM-01 — bounded two-owner resource-context frame bridge

> **Status:** non-normative, bounded Core.Context tests, canonical versioned
> wire, and Rocq extensional frame lemmas. Tracks [FSEM issue #1613](https://github.com/abiggerhammer/phil/issues/1613).
> This is NOT a general two-owner source checker, Haskell-to-Rocq state
> refinement, or whole-source type-soundness theorem.

## Scope and actual production evidence

The previous [CONTEXT-V1 slice](formal-semantics-resource-context-wire-fsem01-v1.md)
checked one source-derived Bytes[8] linear owner with a scoped shared view.
It refused additional owners. This slice tests a **distinct live spectator
owner** while the primary is loaned and later consumed.

The [Haskell driver](../../test/Phase1FSEM01TwoOwnerContextMain.hs) calls
the genuine Grammar-v1 parser and production source borrow checker on the
accepted and BorrowEscape source specimens, confirming ordinary/traced
parity. It obtains two different actual Core.Name identities from the
existing ASCII and Unicode declaration-root specimens.

**Important limitation:** These are independently checked source fragments.
The driver **composes** those independently resolved owners into one real
Core.ResourceContext by invoking the production Core.Context.insertBinding
operation. This is a Core-level two-owner test, **not** a claim that Phil's
surface checker already accepts a single two-owner source program. That
source simulation remains an open FSEM-01 obligation.

For each actual source-derived checkpoint the test constructs the complete
two-owner Core context with the real insertion API, then compares the
results of real startSharedLoan, endSharedLoan and consumeLinear calls to
the exact expected subsequent context. It proves operationally in Haskell
that the spectator retains its type and remains unloaned, even while the
primary is borrowed or consumed. Independently consuming the spectator
during the primary loan leaves the primary binding and active loan intact.
The actual BorrowEscape error prefix cannot consume its borrowed primary
or fabricate a post-error closure.

Negative conformance includes an unexpected third owner, foreign loan,
extra unrestricted/affine entry, missing spectator, wrong type and
role-identity corruption. Error classification is checked specifically,
not merely any rejection.

## A separate versioned two-owner wire

The new ASCII [CONTEXT2-V1](../../proof/Phil/Surface/SurfaceTwoOwnerContext.v)
format is independent of the original OBS-V1 and CONTEXT-V1 contracts.
It contains eight length-framed fields: primary and spectator source
SHA-256 hashes, both declaration-root UTF-8 hex names, both exact
source-resolved Core.Name UTF-8 hex identities, the full resource-state
sequence, and the primary terminal outcome.

Each checkpoint has phase/unrestricted/affine/linear/loans fields.
The full linear binding Map is represented in fixed *role order*;
the actual Map key domain and every Ty are checked before representation.
After successful consumption only the spectator remains. The full loan
Set is also checked: a foreign member cannot disappear silently.

[Independent validation](../../scripts/fsem01_two_owner_witness.py)
joins each new artifact to two actual OBS-V1 specimens; it rejects
noncanonical framing, wrong IDs, forged state/outcome or source fields,
and unknown versions. It regenerates Rocq equality witnesses from
**exact emitted bytes**, not from a manually copied state model.
Python/Haskell implementations are independent of the Rocq kernel and
remain stated trust boundaries.

## Rocq proof scope

[SurfaceTwoOwnerContext.v](../../proof/Phil/Surface/SurfaceTwoOwnerContext.v)
proves the versioned decoder's valid-record roundtrip, exact owner and
foreign-key lookups, and *frame* lemmas: a successful linear shared-loan
start, end, or primary consumption preserves the spectator's binding
and loan lookups, under explicit distinct-owner premises. A live primary
loan prevents primary consumption. The Rocq Context is an extensional
finite lookup model, not an extracted implementation of Haskell Map/Set.

[CI](../../.github/workflows/fsem01-two-owner-context.yml) strictly
builds/typechecks the real Haskell checker and tests, checks independent
source-derived OBS-V1 bindings and two-owner artifacts, regenerates
witnesses, compiles Rocq 9.2 without admissions, and records source,
wire, and proof hashes. PR-only CI supersession applies.

## Remaining obligations

A real single-source two-owner Grammar-v1 program (positive and minimally
rejected), general finite-map/type/mode representation and refinement,
captures/joins/loops, Unicode Text carrier proof, and full source error
simulation remain open. This slice does not discharge satisfies C or
promote non-normative formal typing drafts to authority.
