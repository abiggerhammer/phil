# Phase 1 aggregate schema contract closeout

**Audit item:** `D-AGG-SCHEMA-01`  
**Implementation review base:** `e267755a92f2c4a3a75b70d05945606dd32388b2`  
**Lane:** `impl-audit`

## Result

The supported Phase 1 aggregate helper routes are **explicit-schema interfaces**, not
general source-to-owner elaborators. The Grammar-v1 record/data declaration views
preserve exact checked type information, source order, structural modes and payload
shape, but deliberately do not mint enclosing nominal declaration identity or
whole-declaration uniqueness authority.

This closeout keeps that boundary. It does not infer owner/schema identity from a
display name, structural mode, compact carrier, or a new semantic flag. Instead it
makes the one mandatory consumer-side condition that the existing helper APIs need:
an explicitly supplied field/constructor schema must be unambiguous **before** a
name/tag lookup can discard multiplicity.

No consumed owner is restored.

## Supported record route

| Stage | Production source | Contract |
| --- | --- | --- |
| Declaration producer | [`Parser.hs`](https://github.com/abiggerhammer/phil/blob/e267755a92f2c4a3a75b70d05945606dd32388b2/src/Phil/Surface/GrammarV1/Parser.hs) | Structural Grammar-v1 record declaration, retaining source field order/spelling. |
| Checked typed view | [`RecordFields.hs`](https://github.com/abiggerhammer/phil/blob/e267755a92f2c4a3a75b70d05945606dd32388b2/src/Phil/Surface/GrammarV1/RecordFields.hs) | `grammarV1CheckedClosedRecordMode` checks each supported closed field through `grammarV1CheckedTypeMode`, retaining exact `Ty` (including refinements), exact mode, focusing trace, and source order; Core nominal mode checking owns aggregate mode. Duplicate spelling is deliberately retained here. |
| Declaration/schema association | **Explicit caller premise** | Phase 1 has no general Grammar-v1 record declaration-to-owner exporter. A caller using the Core helper supplies the owner and the complete `[OwnedField]`; this closeout does not manufacture nominal identity from the local checked view. |
| Owner admission | [`Context.hs`](https://github.com/abiggerhammer/phil/blob/e267755a92f2c4a3a75b70d05945606dd32388b2/src/Phil/Core/Context.hs) + caller | The actual aggregate occurrence is an ordinary restricted resource binding. The helper does not synthesize or replace that owner. |
| Schema competence | [`DataDestruction.hs`](https://github.com/abiggerhammer/phil/blob/e267755a92f2c4a3a75b70d05945606dd32388b2/src/Phil/Core/DataDestruction.hs) | `checkOwnedFieldSchema` rejects duplicate supplied field identities before any disposition map or field-name lookup can erase multiplicity. Exact supplied modes/types are otherwise unchanged. |
| Borrow/projection | [`DataBorrow.hs`](https://github.com/abiggerhammer/phil/blob/e267755a92f2c4a3a75b70d05945606dd32388b2/src/Phil/Core/DataBorrow.hs) | `beginBorrowedAggregateField` first validates schema uniqueness, then starts a real shared loan on the actual owner. The borrowed view retains the selected field's exact supplied mode/type and loan end restores the original context. |
| Consuming elimination | [`DataDestruction.hs`](https://github.com/abiggerhammer/phil/blob/e267755a92f2c4a3a75b70d05945606dd32388b2/src/Phil/Core/DataDestruction.hs) | The actual restricted owner is consumed and only explicitly bound fields are installed with their exact supplied modes/types. Linear fields cannot be omitted. |

The important distinction is that `RecordFields` remains a duplicate-preserving
checked **view**. Whole-schema uniqueness becomes mandatory only when the Core
consumer is about to perform name-based selection/disposition. This avoids turning
a useful structural/type projection into a nominal declaration checker.

## Supported sum/data route

| Stage | Production source | Contract |
| --- | --- | --- |
| Declaration producer | [`Parser.hs`](https://github.com/abiggerhammer/phil/blob/e267755a92f2c4a3a75b70d05945606dd32388b2/src/Phil/Surface/GrammarV1/Parser.hs) | Structural Grammar-v1 data declaration, preserving variant order and payload syntax. |
| Checked typed view | [`DataVariants.hs`](https://github.com/abiggerhammer/phil/blob/e267755a92f2c4a3a75b70d05945606dd32388b2/src/Phil/Surface/GrammarV1/DataVariants.hs) | `grammarV1CheckedClosedDataMode` preserves nullary/tuple/record payload shape, ordered variant and record-field identities, tuple arity/order, exact checked payload types/refinements and modes, and Core-checked aggregate mode. It deliberately does not establish enclosing nominal declaration identity. |
| Declaration/schema association | **Explicit caller premise** | The Core sum helper consumes a supplied `[SumConstructor]` tag/payload table and an actual owner occurrence. Phase 1 does not claim that constructor tags are generally exported from Grammar-v1 declaration spelling. |
| Constructor competence | [`DataSum.hs`](https://github.com/abiggerhammer/phil/blob/e267755a92f2c4a3a75b70d05945606dd32388b2/src/Phil/Core/DataSum.hs) | `selectSumConstructorPayload` now rejects duplicate supplied tags before its lookup and validates the selected payload through `checkOwnedFieldSchema`. A first matching duplicate tag/field can no longer stand in for schema authority. |
| Consuming elimination | [`DataSum.hs`](https://github.com/abiggerhammer/phil/blob/e267755a92f2c4a3a75b70d05945606dd32388b2/src/Phil/Core/DataSum.hs) → [`DataDestruction.hs`](https://github.com/abiggerhammer/phil/blob/e267755a92f2c4a3a75b70d05945606dd32388b2/src/Phil/Core/DataDestruction.hs) | The selected exact payload is routed to ordinary consuming aggregate elimination. The original sum owner is consumed; exact selected field modes/types are installed and remain subject to ordinary linearity. |

The constructor tag table and owner/declaration relation remain explicit supplied
Phase 1 premises. Tag equality is therefore used only *within* an already supplied
schema, after uniqueness has been established; it is not treated as nominal
declaration identity.

## Separate operational record route

The older operational Surface `Hello`/`Begin` path has its own explicit supplied
schema in
[`Surface/Check/Support.hs`](https://github.com/abiggerhammer/phil/blob/e267755a92f2c4a3a75b70d05945606dd32388b2/src/Phil/Surface/Check/Support.hs).
`constructValue` obtains `recordShape`, rejects duplicate/extra/missing source
assignments, checks type/sort compatibility, and `readField` projects from the
resulting record shape. That already repaired
`PHIL-AUD-CONSTRUCTOR-SCHEMA-001` route is evidence for an explicit-schema
interface, not a general Grammar-v1 declaration exporter, and is not changed here.

The ordinary `philc` runnable path and the whole-source handoff/verification bundle
likewise do not become aggregate semantic-admission routes as a consequence of this
closeout. Structural parsing or content binding is not upgraded into schema authority.

## Executable preservation evidence

`test/Phase1AuditAggregateSchemaContractMain.hs` composes the real Grammar-v1
checked views with the supported explicit Core interfaces and checks:

- a record declaration retains source order, `U32`, a transparent-claim refined
  `U8`, `Bytes[7]`, exact Unrestricted/Linear modes, and a Linear aggregate mode;
- the supplied record schema can borrow the exact `Bytes[7]` field without
  manufacturing ownership, end the loan back at the original context, then consume
  the owner and restore exact successor modes/types with linear one-use;
- a duplicate-spelling record still succeeds at the deliberately
  duplicate-preserving checked-view layer, but the supplied consuming schema rejects
  before field lookup;
- a data declaration retains nullary, tuple and record payload shape, source variant
  order, exact checked types/refinements and modes;
- an explicitly supplied constructor-tag association selects and consumes that exact
  payload without restoring the sum owner; and
- duplicate supplied constructor tags or duplicate selected payload fields reject
  before first-match/name-based lookup.

The dedicated Haskell-only workflow also reruns the established checked-record,
checked-data-mode, record-destruction, aggregate-borrow and consuming-sum suites.
Independent-audit retains ownership of the historical external replay packet and its
independent review.

## Scope

This is a bounded Phase 1 contract/caller-map closeout plus a narrowly necessary
consumer hardening. It does **not** add a general aggregate compiler, a declaration
registry, nominal schema tokens, a source-to-owner exporter, proof-only/Rocq changes,
LLVM claims, or a final release certificate. It does not change the duplicate-
preserving Grammar-v1 views and does not infer association from spelling, mode or
compact structural carriers.

Within these supported Core helper routes, `D-AGG-SCHEMA-01` is therefore reduced
to an explicit supplied-interface premise with ambiguity rejected at the competent
consumer. Any future general source-declaration-to-owner route must establish its own
nominal association rather than reusing this supplied-interface closeout as that
authority.
