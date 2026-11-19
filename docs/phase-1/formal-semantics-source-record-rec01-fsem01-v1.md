# FSEM-01 REC-01: checked closed source-record fields, dispositions and native Core bridge

**Status: proposed bounded implementation; not general MODE-02/DATA-06 closure.**
Tracking [#1919](https://github.com/abiggerhammer/phil/issues/1919),
FSEM parent [#1613](https://github.com/abiggerhammer/phil/issues/1613).
Source and checked mode authority remains the accepted Grammar-v1 parser,
`grammarV1CheckedClosedRecordMode`, and existing Core nominal record-mode
and resource/destruction consumers. The 46-row COVERAGE-1 register remains a
historical 2026-11-10 baseline: **18 bounded/20 general gap/8 handoff** is not a
current completion percentage and no DATA-06 general row has been promoted.

## Original source witness and exact competence

A closed nongeneric record declaration, followed by one function of the
*same parsed named type*, with one flat record pattern and checked original
parameter/return source occurrences:

```phil
record Packet { tag : U8, payload : Bytes[8], flag : Bool }

fn unpack(packet : Packet) -> Bytes[8] satisfies C {
  let Packet { tag, payload, flag } = packet;
  return payload;
}
```

The adapter additionally admits source-checked aliases such as
`Packet { tag = metadata, payload = owned }`, reordered fields and omission
of Unrestricted fields. Exactly **one** Linear Bytes[N] field must be
source-declared and bound to the actual returned source binder, and
all other fields must independently check as Unrestricted Unit/Bool/U<n>.
The record's derived mode is Linear, with no nominal strengthening evidence.
No generic, requirement-bearing, alias, nested-field-pattern, multi-linear,
dependent/proof/opaque, explicit independently strengthened record mode or
external nominal type is inferred to be competent. Noncompetence remains
`Nothing`, never a normative invalid-source judgment.

Every label and source binder identity is derived from the real original
declaration and checked `PatternBinderScope`/`LetPatternScope` sequence.
`Core.DataDestruction.checkFieldDispositions` checks the source *labels*
against the exact **declared** field schema, detecting duplicate/unknown
fields and missing Linear disposition. The source-checked label=>binder
mapping is then used to allocate exact fresh native successors, not
caller-selected display names or forged proof evidence.

## What is actually executed, and what is NOT

The production **Core** `DataDestruction.consumeAggregateFields` operation
consumes a single Linear aggregate owner and restores exactly the
source-checked field destinations, with Unrestricted omissions permitted.
Independent `Core.Context.useBinding` and `insertBinding` operations
replay its full resulting four-zone resource context. The test
[Phase1FSEM01Rec01SourceRecordDispositionMain.hs](../../test/Phase1FSEM01Rec01SourceRecordDispositionMain.hs)
parses original .phil fixtures, replays the native transitions, checks
the one-shot Bytes[N] return and stale aggregate denial, checks lexical
alpha-renaming/root identity and isolates exact native/lexical/mode failures.

**Important:** `Phil.Core.Syntax.Ty` currently has **no nominal record
constructor**, and `Phil.Surface.Syntax.Pattern` currently has **no record
pattern constructor**. To exercise the existing native Core consumer, the
bridge uses an **internal TyOpaque carrier**, generated from the exact
source declaration name and parameter origin. It is an *explicit modeling
premise*, NOT a proven nominal type equality, actual source record
construction, certified ABI representation, or production Surface
record-pattern-elaboration result. This slice **cannot close** the general
MODE-02 / DATA-06 obligations without a separately reviewed record-type
representation and P9 Surface checker ownership decision. It does not
touch `src/Phil/Surface/Check/Engine.hs`.

## Rocq and trust

[SourceRecordFieldDispositionREC01.v](../../proof/Phil/Surface/SourceRecordFieldDispositionREC01.v)
imports the existing `Phil.Core.DataElimination` axioms-free theorem set
and proves conditional mandatory Linear binding, omitted-Linear rejection,
duplicate disposition failure, exact linear record-owner consumption and
fresh one-shot bound-successor properties. The real source label=>semantic
key relation, nominal record meaning, Haskell `Text/Map/Set` representation
and source-to-Core checker simulation are **undischarged premises**, not
derived by these theorems. No `Admitted`, `Axiom`, `Parameter` or
unexpected TCB change.

**Nonclaims:** no general record parser/type soundness, record construction,
field projection, sums, record recursion, multi-Linear field disposition,
generic/alias/nominal proof authority, FSEM-05 interpreter, FSEM-06
implementation refinement, P9 provider ABI, external assurance,
FSEM-07 graduation or FSEM-01 closure. The existing general gap rows
remain open after this bounded evidence lands.

The exact source HEAD must pass strict GHC 9.6.7 -Wall -Werror including
existing records/data and scope regressions, plus Rocq 9.2 kernel/check/
assumptions **before** a draft PR. Full exact-head hosted CI, fresh
post-READY claim guard, protected expected-head squash and exact trusted
claim release remain separate mandatory merge gates.
