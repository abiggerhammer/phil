# FSEM-05 selected SteveGet qualified original-source event semantics — proposed v1

**Status: implementation/proof candidate for independent FSEM-05 semantic-owner review, not accepted source/native correspondence.**
Owner: [#1912](https://github.com/abiggerhammer/phil/issues/1912), family-level `fsem-05` only. This tranche does **not** satisfy global FSEM-05 exit or P9-G3/P0–P6/R3/R4.

## Original object and producer (Haskell)

The executable selected source producer lives in **new**
`src/Phil/Surface/SelectedSteveGetExecution.hs` (and its one necessary
`phil-core.cabal` exposed-module entry). It **reparses and rechecks original
raw text**, not a caller-supplied `CheckedSourceBundle` or a hand-written
candidate AST. The standalone adversarial driver reads
`examples/steve/get.phil` (Git blob
`8de9853762201b516d7c05bfd5568e54acbd7dc8`) directly.

The producer constructs the explicit one-unit selected portable bundle with
persisted `site.steve.get`, `unit.steve.get`,
`decl:steve.get`, `instance.steve` / `inst:phase1.steve`,
and selected root `program:steve.get`. It calls
`checkPortableSourceBundle` then `buildCheckedSourceArchitecture`,
requiring declaration K = `decl:steve.get` and instance I =
`inst:phase1.steve`. It uses exactly the **free unrestricted**
`contentId : ContentId[SHA256]` binding, **zero formal parameters**,
expected Unit, the two exact source primitive signatures, and the
existing owned-buffer release transition from the Steve shell.
The unrelated external `SteveGet` callable signature is **not** used as
source-parameter evidence.

The whole selected ordinary `Phil.Surface.Syntax` AST is shape-reflected:
`decide blob_read(contentId)`; found `bytes`; the sole lexical
`borrow bytes as bytesView {digest_check(contentId,bytesView)}`;
`digestDecision` accepted/rejected arms each releasing exactly that owner
then returning Unit; and not-found/storage-failure Unit branches.
No extra statements, hidden side effects, alternate arm or changed
argument order can pass the selected reifier. The two `SourceSpan`
occurrences come from the **rechecked actual original AST**, not model
integers or target call names.

This is an independent selected input reflection for this **one**
ordinary-Surface shape. Its completeness outside this shape, parser
correctness, lineage persistence/trust, and source grammar revision
correctness remain representation boundaries. Reconstructed selected
one-unit K/I lineage is not a theorem of identity with every larger
persisted SourceBundle or an authenticated linked native source artifact.

## E, internal H and executable rules

`E` is an explicit response-supplying sequence. The selected Haskell
`SuppliedResponse` input has **only**
`(original SourceSpan, expected qualified operation, original contentId,
typed outcome/payload)`; digest adds the exact lexical `bytesView`
argument. It contains **no** owner, loan, serial or history. Mismatched
site, provider, id, view, program counter or response type **reject**
without mutation. Missing read/digest response **waits**; it does not
invent a found arm, assert provider fairness, or turn a timeout into a fatal.

A private, persistent per-session `SelectedWorld` supplies
`H=(namespace,nextOrigin,issued,retired,active,events)`. The only
allocation is by the transition itself:

1. At the **original read occurrence**, only the selected qualified
   `ReadFound(payload)` allocates `owner=H.next`; not-found and
   storage-failure allocate neither owner nor loan and terminate Unit.
2. With that exact live found owner, the lexical borrow transition
   mints `loan=H.next` and binds it to the owner.
3. The original ordered `digest_check(contentId,bytesView)`
   consumes E's typed digest result only while that owner and loan
   remain live; no post-close digest or substituted `contentId`/view.
4. Close retires the loan **without deleting issued history**;
   accepted and rejected paths each release the exact owner once and
   return Unit. Neither path performs an implicit destructor.
5. The next selected invocation uses the **same mutated world H**,
   not a new caller serial. A stale invocation handle cannot
   execute after completion. The `Data.Unique` world namespace
   distinguishes independently created worlds within the process,
   but this is **not** a durable cross-process or native pointer
   origin certificate.

Because `SelectedWorld` and `SelectedRun` constructors are private and
transitions use `atomicModifyIORef'`, an API caller cannot replay an
earlier mutable H snapshot, decrement its supply, or forge an owner
in a provider response. Recreating a process and native ABA/FFI
correspondence are outside this result; no `StablePtr` is an owner
credential. One non-reentrant selected invocation is active per world.

The corresponding independent Rocq definition is
`proof/Phil/Verification/FSEM05SteveGetSelectedSourceEvents.v`.
`selected_step_fn` is executable; `selected_source_step` has ten
independent declarative cases, not a graph-of-function definition.
Soundness, coverage, determinism, fresh owner/loan ordinal separation,
persistent issued/retired history across two identical-payload found
invocations, nonfound no-issue, wrong event rejection, waiting vs rejection
and fuel partiality are *proposed* named closed lemmas. The Rocq record
uses abstract naturals and does **not** itself establish concrete
Haskell `SourceSpan` or IORef-to-Rocq simulation.

## Exact clause → authority → definition → producer/consumer

| Selected clause | Previously accepted authority | New scoped definition, **requires independent owner approval** | Actual producer/consumer |
|---|---|---|---|
| Original order and selected arm only | [EXEC-ORDER](sequential-execution-order-proof-boundary-v1.md) determines bounded sequential selection, **but its GrammarV1Block is a different AST and externally chosen branch evidence** | Selected step PC is derived from exact ordinary-Surface AST and advances only on E's matching read/digest answer | `prepareSelectedSteveGet` via `checkPortableSourceBundle`; `transition` |
| K/I, free contentId and signatures | [SourceBundle](../../src/Phil/Compiler/SourceBundle.hs), [SourceArchitecture](../../src/Phil/Compiler/SourceArchitecture.hs), [Steve shell](../../src/Phil/Examples/Steve/ApplicationShell.hs) | Source read/digest call occurrence identity is the checked `SourceSpan` under selected K/I; caller id cannot change | Original rechecked AST, canonical env/qualification |
| Typed found/nonfound/failure | Existing [Surface checker](../../src/Phil/Surface/Check.hs) verifies **all** arms statically; [qualified providers](../../src/Phil/Examples/Steve/ProviderQualifications.hs) select contracts and conditions | E supplies exactly one dynamic branch/outcome at selected call; **static checker events do not assert it occurred** | `ReadResponse`/`DigestResponse` validated in `transition`; E is external |
| Fresh semantic owner and lexical loan | [EXEC-BIND](execution-binding-proof-boundary-v1.md) binds identity/release competence; [Core.Context](../../src/Phil/Core/Context.hs) checks loans, not persistent incarnation H | `ReadFound` mints internal owner; lexical borrow mints distinct loan from persistent H; impossible to consume a live loan | `SelectedWorld`, `stepSelectedSteveGet`, Rocq rules |
| Digest, close, release, Unit | Surface release-transition and provider resource discipline | Exact ordered original id/view digest under live loan; retire loan before release; found branches return Unit; no owner in other branches | Original checked AST plus PC transitions |

**Newly proposed semantic owner law (not inferred from existing static checks):**
given the rechecked selected *ordinary* SteveGet source occurrence
`blob_read(contentId)`, fixed qualified Blob/Digest identities,
and one competent typed provider world E, the selected
source-language evaluator consumes **E's actual chosen response**.
Only if that response is found does the evaluator issue an owner
origin from its own nonreusing H; the subsequent lexical borrow
issues its own live loan tied to that exact owner. This law must
be **independently derived/ratified** by FSEM-05's semantic owner.
It is not a result of `evalDecide` enumerating arms, a
`GrammarV1ExecutionChoice`, the native result tag, or an API
caller-provided `serial`.

## Hard boundaries / unproved facts

- The external E response supplier is a **semantic input**, not an
  authenticated observation of `SteveProviderBridge.steveBlobRead`.
  A malicious supplier can supply a well-typed `ReadFound` for
  the exact occurrence despite no linked native call; the current
  library does not purport to attest that link. The independent
  provider-event competence/receipt is the **smallest remaining
  operational authority review question**.
- `SourceSpan` matching authenticates equality **within this checked
  source representation**, not proof of native call provenance.
  The current producer consumes actual parsed AST, unlike the
  different `GrammarV1Block` AST.
- No theorem in the Rocq file asserts that GHC's actual AST/IORef
  transition implements its constructors. This source↔Rocq
  refinement/representation proof is independent remaining work.
- No LLVM or native FFI trace correspondence; no `StablePtr`
  identity, cross-process durability or ABA safety proof;
  no general program evaluator, arbitrary cancellation,
  fairness, fatality or hostile direct-ABI entry.
- `assumption:sha256-semantic-profile.v1`, selected BlobProvider
  publication/lifecycle/no-replace laws and all qualified
  SHA/Blob evidence assumptions remain **UNDISCHARGED**.
- No P9 G3/R1b/R2 proof, Core result binding, R3/R4, FSEM-06
  or whole-language FSEM-05 completion is claimed.

## Review/verification gate

The dedicated unprivileged
`.github/workflows/fsem05-steveget-selected-source-event.yml`
must pass strict GHC **9.6.7** source-rechecker/executable adversarial driver
and independent Rocq **9.2** compilation, named `Print Assumptions`,
forbidden admission scan and `rocq check` at **exact branch head**.
It must reject source AST mutations, wrong call occurrence,
missing E waiting, duplicate/premature release, view/id swaps,
nonfound owner allocation, digest after loan closure and
repeated identical-payload owner replay; it must not claim that
a syntactically well-formed supplied E is a native event certificate.

No PR or merge can be justified from this note alone. Before
opening the sole `fsem-05` PR, require the exact claim audit in
[#1613](https://github.com/abiggerhammer/phil/issues/1613),
no conflicting PR, a green focused preflight, and an
independently justified accepted new selected source-event rule.
Only after that may FSEM-06 #1913 be marked ready.
