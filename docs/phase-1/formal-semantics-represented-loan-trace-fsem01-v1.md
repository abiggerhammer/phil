# FSEM-01 — represented owner identity across production loan checkpoints

> **Scope:** bounded Rocq model checkpoint proofs and executable conformance of actual Grammar-v1 Haskell traces. **Not** full Haskell-to-Rocq simulation or a new normative language rule. Tracks #1613.

## Evidence connected

The [production trace from #1626](formal-semantics-loan-transition-trace-fsem01-v1.md) observes actual Engine loan states and exact generated owner names. The [conditional loan proof from #1627](formal-semantics-exact-loan-transition-model-fsem01-v1.md) establishes exact linear-loan start and end in the existing Rocq Context model. The [declaration identity bridge from #1632](formal-semantics-declaration-identity-bridge-fsem01-v1.md) relates only a finite, duplicate-free root catalog to normalized binder identities; its positions are not persistent Phil identifiers.

The [new Rocq model](../../proof/Phil/Surface/SurfaceRepresentedBorrowTrace.v) composes these existing models. Under explicit catalog, resource-binding and inactive-loan premises, it constructs the **successful** start, close and terminal-consumption states. A separate theorem models the **rejected escape prefix**, where the owner remains present and the loan is active.

| Observed phase | Successful owner / loan | Escaping owner / loan |
| --- | --- | --- |
| Before loan | Present / inactive | Present / inactive |
| Loan started | Present / active | Present / active |
| Borrow body result | Present / active | Present / active |
| Loan closed | Present / inactive | Not reached |
| Terminal owner return | Absent / inactive | Not reached |
| Escape rejected | Not reached | Present / active |

The model has explicit lemmas excluding loan closure and terminal return from its rejection path. This is a statement about the **Rocq modeled path**, not a proof that every Haskell error follows it.

## Executable correspondence

[Phase1FSEM01RepresentedLoanTraceMain.hs](../../test/Phase1FSEM01RepresentedLoanTraceMain.hs) invokes the real Grammar-v1 parser and production borrow checker/tracer on admitted Bytes[8] examples. It obtains roots through production declaration-identity derivation, builds an explicit test-only catalog, and decodes every checkpoint's actual generated owner/view Core names to their resolved binder keys. It verifies exact mapped catalog identity, owner linear-binding membership and shared-loan membership with no extra owners or loans in the admitted one-owner fragment.

A separate fail-closed transition interpreter generates the expected successful and rejected checkpoint sequences. The tests compare them with production snapshots, check normal/traced checker parity, demand the precise BorrowEscape classification and message on rejection, and refuse fabricated catalog identities. Root examples include delimiter-shaped and Unicode values; catalog reordering changes only model IDs and leaves production names intact.

[CI](../../.github/workflows/fsem01-represented-loan-trace.yml) compiles the Rocq proof with version 9.2, rejects proof admissions, and builds/checks/runs the Haskell test with GHC 9.6.7 and -Wall -Werror. Only exact-head passing CI is evidence for this bounded slice.

## Explicit remaining obligations

- **Not a Haskell refinement theorem.** The Rocq Context model and executable production traces remain separate; no universal source-to-model simulation has been proved.
- **Representation boundary.** A finite NoDup catalog does not establish stable global Text-to-nat identity, catalog versioning, or Haskell Unicode Text to Rocq ASCII String equivalence.
- **Rejection semantics.** Tests assert the exact BorrowEscape prefix, but there is no Rocq theorem for runtime borrowed-view detection across arbitrary values or source execution.
- **Control boundaries.** A successful terminal return is not an ordinary continuing join/backedge. Existing ResourceScope continuing-boundary theorems are not substituted.
- **Out of scope.** Affine, pending receive, nested borrows, effects, arbitrary captures and whole-program satisfies C remain unproved.

**Next step:** version the owner-catalog provenance, and establish one explicit source-to-model step/error relation with narrowly defined translation or extraction assumptions before claiming source-level preservation.

## Following transition/error observation slice

[The bounded transition/error bridge](formal-semantics-step-error-bridge-fsem01-v1.md) checks every adjacent production checkpoint against an explicit fail-closed model step and ties the terminal phase to the actual production checker outcome. It tests forged continuations after `BorrowEscape`, bad owner identities/loan flags, and mismatched outcomes. The Rocq theorem proves the model has no successor from rejected/returned states; it **does not** establish universal Haskell refinement or an extracted source small-step semantics.
