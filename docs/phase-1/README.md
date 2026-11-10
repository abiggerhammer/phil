# Phase 1 implementation notes

This directory contains checker-, proof-, provider-, and Systems-facing records produced as Phase 1 implementation slices landed.

## Status ownership

Most `*-v1.md` files here are **historical slice records**, not continuously rewritten roadmaps. Their positive semantic claims describe the slice they accompanied, but statements such as “not yet,” “deferred,” or “this slice does not claim” describe the repository state at that point in history and may later become obsolete.

Current Phase 1 status is owned by the project **Logic Ledger** at claim level and the **Conformance Matrix** at case level. In the repository, checked proof/certification artifacts and executable conformance/correspondence tests are authoritative evidence over prose status summaries.

The important exceptions are documents that explicitly declare themselves current normative authorities, especially:

- [`surface-grammar-v1.md`](surface-grammar-v1.md), together with [`../../grammar/phase1-surface.ebnf`](../../grammar/phase1-surface.ebnf), for the Phase 1 concrete-syntax epoch; and
- any document whose own text explicitly states that it is a current normative specification rather than an implementation-slice record.

## CI operational safety

- [PR-head workflow supersession policy](pr-head-ci-supersession-policy-v1.md) — bounded migration of the highest-traffic PR checks to cancellation-safe concurrency groups, with automated guard tests and explicit exceptions for main/release and coordination workflows.
- [FSEM claim-release recovery](fsem-claim-release-recovery-v1.md) — independent trusted reconciliation when a close-event release fails before any job starts; includes exact merged-PR safeguards and manual fallback.

## Entry points for formal-methods review

- [Normative Phase 1 surface EBNF](../../grammar/phase1-surface.ebnf) — authoritative concrete syntax and token forms; successful parsing is not semantic acceptance.
- [Grammar-v1 status, lexical rules and versioning policy](surface-grammar-v1.md) — defines the concrete-syntax authority boundary and derivation of proof-facing grammar artifacts.
- [Syntax–semantics completeness audit](syntax-semantics-completeness-v1.md) — reconciles programmer-expressible choices against the accepted Phase 1 contracts; it does not independently make typing rules normative.
- [Phase 1 typing and semantics reader's guide](typing-and-semantics-reader-guide-v1.md) — non-normative map of existing semantic authorities, models and proof-scope caveats.
- [Three worked typing-rule families](typing-rules-worked-examples-draft-v1.md) — illustrative positive/expected-negative examples; not all negatives are executable conformance witnesses yet.
- [Formal-semantics judgment inventory (FSEM-00)](formal-semantics-judgment-inventory-v0.md) — proposed rule interfaces, translation boundaries and explicit outstanding evidence, tracked in [FSEM issue #1613](https://github.com/abiggerhammer/phil/issues/1613).
- [FSEM-01 resource and local typing exit-evidence matrix](formal-semantics-fsem01-exit-matrix-v1.md) — as-of-main per-rule source/production/Rocq coverage, six issue acceptance criteria, explicit joins/loops/capture/representation gaps and reviewable proposed exit sequence; **FSEM-01 remains open and non-normative**.
- [FSEM-01 J-1/J-2 parsed-source branch joins and terminal exclusion](formal-semantics-source-branch-join-fsem01-v1.md) — bounded real Grammar-v1 if-join predecessor projection into the production Core resource join; exact linear mismatch, stale owner, terminal exclusion, and conditional Rocq model; not general source if semantics.
- [FSEM-01 J-1/J-2 source affine join and branch-local scope cleanup](formal-semantics-affine-join-scope-fsem01-v1.md) — exact admitted nominal affine source owner, real pre/post branch-pruning resource checkpoints, affine intersection, isolated LinearCompletion and stale-use negatives, and conditional Rocq model; not general if/match source semantics.
- [FSEM-01 real source scoped loans across continuing joins](formal-semantics-scoped-borrow-join-fsem01-v1.md) — checked source borrow-view identities, real loan start/close versus BorrowEscape prefixes, native join prevention on active loans and conditional Rocq loan exclusion; non-normative bounded fragment.
- [FSEM-01 source-checked nonempty Bool join-state and invariant evidence](formal-semantics-bool-join-telescope-fsem01-v1.md) — real two-predecessor checked Bool phi and fresh post-join binder, narrowly discharged true/reflexive invariants, fail-closed type/proof negatives and conditional Rocq resource preservation.
- [FSEM-01 source-checked two-slot Bool join-state and ordered native insertion](formal-semantics-two-bool-join-telescope-fsem01-v1.md) — two exact source tuple operands, per-slot Bool type/mode checks, real ordered post-join Core bindings, failure-prefix tests and conditional Rocq frame preservation; no dependent/linear phi or runtime evaluator.
- [FSEM-01 L-1 source-checked Bool loop entry/backedge](formal-semantics-source-bool-loop-fsem01-v1.md) — actual parsed initializer/header/continue resources and bounded negative traces, plus conditional Rocq frame/loan lemmas; no general runtime loop semantics or termination.
- [FSEM-01 L-1 source-checked loop break and terminal Linear completion](formal-semantics-source-bool-break-fsem01-v1.md) — real scoped Bool header exit, native payload return, source-declared unpaid linear debt rejection and conditional Rocq model; no general loop execution.
- [FSEM-01 L-2 real parsed Linear loop owner transfer](formal-semantics-source-linear-loop-transfer-fsem01-v1.md) — source Bytes owner consumed into a fresh loop header, then consumed/rebound through continue and checked native reentry; exact stale, type and duplicate-owner negatives, conditional Rocq; no runtime loop execution.
- [FSEM-01 L-3 scoped loan inside Linear loop backedge](formal-semantics-source-scoped-loop-loan-fsem01-v1.md) — real source borrow-view lexical scope, native loan start/close and forbidden live-loan move/join, conditional Rocq, no dynamic iteration.
- [FSEM-01 C-1 source closure capture](formal-semantics-source-closure-capture-fsem01-v1.md) — parsed explicit closure captures through real native ownership moves and bounded borrowed-view scope checking; conditional model, not general callable elaboration.
- [FSEM-01 proposed loan-state correspondence](formal-semantics-loan-state-correspondence-fsem01-v0.md) — exact source binder/production resource identities, an explicit candidate Rocq relation, and undischarged source-to-model proof obligations (non-normative).
- [FSEM-01 executable production loan-state trace](formal-semantics-loan-transition-trace-fsem01-v1.md) — same checker transitions, exact live-owner/loan checkpoints and escaped-view error-prefix tests; not a source-to-Rocq theorem.
- [FSEM-01 first Rocq loan-transition proof slice](formal-semantics-exact-loan-transition-model-fsem01-v1.md) — conditional identity-preserving linear loan start/end proofs and explicit unproved Haskell/source encoding boundaries.
- [FSEM-01 binder-name encoding proof and production Text checks](formal-semantics-binder-name-encoding-fsem01-v1.md) — ASCII-string injectivity theorem with Haskell canonical codec tests; Unicode/Text representation and declaration-ID bridges remain explicit.
- [FSEM-01 bounded declaration-root representation](formal-semantics-declaration-identity-bridge-fsem01-v1.md) — duplicate-free finite catalog relation between normalized declaration IDs and actual Haskell root keys; catalog stability and Unicode refinement remain explicit.
- [FSEM-01 represented production loan-state checkpoints](formal-semantics-represented-loan-trace-fsem01-v1.md) — model start/close/terminal and rejected-prefix proofs, plus source-derived production trace ↔ bounded catalog identity and membership tests; no universal Haskell refinement.
- [FSEM-01 bounded transition and BorrowEscape error bridge](formal-semantics-step-error-bridge-fsem01-v1.md) — fail-closed model steps, no post-rejection successors, and actual production trace tampering tests; cross-language simulation still open.
- [FSEM-01 versioned source observation and checked wire decoder](formal-semantics-observation-wire-fsem01-v1.md) — deterministic, source-SHA256-bound actual checker artifacts uploaded by CI and evaluated byte-for-byte by a Rocq-proved decoder; producer refinement still open.
- [FSEM-01 bounded source-observation simulation](formal-semantics-source-simulation-fsem01-v1.md) — conditional Rocq replay with exact producer-binding and finite catalog premises, plus CI witnesses over real source-derived artifacts; no universal Haskell refinement.
- [FSEM-01 bounded observation producer-fidelity proof](formal-semantics-producer-fidelity-fsem01-v1.md) — by-construction preservation of all source-run artifact fields and injective snapshot encoding, with checker-state extraction still a tested trust boundary.
- [FSEM-01 checker-state resource observation bridge](formal-semantics-checker-state-observation-fsem01-v1.md) — exact observed one-owner Haskell Map/Set flags, Rocq resource-context lookup lemmas and start/end/return correspondence; cross-language state refinement remains open.
- [FSEM-01 full bounded resource-context wire](formal-semantics-resource-context-wire-fsem01-v1.md) — exact four-map/set checkpoint extraction, real Haskell start/end/consume transition replay, Rocq-decoded full-state evidence; universal cross-language refinement still open.
- [FSEM-01 two-owner Core frame and context2 wire](formal-semantics-two-owner-context-fsem01-v1.md) — separate source-resolved owner identities, real two-owner Haskell Core operations, independent versioned wire and Rocq frame lemmas; full two-owner source elaboration remains open.
- [FSEM-01 direct two-linear-owner source conformance](formal-semantics-two-owner-source-fsem01-v1.md) — real two-parameter function with exact production map/loan observations; opaque tuple return and general elaboration still open.
- [FSEM-01 exact two-Bytes TyProduct return](formal-semantics-product-return-fsem01-v1.md) — bounded source element type/mode elaboration and runtime return matching, with the general tuple algebra still open.
- [FSEM-01 mixed flat products and finite contract preservation](formal-semantics-flat-product-fsem01-v1.md) — flat arity ≥2 and primitive mixed modes with conditional Rocq exact-contract lemmas; affine source typing/general refinement remain open.
- [FSEM-01 finite resource contexts and early SURF-008 preflight](formal-semantics-finite-context-fsem01-v1.md) — arbitrary numbers of modeled owners, four-zone frames and exact Haskell Map/Set checks; implementation-to-Rocq refinement remains open.
- [FSEM-01 source-declared affine nominal ownership](formal-semantics-source-affine-fsem01-v1.md) — exact admitted nominal mode provenance, executable borrow/consume/drop and rejection witnesses, and conditional Rocq frame lemmas; full source semantics still open.
- [FSEM-01 mixed affine/linear source ownership](formal-semantics-mixed-affine-linear-fsem01-v1.md) — one parsed function with simultaneous externally admitted affine Permit and intrinsic Linear Bytes, exact production completion/escape errors, and conditional Rocq mixed-mode frame/debt lemmas.
- [FSEM-01 source-checked nominal affine product return](formal-semantics-nominal-affine-product-fsem01-v1.md) — exact source-declared `(Permit, Bytes[8])` ordered product, admitted nominal provenance, real checker ownership moves and rejected variants, with conditional Rocq contract/frame lemmas.
- [FSEM-01 source product elimination with restored affine/linear owners](formal-semantics-source-product-elimination-fsem01-v1.md) — checked nominal product parameter, real Core product consumption and exact typed successor bindings through the production Surface checker, precise failures and conditional Rocq restoration proofs.

These review documents do not replace accepted semantic contracts, the normative grammar, the Logic Ledger, or exact-commit proof and conformance results.

## Reading historical slices

A historical slice document should therefore be read as:

1. the semantic boundary implemented or exercised by that slice;
2. the cases and artifacts that accompanied it; and
3. a timestamped record of what was deliberately outside that slice at the time.

Do not infer from an old “not yet” list that the named later slice is still open. Do not infer from a historical implementation note that its implementation is the language specification. Phil’s accepted ADRs/contracts, current logic ledger, conformance matrix, and checked repository evidence retain those roles.

Bounded FSEM-02 [source offer-catalog totality](formal-semantics-source-offer-fsem02-v1.md) is non-normative: exact parsed-arm coverage and conditional Rocq catalog facts, not complete offer execution or rendezvous.

Bounded FSEM-02 [source offer-arm branch replay](formal-semantics-source-offer-replay-fsem02-v1.md) connects a source-checked return-unit arm catalog, an externally selected label and exact checked protocol projection to a production Core local offer step. It does not execute general arm bodies, close the successor implicitly, or establish rendezvous.

The bounded [FSEM-02 source-checked restricted payload rendezvous](formal-semantics-restricted-source-transfer-fsem02-v1.md) composes independently parsed typed send/receive source with the existing production Core atomic payload owner transition, exact accepted/rejected source replay, and conditional Rocq owner/endpoint frame lemmas. Non-normative: external nominal/activation authority remains a premise; full architecture admission, source-close execution, and universal Haskell-to-Rocq refinement remain open.

The bounded [FSEM-02 source-checked terminal endpoint closure](formal-semantics-source-terminal-close-fsem02-v1.md) executes the actual parsed post-send/receive close statements through the production Core stateful endpoint closer, retires exactly both endpoint-owner occurrences, and checks rejected stale/head/role/outcome cases; the receiver's restricted payload and root/process closure obligations remain live. Conditional Rocq owner-map/resource results are **non-normative**, not a universal implementation refinement.

The bounded [FSEM-02 checked-source terminal obligation gate](formal-semantics-source-terminal-obligations-fsem02-v1.md) composes the already checked send/receive and two source close commands with explicit native process-local disposal and root terminal checks. It rejects unaccounted activation owners, open linear payload/assurance/root residues, and unsupported terminal control. The finite Haskell replay and conditional Rocq residual-index theorem are non-normative, not proof of source-authorized disposal or complete root admission.

- [FSEM-02 source terminal-close replay and exact-state correspondence](formal-semantics-terminal-close-replay-fsem02-v1.md) — independently re-executes both native endpoint closes from checked rendezvous state, requires full exact post-close state equality, tests forged snapshots and stale owners, and proves conditional Rocq owner-projection rejection/frame lemmas; not source disposal authority or Haskell/Rocq refinement.
