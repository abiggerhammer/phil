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
- `receiveFrame` accepts only exact `Frame[G]` messages. An outer refinement such as `{x : Frame[G] | P}` remains fail-closed until the value/refinement checker can establish `P` rather than silently discarding it.
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

## Implemented in the bidirectional-value slice

- Core values represent variables, unit, booleans, width-indexed unsigned literals, and explicit type ascription.
- `synthValue` implements the checker-side `⇒` judgment over full `CheckState`, preserving residual obligations while updating affine/linear resource residue.
- Variable synthesis automatically respects structural mode: `Γ` remains reusable, `A` is consumed at most once, and `Δ` is consumed exactly once when the value occurrence transfers ownership.
- A shared-borrowed affine/linear owner cannot be consumed by value synthesis.
- Internal `PendingRecv` resources are explicitly not ordinary values and cannot be discharged by evaluating their variable; only recognition commit/fatal operations may consume them.
- `checkValue` implements the checker-side `⇐` judgment by synthesis plus an explicit equality-boundary classification.
- Exact structure and guarded recursive session unfolding are definitional equality in the represented Phase 0 subset; choice label order is irrelevant.
- Different indices of the same dependent `Bytes[...]` family are classified as requiring explicit propositional equality/transport, never silently coerced.
- Unrelated base families remain incompatible; a refined value may canonically forget refinements only when its underlying base type is definitionally equal to the expected type.
- Fixed-width unsigned literals are checked against mathematical range (`0 <= n < 2^w`) and therefore do not introduce modular wraparound semantics.

The equality API exposes three outcomes: definitionally equal, requires explicit propositional equality, or incompatible. The following slice supplies the evidence/transport machinery for the middle case.

## Implemented in the refinement/evidence/transport slice

- Proof-relevant dependent indices are structured `RefTerm` values rather than strings. The represented Phase 0 term forms include variables, Nat/UInt/Bool literals, field projection, `len`, explicit `toNat`, addition, guarded natural subtraction, literal scaling, and opaque term leaves.
- Propositions are structured over those terms: equality/inequality/order, membership/disjointness, conjunction/disjunction/negation, and named claim atoms.
- The executable refinement sort language distinguishes `Bool`, `Nat`, `UInt[w]`, `Enum[E]`, `FiniteSeq[T]`, `FiniteSet[T]`, `StableId[K]`, and explicitly opaque elaborated sorts.
- Proof-relevant field projections and opaque semantic leaves carry the sort established by elaboration. `TyOpaqueSorted` lets an otherwise opaque runtime type expose a declared refinement sort for variables such as finite collections, enum values, or stable identities without encoding that fact into a string.
- Value synthesis/checking and explicit transport validate proof-relevant type indices before type comparison. In particular, `Bytes[index]` requires `index : Nat`, invalid `UInt` widths are rejected, and invalid declared sorted-opaque sorts cannot cross the value-checking boundary merely because their runtime types otherwise match.
- Equality and inequality require identical sorts; ordered comparisons accept `Nat` or equal-width `UInt`; membership requires a finite collection with the matching element sort; disjointness requires matching finite-collection sorts. Stable identities therefore compare only within the same identity kind.
- Named claim arguments must each be individually well-sorted. Claim declaration lookup, arity checking, and signature matching remain assigned to executable `Σ` handling in focusing/elaboration rather than being guessed by this slice.
- Canonical normalization evaluates literal UInt-to-Nat coercions and simple arithmetic/propositional structure without introducing modular arithmetic or truncated natural subtraction.
- Every proof-relevant `Nat` subtraction is inspected before proposition normalization and generates the side requirement `rhs <= lhs`; a surrounding equality or other simplification cannot erase that requirement.
- Subtraction side requirements use the same explicit disposition machinery as other refinement obligations: they may discharge definitionally, use matching evidence, or—only through `checkValueWithResidual`—become deterministic child obligations such as `<parent>.nat-sub.1` with inherited origin/scope/required-point metadata.
- A subtraction precondition already known false is fatal and cannot be residualized. Carried evidence for a refined value's main proposition likewise does not bypass embedded subtraction side conditions.
- `Bytes[...]` indices now use structured terms. Definitionally equal normalized indices compare equal; distinct indices in the same family still require explicit equality evidence.
- Structured term substitution instantiates refinement binders with the checked semantic value. A value whose refinement proposition mentions its binder must expose a refinement-visible term.
- Refined value checking first checks the base type, then discharges the instantiated proposition by definitional normalization or exact matching reusable evidence in `Γ`.
- Refined values canonically eliminate to their definitionally equal base type without losing or duplicating resource ownership.
- An unrestricted refined binding itself entails its instantiated refinement proposition, so later checks may use the fact already carried by that binding; the proposition remains subject-specific.
- Generic `Proof[P]` evidence and `TyValidated claim context subject` evidence are reusable only from `Γ`; validation evidence entails exactly the claim/context/subject proposition it names.
- Stale policy contexts and wrong subjects therefore do not match merely because the claim name is the same.
- Named claim atoms, including opaque claims such as `DigestMatches`, are never self-proved by this layer. They require matching evidence or an explicit residual disposition.
- `checkValueUsing` validates an explicitly supplied evidence binding against the exact required proposition.
- `checkValueWithResidual` is the only path in this layer that may residualize an otherwise-undischarged refinement. It requires an explicit stable obligation ID plus origin, scope, and required point.
- A proposition already known definitionally false cannot be residualized as a runtime/export obligation merely to evade static rejection.
- `Obligation` now records scope as required by the accepted ADR-006 checker-to-ledger handoff shape. Reusing a stable obligation ID for different metadata/proposition remains an error.
- `VTransport` / `transportValue` implement explicit propositional transport for the current dependent `Bytes[index]` family. The required proof is `Proof[sourceIndex == targetIndex]`; no implicit symmetry or coercion is invented.
- Transport preserves structural ownership: a linear source occurrence is consumed once, one target-typed result emerges, and unrestricted equality evidence remains reusable.
- Transport to a refined target is fail-closed; refinement proof discharge remains a separate explicit step.
- Because proof-relevant indices are now structured, definitional equality uses a paired binder environment to compare refinement/session binders alpha-equivalently while respecting nested shadowing and avoiding variable capture.

## Implemented in the deterministic-focusing slice

- `StaticContext` now represents the claim-relevant executable portion of `Σ`: named claims have ordered parameter names/sorts and are declared either transparent with a proposition body or opaque with no solver-visible body.
- Claim declaration rejects duplicate claim names, duplicate parameter binders, and invalid parameter sorts.
- `validateStaticContext` checks transparent definitions before use. Definitions must be sort-correct under exactly their declared parameters, may refer only to declared claims, and may not contain direct or mutual transparent recursion.
- Claim applications are checked against `Σ` for existence, arity, and parameter sort. The checker does not infer claim signatures from printed atom text.
- Transparent claim expansion is deterministic and transitive. Expansion produces explicit focusing trace entries and is followed by refinement sort checking and canonical normalization.
- Opaque claims never expand. After matching in-scope evidence is considered, an unresolved opaque proposition stops at `FocusNeedsExplicitMechanism`; it is never routed to the transparent decision-procedure boundary.
- Canonical elaboration inserts the total `UInt[w] -> Nat` coercion explicitly in known `Nat` contexts, including Nat arithmetic, mixed UInt/Nat ordering, and claim parameters declared as `Nat`. The reverse `Nat -> UInt[w]` direction remains non-implicit.
- `elaborateRefTermAs ... SortNat` is the deterministic Core-facing mechanism the later source/type elaborator uses for proof-relevant Nat indices such as `Bytes[begin.length]`.
- Proposition focusing preserves the pre-normalization natural-subtraction prerequisites implemented in the prior slice. A main proposition may normalize to `true` only after its generated subtraction requirements have been retained in the focus plan.
- Matching unrestricted evidence is resolved modulo deterministic transparent expansion and proposition normalization, so evidence for a named transparent claim can match its canonical expanded goal.
- A focused requirement has exactly one current pre-solver disposition: definitionally discharged, discharged by matching in-scope evidence, requires the configured transparent decision procedure, or requires an explicit non-solver mechanism because opaque structure remains.
- A proposition already normalized to `false` with no matching evidence is rejected before solver dispatch.
- Structural-mode lookup, guarded session-head exposure, and exact branch-exhaustiveness checking are executable deterministic focusing operations. Branch handlers must cover exactly the unique labels declared by the session choice.
- Focusing does not choose protocol labels, validators, assumptions, or escalation boundaries. Those remain explicit program/architecture decisions as required by the normative focusing rule.

## Implemented in the checked-decision/disposition slice

- `Phil.Core.Decision` separates certificate production from certificate checking. The built-in arithmetic engine proposes `DecisionCertificate` values; `checkDecisionCertificate` independently reconstructs the requested proposition from the certificate and its supplied checked facts before the result may count as static evidence.
- The certificate language covers the represented Phase 0 linear-arithmetic core over `Nat` and the mathematical values of `UInt[w]`: exact linear equalities, non-strict and strict order, conjunction/disjunction, and disequality established by a strict order in either direction.
- Linear certificates may cite exact supplied evidence, the semantic lower bound of a total `Nat`, and the lower/upper mathematical bounds of a `UInt[w]` or its explicit `toNat` image.
- Inequality premises may only be combined with nonnegative rational weights. Equality premises may be used with either sign. Equality goals cannot cite inequality bases, inequality slack must be nonnegative, and equality slack must be zero.
- The certificate checker validates UInt widths rather than trusting a bound label. A forged `UInt[8]` upper-bound certificate attached to a `Nat` term is rejected.
- Finite-collection and other non-arithmetic atoms remain uninterpreted to the arithmetic producer. An exact atom may be consumed when it is already supplied as checked evidence; the producer never invents collection membership/disjointness facts.
- Natural-subtraction definedness is checked on the pre-normalized proposition before the solver form is constructed, so an identity such as `(a-b) == (a-b)` cannot erase its required `b <= a` premise.
- Certificate-invented `Nat >= 0` bases are subject to the same definedness rule. A forged proof cannot circularly establish `b <= a` by citing the nonnegativity of the partial term `a-b` before `b <= a` is known.
- The current built-in producer is intentionally sound but incomplete. It deterministically handles normalization identities, Nat/UInt domain bounds, short linear-inequality chains, simple equality combinations, propositional conjunction/disjunction, and inequality-derived disequality. Unsupported transparent goals return `unknown`; `unknown` is never interpreted as proof or truth.
- `Phil.Core.Discharge` applies the ADR-006 required-point order to a named `Obligation` while preserving its stable ID, canonical proposition, origin, scope, and required point.
- A resolved obligation records one explicit disposition: static discharge by definition, matching in-scope evidence, or independently checked certificate; an exact architecture-declared runtime binding; or an exact architecture-declared export boundary.
- Explicitly supplied evidence is checked against the canonical required proposition and must be unrestricted evidence in `Γ`.
- Runtime bindings must match the exact obligation ID, canonical proposition, and required point. Their declared success evidence must itself entail the exact canonical proposition; a mismatched validator result type cannot close the obligation.
- Export bindings likewise match exact obligation identity, canonical proposition, and required point. Export is local closure of responsibility, not a proof of the proposition.
- Natural-subtraction prerequisites become deterministic child obligations such as `<parent>.nat-sub.1`, inheriting the parent's origin/scope/required point. A statically or runtime-established child may become a checked fact on the success continuation.
- An exported prerequisite is never reused as a local solver assumption. If a parent still depends on an exported prerequisite, the parent must itself cross an explicit export boundary rather than pretending that the prerequisite became true locally.
- Runtime disposition precedes export when both are explicitly configured, following ADR-006's canonical order. With no successful static, explicit-evidence, runtime, or export disposition, the obligation is rejected as unresolved.
- `Assumed` is deliberately absent from ordinary required-point resolution. ADR-010 assumptions remain explicit architecture/manifest trust boundaries rather than a fallback that source checking can synthesize after failed proof search.

This slice does not yet implement the complete ADR-010 append-only assurance graph, immutable revision/artifact digests, acceptance-rule/acyclicity verification, a validator declaration registry with artifact identity, external proof-adapter verification, or certified manifest closure. Runtime/export records here are checker-to-ledger dispositions whose later ledger entries still require those assurance checks.

## Implemented in the surface parser/elaboration slice

- `Phil.Surface.Syntax` represents Phase 0 source components, parameters, blocks, statements, branch arms, expressions, propositions, and types with explicit source spans carrying file, line, column, and absolute offset information.
- `Phil.Surface.Parser` is a full-consumption Megaparsec parser. Non-comment trailing input and unterminated blocks are syntax errors rather than silently ignored input.
- The parser accepts the surface constructs exercised by the accepted upload client/server and all twenty semantically rejected Phase 0 witnesses, including tuple bindings, typed parameters, `provides`, projections/calls/arithmetic, construction, session actions, `using`, split recognition/commit, validation, `or fail`/`or reject`, scoped `borrow`, `decide`, `offer`, fatal failure, close/release/return, `accept ... as`, and `prove`.
- All twenty rejected witnesses are now repository fixtures under `examples/rejected/`. Parser conformance deliberately requires them to parse: resource/session/evidence mistakes belong to later competent semantic layers, not to syntax rejection.
- Surface propositions and types include the Phase 0 `Bytes[...]`, `Frame[...]`, `Proof[...]`, `Validated[...]`, fixed-width unsigned, and generic named/indexed forms required by the witness language.
- `Phil.Surface.Elaborate` canonically lowers the already-executable refinement/type/value subset into existing Core representations. It does not invent whole-process Core semantics for primitives whose contracts are not yet represented in executable `Σ`.
- Proof-relevant field projections require an elaboration-provided sort; the front end never guesses a field sort from spelling.
- Dependent `Bytes[...]` indices use the existing focusing elaborator and therefore insert the canonical total `UInt[w] -> Nat` coercion when required.
- Ambiguous integer values require an expected fixed-width unsigned type rather than receiving a guessed width.
- Symbolic multiplication remains outside the Phase 0 refinement fragment; only literal scaling elaborates.
- Generic opaque indexed types are serialized only when every index expression has a canonical supported rendering. Unsupported index syntax fails closed instead of collapsing multiple source expressions to one placeholder type identity.
- Fixed-width surface type widths are range-checked before conversion to the host `Int`, preventing absurd source numerals from wrapping through the implementation representation.
- `phil-core parse FILE` exposes the trusted parser directly and reports source-positioned syntax errors. A successful parse explicitly reports that it is parse-only and does not claim semantic acceptance.

## Implemented in the Phase 0 surface-conformance slice

- `Phil.Surface.Check` now checks whole Phase 0 components rather than stopping at fragment elaboration. It is a small facade over a narrow source preflight pass and a Core-backed process engine.
- `SurfaceEnvironment` makes the architecture boundary explicit: immutable Core claim declarations, initial resource bindings, primitive contracts, surface type aliases, selection prerequisites, dependent receive prerequisites, provider expectations, and the legacy split-ingress fixture mode are supplied as data rather than inferred from names.
- Surface aliases such as `Client[Upload]` and `Server[Upload]` resolve to the exact projected endpoint types supplied by the Phase 0 architecture environment. Typed component parameters are checked against those resolved architecture bindings rather than accepted by spelling alone.
- Source endpoint names use SSA-like elaboration internally: each session action receives a fresh Core successor owner, while branch-local surface code can deterministically rebind the programmer-visible endpoint name to that successor.
- `decide` evaluates its scrutinee exactly once and carries the resulting resource state into each arm. Calls, validation, recognition, and storage decisions therefore cannot be treated as inert read-only terms.
- External offers require exact declared label coverage before arm checking. Continuing branches rejoin through the existing Core `joinContinuing` resource rule, while terminal paths do not manufacture a fake continuation.
- Grammar-backed receive, raw borrowing, recognition evidence, `commit_receive`, and recognition failure reuse the existing `PendingRecv`/provenance Core boundary rather than a separate surface-only ownership model.
- Dependent byte counts, explicit `using` evidence, refined branch payloads, opaque claims, checked arithmetic proof attempts, and explicit transport requirements reuse the existing elaboration/value/focusing/decision APIs.
- Semantic projection aliases are rewritten with explicit cycle/fixed-point detection. A canonical self projection such as `begin.length` terminates rather than recursively rewriting forever.
- A narrow preflight layer rejects source text that explicitly continues after an unconditional terminal statement and reports lexically absent arguments to evidence-consuming primitives as `MissingEvidence`. It does not replace Core resource/session checking for ordinary uses.
- The Phase 0 conformance harness supplies the frozen projected upload sessions and primitive contracts independently of its expected-result table. The checker derives acceptance/rejection first; the harness compares the resulting stable rejection class afterward.
- Both accepted upload role programs check end to end against their projected local sessions. The client explicitly releases its linear payload on `unsupported`, server `reject`, and client `cancel`; the payload path transfers ownership through `send_exact`. No terminal ownership allowance is used to make the positive witness pass.
- All twenty repository negative witnesses are required to fail in their declared earliest semantic rejection class, covering structural reuse/drop, protocol order, branch exhaustiveness, raw/semantic separation, missing/stale evidence, explicit transport, incompatible branch residues, terminal continuation, recognition provenance, borrow escape, opaque proof, and unchecked machine arithmetic.
- The conformance suite gives every source fixture an execution timeout. Checker nontermination is therefore an explicit conformance failure naming the responsible `.phil` witness rather than a whole-workflow hang.

This slice establishes end-to-end semantic checking for the frozen Phase 0 upload witness language and negative corpus. It does not claim that every future Phil surface construct or architecture declaration is already generalized.

## Implemented in the assurance-ledger / manifest-verification slice

- `Phil.Assurance.Handoff` is the explicit checker-to-ledger seam for `ResolvedObligation`. It preserves the canonical proposition and exact `StaticallyDischarged` / `RuntimeBound` / `Exported` disposition, and deterministically records prerequisite revisions with `generated_from` lineage to their parent revision.
- Handoff does not invent artifact, validator, assumption, export-destination, or acceptance metadata that Core does not know. Architecture supplies revision kind, representation, subject/context identities, and the acceptance rule explicitly.
- `ObligationRevision` carries the stable logical obligation ID, a deterministic revision identity, canonical statement/digest, origin/scope/required point, representation, subject/context identities, acceptance rule, and immutable lineage.
- Core propositions have an explicit canonical renderer for revision identity rather than relying on Haskell `Show` output. Changed canonical proposition, subject/context identity, semantic scope, representation, or acceptance rule yields a new revision identity; semantically irrelevant presentation text is outside this identity path.
- Ledger evidence, assumptions, exports, and assurance-use records use stable explicit IDs plus independently checked content digests. This permits real dependency cycles to be represented and rejected rather than making cycles impossible through recursive content-addressing.
- Manifest identity binds selected revision IDs **and immutable revision content**, plus evidence/assumption/export/use IDs and their verified content digests, build identities, certification scope, validity context, and ADR-011 lowering-ledger root.
- `verifyLedgerExtension` enforces append-only semantic history: existing revisions, evidence, assumptions, exports, and assurance uses may remain unchanged while new nodes are appended; an old node cannot be silently rewritten in place.
- The verifier checks map-key/record identity consistency, statement/content digests, referential integrity, artifact availability/digests where required, and nonempty stable node identities.
- Acceptance rules are compositional `entry` / `all` / `any` structures evaluated against usable evidence dependency closure. Empty `all` or `any` forms are invalid rather than vacuously certifying an obligation.
- The justification graph is required to be acyclic across evidence dependencies, obligation dependencies, and revision-lineage edges. Protocol/session recursion remains a separate graph and does not count as assurance justification recursion.
- Evidence selected by a manifest must be accepted, within its declared validity scope, and backed by all selected dependencies/assumptions. Selected rejected evidence cannot certify anything.
- Assumption nodes are first-class, content-digested records. A manifest may use one only when the trusted verification context explicitly permits that exact assumption identity.
- Out-of-scope obligations require exactly one explicit export entry to a permitted architecture boundary. Export is bounded local closure; an exported obligation cannot be reused as a truth-producing dependency for an in-scope claim.
- Runtime-enforced entries must name a concrete mechanism, execution point, success-evidence type, failure/resource contract, runtime residue, and ADR-011 cost reference. Retained-runtime assurance uses must cite `RuntimeEnforced` evidence for the same obligation and the same known cost reference.
- Erasure uses require explicit evidence entries for the same accepted obligation; disappearance of a proof/check object by itself never counts as justification for erasure.
- Artifact-backed assurance kinds such as proof-assistant theorems, translation validation, differential/property testing, and checked certificates require an exact artifact identity/digest available to the verification context. The verifier checks the reference; it does not rerun arbitrary external tools.
- The Phase 0 upload witness is executable as an assurance manifest with eleven normative obligations, four shared runtime assumptions, combined kernel/runtime acceptance where ADR-010 requires both, and ADR-011 retained-runtime links.
- The assurance suites adversarially cover tampered revision/evidence/use digests, missing evidence, stale scope, unpermitted assumptions/exports, unknown cost references, rejected evidence, vacuous acceptance, actual cyclic dependencies, artifact requirements/digest mismatches, bounded export closure, exported-dependency misuse, missing expected obligations, manifest tampering, append-only history, runtime-use kind checking, and lossless Core disposition/lineage handoff.

This slice verifies the in-memory certification graph and checker handoff. Serialization, UI/report generation, persistent ledger storage, concrete native-build artifact production, and external proof/test/translation-validator execution remain outside the verifier boundary. The semantic/reference upload manifest deliberately does not invent implementation-specific native evidence that does not yet exist.

## Next checker slices

1. Generalize the declaration/architecture environment beyond the frozen Phase 0 witness where later examples require it.
2. Introduce the next lowering/representation slice and connect its concrete ADR-011 decisions to verified assurance uses.
3. Add a stable manifest serialization only when an interchange/build artifact is needed; serialization remains separate from graph-verification semantics.

## Explicit current non-goals

The checker still does not claim general end-to-end source-level Phil conformance beyond the frozen Phase 0 witness language. In particular it does not yet project dependent session types from a parsed global protocol, provide a general source declaration system for primitive contracts/type aliases/validator artifacts, execute grammar recognizers, provide a complete decision procedure for every transparent proposition, produce or independently validate native runtime-validator implementations, synthesize assumptions, cross obligation boundaries without explicit architecture, persist/parse a frozen assurance-manifest interchange format, execute external proof assistants/tests/translation validators as part of manifest verification, or lower to systems/LLVM IR. Return/provider checking is currently limited to the represented component/provider forms used by the witness. Transport-acquisition failure for `receiveFrame` remains represented by the accepted primitive contract rather than simulated inside the structural checker.
