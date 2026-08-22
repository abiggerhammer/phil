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

Whole-component process elaboration/checking is deliberately not part of this slice. A syntactically valid component may still fail at resource, session, recognition, evidence, obligation, or provider-interface checking.

## Next checker slices

1. Conformance harness over the accepted/rejected `.phil` corpus, including whole-component surface-to-Core checking.
2. Assurance-ledger handoff and manifest verification.

## Explicit current non-goals

The checker still does not claim end-to-end source-level Phil conformance. In particular it does not yet project dependent session types from a global protocol, elaborate/check every parsed process construct into executable Core, substitute communicated semantic values into all dependent continuations, execute grammar recognizers, provide a complete decision procedure for every transparent proposition, validate runtime-validator artifact identities, synthesize assumptions, cross obligation boundaries without explicit architecture, validate return values against a provider signature, validate the upload protocol end-to-end, verify a closed ADR-010 build manifest, or lower to systems/LLVM IR. Transport-acquisition failure for `receiveFrame` is still represented by the accepted primitive contract rather than simulated inside the structural checker.