# A Tour of Phil — Phase 1

## From one architecture to a language for architectures

*Work-in-progress Phase 1 edition. This tutorial explains the semantic model Phase 1 is building toward. Unlike the frozen [Phase 0 Tour](tour-phase0.md), it intentionally does not yet present executable `.phil` listings. Phase 1 Surface Grammar v1 is normative, but the canonical parser/elaborator/front-end path is still being completed. Source examples will be added only after they can be checked through that path and kept under CI.*

Phil is a systems language for building software from the outside in. Instead of starting with “what instructions should the computer run?”, Phil starts with questions like:

- What parts does this system have?
- What may those parts say to each other?
- What resources does each part own?
- What is each part allowed to do?
- What may a computation make observable?
- What must its surroundings provide?
- What must be true before the program can take the next step?
- What happens when something goes wrong?
- What facts must survive when the implementation changes?

Phase 0 answered those questions for one nontrivial program: the framed upload architecture.

Phase 1 asks a harder question:

> Can those rules describe **architectures in general**, without the compiler secretly knowing which program it is looking at?

The short version is:

> **Phase 0: one architecture works.**  
> **Phase 1: the language works for architectures.**

You do not need to know formal logic, category theory, compiler construction, or security jargon to follow this tour. We will introduce technical names only after there is a concrete distinction that needs one.

## 1. Phase 1 removes the special cases

The Phase 0 upload program proved that Phil's basic idea can work end to end.

The source describes a protocol. Session endpoints move through that protocol linearly. Received bytes do not advance the conversation until recognition succeeds. Policies produce evidence. Owned resources cannot silently disappear. Failure paths have explicit resource behavior. Lowering preserves facts instead of treating them as comments. The resulting native program can be checked and certified against the exact source architecture.

That is already useful, but there is a trap hiding in any first implementation.

If a compiler understands only one program, it is easy for some of the program's architecture to live accidentally inside the compiler itself.

For example, imagine a compiler rule that effectively says:

```text
if this is the upload program,
    create these two components,
    give this provider to the server,
    connect these protocol roles,
    and lower them this way
```

Even if the resulting program behaves correctly, the architecture is no longer completely expressed by the language. Some of it exists as privileged compiler knowledge.

Phase 1 removes that privilege.

The upload program must become just one ordinary Phil program. A very different program must travel through the same machinery without adding another branch saying “if this is the other special program...”.

That second pressure case is **Steve**, a small content-addressed store.

Steve is deliberately boring. It stores bytes under an identity derived from their content, retrieves them again, and has to preserve properties such as digest identity, install-if-absent behavior, provider authority, and explicit failure semantics.

The upload program and Steve need different architecture. That is the point.

If the language can describe both through the same parser, type checker, contract machinery, Systems lowering, and assurance model, then the compiler is starting to understand a language rather than a pair of examples.

> **Source example to add after the canonical front end lands:** the smallest ordinary declarations that distinguish the upload architecture from Steve without any compiler-recognized program identity. The example should be checked through the canonical parser/elaborator and should have a negative companion showing that an undeclared provider/protocol/root cannot be installed by compiler magic.

## 2. The program declares its architecture

In Phase 0, it was enough to demonstrate one architecture precisely.

Phase 1 needs ordinary source declarations that say what the architecture **is**.

A useful way to think about an architecture is as a graph whose nodes and edges have meaning.

The nodes may include things such as:

- components;
- first-class callables;
- providers;
- protocol instances;
- capabilities;
- owned resources;
- runtime enforcement mechanisms.

The edges may include things such as:

- “this component uses this provider”;
- “this endpoint is the server role of this protocol instance”;
- “this capability gives this callable authority over this subject”;
- “this obligation concerns this exact semantic object”;
- “this implementation realizes this public provider contract.”

Those relationships are not merely wiring hints for a backend. They are part of what the program means.

That means Phil needs **semantic identity**.

Suppose two storage objects happen to occupy the same machine address at different times. They are not therefore the same semantic object.

Suppose two provider operations lower to the same C symbol. They are not therefore the same architectural operation.

Suppose two equal byte strings are stored in different ownership positions. Equality of their contents does not by itself make their owners interchangeable.

Phil therefore treats names, source locations, pointers, handles, backend symbols, and allocation addresses as possible representations of an identity — not as the identity itself.

The architecture must have stable checked identities and revisions that survive harmless implementation changes.

This principle will recur throughout the tour:

> **Representation coincidence is not semantic identity.**

> **Source example to add after the canonical front end lands:** two architecture occurrences with equal-looking types or representations but distinct semantic identities. One positive case should preserve the distinction; one negative case should try to substitute one occurrence for the other and fail at the competent identity/subject layer.

## 3. Abstraction means saying what you actually need

A general language needs reusable code.

That usually means some form of **generic abstraction**: write something once and use it with several concrete types, values, providers, or functions.

But Phil cannot safely define genericity as “replace a name with whatever the caller supplies and hope type checking works out.”

The reason is ownership.

Imagine a generic function that receives a value `x` and simply returns it.

It does not need to copy `x`.

It does not need to discard `x`.

So this operation should work even if `x` is linear — that is, even if it must be transferred exactly once.

Now imagine another generic function that receives `x` and uses it twice.

That function **does** require permission to duplicate the value.

Or imagine one that ignores `x` entirely.

That function requires permission to discard it.

Phil therefore does not give an unknown type secret privileges just because it is abstract.

An abstract value is not automatically copyable, droppable, serializable, movable between devices, comparable, hashable, or safe to hand to foreign code.

A generic body exposes the requirements it actually uses.

Conceptually:

```text
generic body
+ declared assumptions
→ checked parameter requirements
→ reusable result contract
```

If a body only transfers a value from input to output, it should induce no copy/drop requirement.

If it duplicates the value, it induces a duplication requirement.

If it discards the value, it induces a discard requirement.

The important idea is not the syntax. It is that requirements become part of the checked interface instead of remaining folklore about what happened to work in one compiler.

At instantiation time, the caller must satisfy those exact requirements.

This is one of the ways Phil tries to make abstraction honest:

> **Generic code may rely only on the facts and permissions its contract actually provides.**

> **Source example to add after the canonical front end lands:** a structure-polymorphic identity function that accepts a linear actual and returns the same unique owner; a generic discard that is rejected without weakening permission; and a generic duplicate that is rejected without contraction permission. These should become canonical positive/negative tutorial fixtures tied to the corresponding generic conformance cases.

## 4. Ownership does not disappear inside abstraction

Phase 0 already used three structural modes:

- **unrestricted** values may be duplicated and discarded;
- **affine** values may be discarded but not duplicated;
- **linear** values may be neither duplicated nor discarded.

Phase 1 keeps those rules when values become generic, get placed inside records, cross branches, enter loops, or are captured by closures.

This matters because abstraction can otherwise become a laundering mechanism.

Suppose a linear capability is placed inside a generic box. If the box suddenly becomes freely copyable, the program has duplicated the capability indirectly.

Suppose a linear resource is captured by a closure. If the closure is then treated as an unrestricted function value, the resource has again been duplicated through representation.

Phil instead derives the structural behavior of compound things from what they own.

A closure owning a linear capture is linear.

A record owning a linear field cannot become unrestricted merely because the record has a convenient name.

A loop carrying a linear owner must account for that owner at the backedge.

A branch join cannot invent a hidden “maybe the resource is here” representation merely to make two incompatible branches fit.

The broad rule is:

> **Abstraction may hide representation. It may not hide ownership.**

> **Source example to add after the canonical front end lands:** a closure capturing one linear value, plus a negative case attempting to duplicate the closure; and a branch or loop example showing that the same exact linear owner must be accounted for at reconvergence/backedge.

## 5. Functions are values with contracts

In Phase 1, functions and closures are ordinary first-class values.

That means they can be passed to other functions, returned, stored, placed in data structures, or supplied as generic arguments.

But a callable is not described only by a machine-level shape like “takes two pointers and returns an integer.”

A **callable contract** can describe several independent dimensions, including:

- parameter and result types;
- resource transitions;
- captured-resource mode;
- authority the caller must supply;
- possible effects;
- modeled failure outcomes;
- postconditions and evidence;
- residual obligations;
- cost information where relevant.

This lets Phil state a useful refinement rule.

Suppose a caller is prepared for a function that may read and write a store.

An implementation that only reads is narrower. That is safe.

An implementation that may also send data over the network is wider. That is not silently substitutable.

Likewise, an implementation that requires **less** caller authority can be a valid refinement, while one that requires new authority cannot be slipped in merely because its machine signature matches.

So higher-order substitution is about semantic boundaries, not just ABI compatibility.

> **Source example to add after the canonical front end lands:** one higher-order function receiving a callable under a public contract, one narrower accepted implementation, and one same-machine-shape implementation rejected because it widens either authority, effects, or failures.

## 6. Effects say what a computation may do

Now we need a distinction that ordinary function types do not capture well.

Imagine a callable that may write a blob store.

That is not the same statement as “this callable takes a blob and returns unit.”

Phil calls the former kind of information an **effect**.

An effect answers a deliberately narrow question:

> **What kind of semantically observable action may this computation perform?**

Effects in Phil are **may-effect upper bounds**.

If a callable is permitted to perform:

```text
Read(store)
Write(store)
```

then an implementation that only reads is still within the contract.

An implementation that additionally sends network traffic is not.

Effects can also name exact semantic subjects.

These are different effects:

```text
Write(blob_store)
Write(log)
Send(endpoint)
Read(clock)
```

That subject matters. `Write(storeA)` does not become `Write(storeB)` merely because both stores currently use the same runtime function or happen to share a representation.

Effects also compose conservatively.

If one reachable path may read and another may write, the surrounding computation may do either. A public effect bound therefore includes the possibilities of every reachable branch.

The result is a simple refinement direction:

> **An implementation may be narrower than its public effect bound. It may not silently be wider.**

> **Source example to add after the canonical front end lands:** a callable with subject-indexed effects, two distinct storage subjects, a valid narrower effect instantiation, and a rejected widening. Include the `Effects`-parameter example only once its parser/elaborator semantics are live, even though Grammar v1 already fixes the concrete spelling.

## 7. Carrying an effect is not performing it

Effects become especially useful for higher-order code.

Suppose a function value has a contract saying that invoking it may write storage.

Merely **possessing** that function does not write anything.

Passing it to another function does not write anything.

Storing it in a record does not write anything.

Returning it does not write anything.

Only a reachable invocation contributes the invocation effect.

That makes higher-order effects **latent**.

This distinction becomes crucial when closures carry resources or authority.

A closure may contain the capability needed to write a store. Code that merely forwards that closure has not therefore written the store.

Phil wants to keep these ideas separate:

```text
can invoke something that may write
≠
performed the write
```

> **Source example to add after the canonical front end lands:** a higher-order forwarding combinator whose effect parameter stays latent while the callable is passed through, followed by an invocation site where the effect becomes part of the reachable effect footprint.

## 8. Permission is not an effect

Here is another distinction that is easy to blur.

Suppose a computation has the effect:

```text
Write(blob_store)
```

Does that mean the computation has permission to write the store?

No.

An effect describes what the computation **may do** if it executes legally.

Permission is a different question.

Phil represents authority explicitly through capabilities and other authority-bearing values or contracts.

So these two statements are different:

```text
this callable may write blob_store
this context gives the callable authority to write blob_store
```

A callable whose contract permits a write still cannot perform it if the required authority is absent.

Conversely, possessing write authority does not mean a write has happened.

This is important enough to make a rule:

> **Effects describe possible action. Authority describes permission. Neither implies the other.**

That separation lets the checker reject a program for **missing authority** even if the requested operation lies inside its effect bound.

It also lets Phil state negative authority claims properly. “This component cannot delete objects” should not mean merely “our test run did not happen to call delete.” It should mean that the component lacks a checked path to the relevant authority.

> **Source example to add after the canonical front end lands:** one callable whose effect bound includes a storage write but which is rejected because the required authority is absent; and one program that possesses the authority but never invokes the effectful operation.

## 9. The surrounding world can have requirements too

Effects describe what flows outward from a computation.

Sometimes we need the dual-looking question:

> What must the surrounding context make available to the computation?

This is often called **coeffect-like** information.

One concrete way to understand it is through **affordances**.

An environment may afford persistent storage: the relevant kind of storage exists and can in principle be used.

That is not yet authority.

The environment may make the store available while withholding permission to modify it.

So a useful intuition is:

> **An affordance is a kind of coeffect: it describes something the surrounding context makes available.**

Authority and capabilities are another especially important class of contextual requirement, but availability and permission remain distinct.

This gives us four useful questions to keep apart:

1. **Types and resource state:** what values and owned resources exist before and after?
2. **Effects:** what semantically observable actions may occur?
3. **Contextual requirements:** what must the environment make available, including required authority?
4. **Outcomes and obligations:** what can happen, and what claims remain to be discharged?

A single storage operation may participate in all four, but Phil does not collapse them into one giant annotation.

That separation is intentional. It keeps each piece of the type system responsible for a question it can answer precisely.

> **Source example to add after the canonical front end lands:** a small example in which a storage affordance/environment requirement, storage authority, and `Write(store)` effect are visibly separate facts. Do not introduce a new surface-level “coeffect language” merely for the tutorial; use whatever checked contextual-requirement forms the canonical front end actually exposes.

## 10. Protocols become reusable language objects

Phase 0 already treated the upload conversation as part of the program.

Phase 1 generalizes that idea.

A **protocol family** is a reusable description of a conversation pattern.

An actual use of that family creates an exact **protocol instance**.

Each role gets a local session description, and each live runtime endpoint is indexed by:

- the exact protocol instance;
- the exact role;
- the exact current session state.

This matters because two sessions following the same protocol family are still not the same conversation.

A client endpoint from upload session A cannot be substituted for the corresponding client endpoint from upload session B merely because both are currently at the same protocol state.

Likewise, a generic function that accepts an endpoint at an unknown state does not thereby gain permission to send or receive arbitrarily.

The contract must establish the transition that is legal at that state.

So Phase 1 gets reusable protocol abstraction without losing the exact state discipline that made Phase 0 useful.

> **Source example to add after the canonical front end lands:** two instances of the same protocol family plus a negative cross-instance endpoint substitution; and a small endpoint-polymorphic callable that cannot perform an unconstrained communication action until its contract establishes the required state transition.

## 11. Providers are contracts, not privileged libraries

Most useful systems depend on things whose implementation may vary:

- storage;
- hashing;
- clocks;
- randomness;
- transports;
- operating-system services;
- hardware devices;
- foreign libraries.

Phil calls an architectural implementation boundary of this kind a **provider**.

A provider contract says what clients may rely on.

That can include more than operation names. It may include:

- callable behavior;
- authority surface;
- resource transitions;
- failure behavior;
- state simulation;
- lifecycle/crash behavior;
- history-wide laws;
- evidence competence;
- assumptions and trust boundaries.

A concrete implementation becomes eligible only when it is **qualified** for the exact public contract.

Successful linking is not qualification.

Matching function signatures are not qualification.

Passing a few tests is not automatically qualification for a universal claim.

A provider may need tests, proofs, checked models, explicit assumptions, or other evidence depending on the claim being made.

This is how Phase 1 makes implementation replacement meaningful.

If two materially different implementations both satisfy the same public provider contract, the architecture can remain the same while the realization changes.

That is a small-scale version of Phil's larger promise:

> **Architecture executable, implementation replaceable.**

Phase 1 proves this for ordinary providers inside the first Phil implementation.

Phase 2 will attack the bigger privileged implementation: the compiler/checker itself.

> **Source example to add after the canonical front end lands:** one provider contract with two qualified implementations or materially distinct test realizations, plus an ABI-compatible but unqualified implementation that is rejected. The tutorial should explain qualification evidence without implying that tests alone prove arbitrary provider laws.

## 12. Ordinary data and control must obey the same rules

A language for architectures also needs ordinary programming constructs.

Records, sum types, branches, loops, and recursion cannot become escape hatches around the semantic model.

For records and sums, structural mode follows what the value owns.

For branches, continuing paths must agree on the resource state needed after reconvergence.

For loops, the backedge must re-establish an explicit state contract.

For recursion, a recursive callable is checked against a stabilized callable contract rather than by asking the compiler to unfold the program forever and discover what it does.

This leads to an important boundary in Phil:

> **Runtime computation may be unbounded. Static checking must not require unbounded search.**

A loop can run for as long as the program requires. The checker does not need to prove how many times it will execute.

Instead, it checks that every admitted pass around the loop re-establishes the declared resource/state invariant.

Likewise, Phil uses dependent types where they buy precision, but dependency is not permission to run arbitrary effectful programs during type checking.

The language can therefore be computationally powerful without making the compiler omniscient.

> **Source example to add after the canonical front end lands:** one resource-carrying loop whose initial edge and backedge re-establish the same explicit state, one rejected backedge that loses or changes a linear owner, and one small record/sum example whose structural mode follows its contents.

## 13. The two witnesses should look different

The best test of a generalization is not whether the old example still works.

It is whether a different example works **for different reasons** without requiring special machinery.

Phase 1 therefore keeps two positive witnesses.

### The framed upload

The upload architecture remains the compatibility witness.

It still needs:

- exact protocol progression;
- recognition before receive commit;
- policy and digest evidence;
- explicit ownership transfer;
- branch-sensitive failure/resource behavior;
- bounded authority;
- preserved assurance lineage.

Phase 1 must not weaken those rules in the name of generalization.

### Steve

Steve provides different pressure.

A content-addressed store needs to care about things such as:

- digest identity;
- exact subjects of equality/evidence claims;
- install-if-absent behavior;
- provider qualification;
- authority confinement;
- stable object identity;
- storage failure semantics.

There is no reason its architecture should look like an upload protocol.

If both programs begin as ordinary `.phil` source and travel through the same semantic pipeline, their differences become evidence that the abstractions are doing real work.

The compiler should not know either witness by name.

> **Future Tour structure:** once both canonical source witnesses exist, this section should become the spine of the executable half of the tutorial. Follow one small slice of upload and one small slice of Steve side by side, showing how the same generic concepts — contracts, authority, effects, identities, providers, lowering — express genuinely different programs.

## 14. Lowering is not where the compiler gets to improvise

Eventually source programs must become executable machine behavior.

That process is called **lowering**.

A conventional compiler description can make lowering sound like a recipe:

```text
source construct X
→ target instruction sequence Y
```

Phil needs a more flexible definition because several different implementations may correctly realize the same architecture.

For example, a target may:

- inline a callable or keep a call boundary;
- specialize a generic or pass an explicit provider;
- stage bytes through a temporary buffer;
- choose one of several qualified providers;
- use a runtime check or an accepted assurance carrier;
- choose a target-specific representation.

Those choices need not change the source architecture.

So Phil treats lowering as a **checked refinement relation**.

The governing rule is:

> **Lowering may choose representation; it may not choose semantics.**

The lowering producer may propose a realization.

A verifier then checks the relationship between the exact source architecture and that realization.

Every live semantic fact needs an explicit fate.

It may be:

- preserved directly;
- realized by a concrete mechanism;
- enforced at runtime;
- erased after accepted discharge;
- exported across an explicit boundary;
- refined into a stronger target fact with a new obligation;
- carried as an explicit assumption dependency.

What is not allowed is a generic “we dropped it because the backend no longer needed the field.”

This is one of Phil's most important competence-boundary rules:

> **A later stage may forget representation only after it has accounted for meaning.**

> **Source/realization example to add later:** show one semantic source effect and one target-introduced staging operation. The tutorial should make clear that the staging operation is a realization effect with explicit authority/failure/cost accounting, not a retroactive claim that staging was part of the source semantics.

## 15. Source effects and machine events are different things

The effects section gave us source-level statements such as:

```text
Write(blob_store)
Send(endpoint)
```

A machine implementation may perform many more low-level operations:

- allocate memory;
- copy bytes;
- marshal arguments;
- call a runtime helper;
- synchronize threads;
- stage data between memory domains;
- clean up temporary objects.

Those machine operations are not automatically new source effects.

Some are internal realization machinery.

But “internal” does not mean “irrelevant.”

If a realization operation introduces authority, failure, cost, subject-transfer, deployment, or trust consequences, those consequences still need to be accounted for at the appropriate layer.

So Phil distinguishes:

```text
source semantic effect
from
realization effect / mechanism
```

The implementation is free to change mechanisms as long as the checked refinement still preserves the public semantic boundary and records the new obligations it introduces.

This is how Phil can allow implementation diversity without defining semantics as “whatever the first compiler happened to emit.”

## 16. Assurance follows the exact claim

Phase 1 does not invent a new assurance system for generics, providers, functions, protocols, or effects.

They all use the same basic idea Phase 0 introduced: **obligations and evidence stay attached to exact claims**.

Suppose a generic body has been checked under requirements `R`.

A concrete instantiation should usually need to show that `R` holds for its exact parameters. It should not have to re-prove the generic body from scratch.

Suppose a provider implementation has evidence for one exact public contract revision.

That evidence does not automatically qualify it for a different revision.

Suppose a runtime check establishes a fact about one exact semantic subject.

That evidence cannot be retargeted merely because another subject currently has equal bytes or the same machine representation.

Suppose a target introduces a stronger ABI requirement than the source ever claimed.

The target cannot borrow authority from the more abstract source theorem. It needs an explicit derived obligation for the stronger fact.

Phil's assurance story therefore keeps asking the same questions:

- What exact proposition or relationship is being claimed?
- What exact semantic subject does it concern?
- What evidence establishes it?
- Under what assumptions and validity scope?
- Which later transformations depend on it?
- Where does the claim stop?

A certificate is useful only when those answers remain inspectable.

## 17. The checker is deliberately less powerful than the runtime language

Phil is intended to permit general runtime computation, including loops and recursion.

But type checking should not become “run the program and see whether the theorem eventually becomes obvious.”

That would make checking unpredictable or nonterminating, and in the general case it cannot work.

Phil therefore draws a hard line between:

- computation the runtime may perform;
- bounded computation used for definitional equality;
- certificate-checkable automatic reasoning;
- explicit evidence for stronger claims;
- runtime checks for dynamic uncertainty;
- explicit assumptions when neither proof nor checking closes the gap.

A useful summary is:

```text
bounded computation
→ definitional equality

accepted evidence
→ propositional/static claims

runtime mechanism
→ dynamic uncertainty

explicit assumption
→ visible trust boundary
```

This makes the checker less magical and more useful.

When a program is rejected, Phil wants the rejection to name a competent reason:

- a linear resource was duplicated;
- a protocol endpoint is at the wrong state;
- required authority is absent;
- an effect bound was widened;
- evidence names the wrong subject;
- a provider is unqualified;
- a loop backedge failed its resource contract;
- an assumption disappeared during lowering.

It should not fail because theorem search wandered off indefinitely.

## 18. The grammar is already normative; the front end is not finished

Phase 1 now has one normative concrete-syntax authority:

```text
grammar/phase1-surface.ebnf
```

That file defines **Phase 1 Surface Grammar v1**.

It fixes the lexical and concrete structure of the current syntax epoch, including the effect-set forms discussed earlier in this tour.

But grammar acceptance is only the first layer.

A source file still has to pass through:

```text
bytes / text
→ lexical + grammar structure
→ located surface form
→ name/scope resolution
→ elaboration
→ Core/static checking
→ architecture instantiation
→ Systems realization
→ backend / target
```

The canonical parser and elaborator must agree with the exact Grammar-v1 revision rather than defining an accidental second language through parser-library behavior.

That is why this draft contains no claimed executable Phase 1 `.phil` listings yet.

A tutorial example should eventually satisfy a stronger standard than “this looks plausible according to the EBNF.”

Every source listing in the finished Phase 1 Tour should be:

1. accepted by the canonical parser for the exact Grammar-v1 revision;
2. accepted by the semantic layer it is intended to demonstrate;
3. accompanied by a deliberately rejected companion where that distinction is pedagogically useful; and
4. exercised in CI so documentation drift becomes a build failure.

Until that front-end path exists, prose is safer than fake certainty.

## 19. What this draft will gain as Phase 1 closes

This version of the Tour is intentionally semantic-first.

As Phase 1 implementation closes, it should gain executable source in roughly this order:

1. **Canonical declarations and roots** — enough ordinary source to show that architecture comes from the program, not compiler-installed witness bindings.
2. **Generics and structural requirements** — linear identity, rejected discard, rejected duplication.
3. **Callables, effects, and authority** — latent effect propagation, subject-indexed effects, missing-authority rejection, higher-order narrowing.
4. **Protocol abstraction** — reusable family/instance identity and cross-instance rejection.
5. **Provider qualification/replacement** — one contract, multiple realizations, unqualified replacement rejection.
6. **Ordinary data and cyclic control** — records/sums plus explicit join/backedge resource state.
7. **Upload and Steve source witnesses** — small end-to-end slices of both programs through the same front end.
8. **Systems/assurance views** — show the checked realization facts, derived obligations, and exact evidence lineage for those source slices.
9. **Runnable commands** — only once the repository can offer commands that exercise the canonical Phase 1 source path rather than a tutorial-only fixture.

At that point the Tour should receive the same readability pass as the Phase 0 edition: define jargon where it first becomes necessary, keep the main narrative concrete, and move implementation archaeology out of the reader's path.

## 20. Where Phase 1 stops

Phase 1 removes one privileged assumption:

> the language is not secretly the semantics of one demonstrator.

It does **not** remove every privileged assumption in the project.

Phase 1 may still use one conventional implementation and one conventional host/backend profile.

It does not require:

- an independently written second Phil compiler/checker;
- GPU, NPU, EVM, Solana, or other materially different execution targets;
- independently certified component composition;
- a package ecosystem;
- a mature standard library, formatter, or IDE;
- arbitrary effect handlers;
- multiparty or asynchronous protocol semantics;
- unrestricted type-level theorem proving.

Those are later pressures.

The roadmap has a useful rhythm:

```text
Phase 0 — Establish: one architecture works.
Phase 1 — Generalize: no privileged program.
Phase 2 — Replace: no privileged implementation.
Phase 3 — Retarget: no privileged machine model.
Phase 4 — Compose: no privileged monolith.
Phase 5 — Deploy: no privileged laboratory.
```

Phase 1 is done when the upload demonstrator and Steve are no longer special things the compiler knows how to translate.

They are simply programs in Phil.

## 21. The ideas to keep

If you remember only a few things from this Phase 1 tour, remember these:

- **Phase 1 removes special cases.** The architecture must come from ordinary program declarations and checked contracts, not witness recognition inside the compiler.
- **Semantic identity is not representation identity.** Equal pointers, symbols, handles, addresses, or bytes do not silently merge distinct architectural subjects.
- **Generic code receives no secret privileges.** If it copies, drops, calls, writes, assumes, or depends on something, that requirement belongs in its checked interface.
- **Ownership survives abstraction.** Putting a linear thing inside a closure, record, generic, branch, or loop does not make the ownership obligation disappear.
- **Callables are semantic values, not just machine signatures.** Their contracts include resource, authority, effect, failure, and assurance boundaries.
- **Effects are may-effect bounds.** Implementations may narrow them but may not silently widen them.
- **Effects are not authority.** What a computation may do and what it is permitted to do are different facts.
- **Higher-order effects are latent.** Passing a function that may write does not perform the write.
- **An affordance is a kind of coeffect.** Contextual requirements describe what the surrounding world makes available; availability and permission still remain distinct.
- **Protocols are reusable but instances stay exact.** Two conversations following the same protocol are still different sessions.
- **Providers are qualified against contracts.** Linkability and nominal resemblance do not establish semantic replacement.
- **Lowering is checked refinement.** It may choose representation and mechanism; it may not choose new source semantics.
- **Assurance follows exact claims and subjects.** Evidence cannot be retargeted because two things happen to look alike.
- **The runtime may be powerful without making the checker omniscient.** Automatic checking stays inside deliberately bounded competent procedures.
- **Grammar and static semantics are separate.** Grammar v1 says what source has Phil's concrete shape; the canonical front end must still establish what that source means and whether it is allowed.

The shortest version is still the Phase 1 charter's:

> **Phase 0 proves the idea locally. Phase 1 removes the special cases.**
