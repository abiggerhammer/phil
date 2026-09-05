# A Tour of Phil — Phase 1

## From one architecture to a language for architectures

*Work-in-progress Phase 1 edition. The canonical Grammar-v1 parser/elaborator/front-end path is now available, so this Tour is beginning its executable-source pass. The `.phil` listings below are taken from source forms exercised by the Phase 1 front-end corpus and named semantic-routing tests. Where a listing demonstrates only one competence layer, the surrounding text says so; parseability is never treated as proof of semantic acceptance.*

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

The ordinary root form is now real source rather than tutorial pseudocode. One front-end conformance case is:

```phil
program main = instantiate pkg.Arch {
  entry ingress : U32;
  assume true within trust.zone;
  export obligation proof.ready to audit.sink;
  observable metrics.bytes;
};
```

The important point is what is *not* present: there is no compiler-recognized upload or Steve switch. `pkg.Arch` is an ordinary architecture reference, and the entry, assumption, exported obligation, and observable are ordered source items checked through the same program-root machinery. The front-end test also renames the source program while supplying the same stable lineage identity and checks that display spelling does not become semantic identity. See [`Phase1GrammarV1ProgramSurfaceMain.hs`](../../test/Phase1GrammarV1ProgramSurfaceMain.hs).

The final upload/Steve side-by-side listings will make this section more concrete still, but the program-root syntax and its stable-identity boundary are no longer hypothetical.

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

Phil therefore treats display names, file paths, source positions, pointers, handles, backend symbols, and allocation addresses as possible representations of an identity — not as the identity itself.

Phase 1 now makes another distinction here: **stable lineage** is not the same thing as a checked revision.

An identity-bearing declaration or generative architecture/process occurrence has a stable lineage key. In the Phase 1 model, exact `DeclarationKey`, `InstanceKey`, and `ProcessKey` lineage is persisted with the source bundle. A top-level declaration may also carry its admitted `@key("...")` lineage attribute. Tooling may create a fresh key for a genuinely new site, but certifiable identity cannot be reconstructed later by hashing whatever file path, name, or source offset happens to exist today.

That matters during ordinary editing.

A lineage-preserving rename or move can keep the same stable key.

Copying or independently recreating an occurrence normally creates a fresh key.

Changing a public contract or implementation may change a checked revision even while the stable lineage remains the same.

So Phil keeps apart:

```text
stable lineage identity
≠
current source spelling/location
≠
checked interface/definition/instance revision
```

The collection of source text plus exact persisted lineage and related source-level metadata is called a **SourceBundle**. It is an input to checking, not an ambient Haskell project object and not ordinary runtime program behavior.

This principle will recur throughout the tour:

> **Representation coincidence is not semantic identity.**

And now we can add a second one:

> **Stable identity is carried deliberately; it is not rediscovered from accidents of the current source tree.**

For a top-level declaration, that lineage can be visible directly in source:

```phil
@key("decl:upload-id")
record UploadId {}
```

The canonical SURF-010 SourceBundle fixture carries that exact declaration lineage together with separate stable instance and process keys. Those occurrence keys are bundle metadata rather than attributes on architecture items, which is why a rename or move can preserve identity while copying a genuinely new site requires fresh lineage. See [`surf010-inline.bundle`](../../test/fixtures/phase1/surf010-inline.bundle).

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

Grammar v1 spells those requirements explicitly. This front-end fixture routes the three currently Core-backed categories through their competent semantic checkers:

```phil
record Routed[T : Type] requires {
  structural T : duplicate;
  proposition true;
  provider P : ProviderContract;
} {
  value : T
}
```

Here `structural T : duplicate;` does not make `T` duplicable. After binder resolution it becomes a contraction requirement on the exact generic parameter, which a concrete instantiation must satisfy. The same test verifies that a missing or ambiguous `T` resolution rejects rather than selecting a convenient binder. See [`Phase1GrammarV1GenericRequirementElaborationMain.hs`](../../test/Phase1GrammarV1GenericRequirementElaborationMain.hs).

The structure-polymorphic identity/discard/duplicate trio is still the best compact tutorial example to add once we choose the final pedagogical bodies, but the requirement surface and its stable binder routing are already executable.

## 4. Ownership does not disappear inside abstraction

Phase 0 already used three structural modes:

- **unrestricted** values may be duplicated and discarded;
- **affine** values may be discarded but not duplicated;
- **linear** values may be neither duplicated nor discarded.

Phase 1 keeps those rules when values become generic, get placed inside records, cross branches, enter loops, are sent between processes, or are captured by closures.

This matters because abstraction can otherwise become a laundering mechanism.

Suppose a linear capability is placed inside a generic box. If the box suddenly becomes freely copyable, the program has duplicated the capability indirectly.

Suppose a linear resource is captured by a closure. If the closure is then treated as an unrestricted function value, the resource has again been duplicated through representation.

Phil instead derives the structural behavior of compound things from what they own.

A closure owning a linear capture is linear.

A record owning a linear field cannot become unrestricted merely because the record has a convenient name.

A loop carrying a linear owner must account for that owner at the backedge.

A branch join cannot invent a hidden “maybe the resource is here” representation merely to make two incompatible branches fit.

And putting a stateful restricted occurrence behind an unrestricted wrapper does not make that occurrence safe to alias between processes. Structural permission belongs to the value being copied; it does not erase the identity and ownership of reachable state hidden behind it.

The broad rule is:

> **Abstraction may hide representation. It may not hide ownership.**

The source can also state an intentionally stricter possession mode when that restriction belongs to the public contract. The production corpus contains this complete example:

```phil
module corpus.closure_explicit_mode;

callable OneShot(x : U32) -> U32 {
  outcomes { success U32 };
  outcome success U32 {
    state ();
    callee consume;
  }
}

component Demo() {
  let f = closure mode linear (x : U32) satisfies OneShot captures () {
    return x;
  };
}
```

`mode linear` is not permission to weaken a linear capture; it is a stronger possession restriction on the callable value itself. The parser preserves it exactly and the later callable-mode semantics decide whether the closure's captures justify that mode. See [`22-closure-explicit-mode.phil`](../../test/fixtures/phase1-surface/accepted/22-closure-explicit-mode.phil).

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
- success, typed-negative, declared-terminal, and fatal outcomes;
- postconditions and evidence;
- residual obligations;
- cost information where relevant.

This lets Phil state a useful refinement rule.

Suppose a caller is prepared for a function that may read and write a store.

An implementation that only reads is narrower. That can be safe.

An implementation that may also send data over the network is wider. That is not silently substitutable.

Likewise, an implementation that requires **less** caller authority can be a valid refinement, while one that requires new authority cannot be slipped in merely because its machine signature matches.

Failure behavior matters too. A same-signature implementation that introduces a new fatal outcome or changes what resources remain on a branch is not automatically a refinement.

So higher-order substitution is about semantic boundaries, not just ABI compatibility.

Here is a deliberately dense callable from the front-end conformance corpus. It is useful precisely because its clauses stay distinct rather than collapsing into “function metadata”:

```phil
callable C[E : Effects] requires {
  effects E within {IO, Audit};
} (x : U32) -> Unit {
  requires true;
  consumes {x, store.slot};
  borrows {loan};
  authority {Cap, OtherCap};
  effects {IO, Audit(x)};
  outcomes {success Unit};
  outcome success Unit {}
  ensures true;
  obligation true;
  assumes true;
  cost 7;
  callee preserve;
}
```

The corresponding test checks that requirements, consumption, borrowing, authority, effects, outcomes, obligations, assumptions, cost, and callee transition remain separate ordered categories. References such as `Cap` or `store.slot` still need the competent semantic context; parsing the declaration does not manufacture them. See [`Phase1GrammarV1CallableEffectsMain.hs`](../../test/Phase1GrammarV1CallableEffectsMain.hs).

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

Effects parameters are live in the canonical front end too. This test fixture uses the same exact parameter twice with a concrete effect set in between:

```phil
callable GenericEffects[E : Effects, T : Type]() -> Unit {
  effects E;
  effects {IO, IO};
  effects E;
}
```

The duplicate `IO` entries normalize as a set, while the two uses of `E` remain uses of the same resolved stable generic parameter. Missing, wrong-kind, or foreign binder evidence rejects explicitly rather than turning `E` into a stringly typed effect name. See [`Phase1GrammarV1CallableEffectsMain.hs`](../../test/Phase1GrammarV1CallableEffectsMain.hs).

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

> **Next executable example:** a higher-order forwarding combinator whose effect parameter stays latent while the callable is passed through, followed by an invocation site where the effect becomes part of the reachable effect footprint.

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

> **Next executable example:** one callable whose effect bound includes a storage write but which is rejected because the required authority is absent; and one program that possesses the authority but never invokes the effectful operation.

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

> **Next executable example:** a small example in which a storage affordance/environment requirement, storage authority, and `Write(store)` effect are visibly separate facts. Do not introduce a new surface-level “coeffect language” merely for the tutorial; use the checked contextual-requirement forms the canonical front end already exposes.

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

There is another boundary before transfer: a Phil value does not become a valid protocol `Message` merely because it can be moved or serialized somehow. Boundary-message admissibility is checked first. A scoped loan, live endpoint, or live authority-bearing occurrence cannot be smuggled through an ordinary aggregate and thereby acquire deferred remote-delegation semantics that Phase 1 never admitted.

So Phase 1 gets reusable protocol abstraction without losing the exact state and boundary discipline that made Phase 0 useful.

> **Next executable example:** two instances of the same protocol family plus a negative cross-instance endpoint substitution; a small endpoint-polymorphic callable that cannot perform an unconstrained communication action; and a message-admissibility pair showing that “movable value” is not automatically “protocol message.”

## 11. Processes are semantic; threads are not

Protocols tell us which communications are legal. They do not, by themselves, tell us what the program's concurrent population is.

Phase 1 therefore admits a deliberately small concurrency model: a **finite static process network** declared by the architecture.

A process occurrence is a semantic member of that network. It has an exact stable `ProcessKey`, an executable target, and its own local Phil execution state.

This is not the same thing as an operating-system process, thread, task, worker, coroutine, GPU lane, or event-loop callback.

A realization may map:

- one Phil process to one host thread;
- one Phil process across several target stages;
- several Phil processes onto one thread or event loop.

Those mappings are implementation choices as long as the checked realization preserves the Phil process identities, ownership, communication causality, effects, failures, and terminal behavior.

The governing distinction is:

> **Process identity belongs to the architecture. Thread identity belongs to the realization.**

The static process population is generative. Two distinct architecture occurrences of the same reusable definition can contain corresponding declaration-local process sites and still produce distinct process occurrences. A reference to an already-existing architecture occurrence does not clone its process population.

Every restricted semantic occurrence is owned by exactly one process context at a time unless an existing Phil rule explicitly transfers it. Unrestricted immutable values or evidence may be copied only through their ordinary structural permission; an unrestricted wrapper is not permission to create shared mutable semantic state behind the checker's back.

Internal communication is synchronous CSP-style rendezvous. An internal send/receive or branch action advances only as one joint transition over the exact dual endpoints of the same protocol instance and opposite roles. The transfer consumes the predecessor ownership and produces only the declared successors.

Source declaration order is not a scheduler. Phil preserves each process's local program order and architecture/protocol causality. Independent events otherwise remain unordered unless some explicit semantic relation orders them.

This leaves several properties deliberately outside the default semantics:

- fairness;
- eventual response;
- deadlock freedom;
- deadlines;
- scheduling policy.

Those may be obligations a program proves or assumes. They are not facts the concurrency checker gets for free.

Process activation itself is pleasantly small source syntax. Inside an architecture:

```phil
process worker_run = worker;
```

The right-hand side names an already-created executable occurrence; it does not instantiate or clone it. The process site supplies generative process/activation identity through its persisted SourceBundle lineage. The same syntax-completeness audit that introduced this form explicitly keeps OS threads, tasks, workers, and scheduler choices outside source semantics. See [`syntax-semantics-completeness-v1.md`](../phase-1/syntax-semantics-completeness-v1.md).

## 12. External participants are explicit, and failure stays local

Not every protocol participant has to be a Phil process.

An architecture may explicitly classify a protocol role as **external**.

That word is deliberately narrow. It says only:

> this role lies outside the Phil process population.

It does **not** automatically choose:

- a transport;
- a boundary representation;
- an entry resource;
- a capability or authority source;
- an assumption;
- a deployment relation;
- a target realization.

Those are separate competence questions.

Missing internal ownership also does not mean “probably external.” Every executable protocol-role occurrence must be classified explicitly. An unresolved, ambiguous, inactive, or unactivated internal target rejects rather than falling back to externality.

Failure obeys the same non-magic rule.

If an external peer disappears, a Phil process waiting on it does not automatically become successfully terminal. The internal process may remain active and stuck with a live endpoint or obligation. Likewise, a fatal transition in one Phil process does not silently cancel its peers or clean up their resources.

A local process reaches a terminal fact only when its own declared terminal transition has closed the exact local resource, endpoint, and obligation boundary required for that outcome.

The whole network reaches successful terminal closure only when every static Phil process occurrence is terminal and the root architecture's remaining boundary/assurance obligations are closed.

An active network with no enabled step is **stuck**. It is not successful termination.

The internal/external distinction is explicit in the source rather than inferred from a missing binding:

```phil
role p.client = worker;
role p.server = external;
```

`worker` must resolve to the appropriate activated internal occurrence. `external` means only that the peer role lies outside the Phil process population; it does not choose a transport or synthesize successful failure handling. The production corpus contains both accepted and malformed external-role cases, while the concurrency checker owns the semantic closure rules. See [`syntax-semantics-completeness-v1.md`](../phase-1/syntax-semantics-completeness-v1.md).

## 13. Providers are contracts, not privileged libraries

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

The declaration surface makes the separation visible:

```phil
provider Store {}
provider implementation MemoryStore satisfies Store {}
opaque provider implementation RemoteStore satisfies Store;
```

These lines declare a contract and two implementations that *claim* to satisfy it. They do not self-qualify either implementation. Qualification is an assurance/build object checked outside ordinary source, which prevents “I wrote `satisfies`, therefore the theorem is true” from becoming a language escape hatch. These forms are exercised by the Grammar-v1 determinacy and provider-declaration tests; see [`Phase1GrammarV1DeterminacyMain.hs`](../../test/Phase1GrammarV1DeterminacyMain.hs) and [`Phase1GrammarV1ProviderDeclarationsMain.hs`](../../test/Phase1GrammarV1ProviderDeclarationsMain.hs).

## 14. Ordinary data and control must obey the same rules

A language for architectures also needs ordinary programming constructs.

Records, sum types, tuples, branches, loops, and recursion cannot become escape hatches around the semantic model.

For records, sums, and products, structural mode follows what the value owns unless an admitted stricter declaration-level contract justifies strengthening it.

For branches, continuing paths must agree on the resource state needed after reconvergence.

For loops, the initial edge and every backedge must re-establish the same explicit state contract and logical invariant.

For recursion, a recursive callable is checked against a stabilized callable contract rather than by asking the compiler to unfold the program forever and discover what it does.

This leads to an important boundary in Phil:

> **Runtime computation may be unbounded. Static checking must not require unbounded search.**

A loop can run for as long as the program requires. The checker does not need to prove how many times it will execute.

Instead, it checks that every admitted pass around the loop re-establishes the declared resource/state invariant.

Likewise, Phil uses dependent types where they buy precision, but dependency is not permission to run arbitrary effectful programs during type checking.

The language can therefore be computationally powerful without making the compiler omniscient.

A declaration can state a stricter nominal mode explicitly. This accepted production fixture is intentionally tiny:

```phil
module corpus.record_mode;

record FireOnceToken mode linear {
  id : U64
}
```

The keyword `linear` does not let the parser decide whether the declaration is semantically justified; it preserves the author's requested strengthening for the structural-mode checker. Ordinary compound values still derive their minimum mode from what they own. See [`11-record-explicit-linear-mode.phil`](../../test/fixtures/phase1-surface/accepted/11-record-explicit-linear-mode.phil).

A later Tour pass should pair this with the resource-carrying loop fixture so the initial edge and backedge can be read next to the declaration whose owner they preserve.

## 15. Ordinary execution has target-independent rules

Once Phil admits ordinary runtime computation, “whatever Haskell or LLVM happens to do” cannot define its evaluation semantics.

Within each Phil process, Phase 1 uses deterministic strict sequential evaluation.

At the language level:

- statements execute in textual order;
- strict subexpressions and runtime arguments evaluate left to right;
- conditions and scrutinees evaluate before branch selection;
- untaken branches do not execute;
- local bindings are initialized, lexical, and immutable;
- Phase 1 rejects active lexical shadowing rather than letting a compiler's internal name map define binder identity.

A target may reorder, fuse, inline, vectorize, or otherwise transform the implementation only when a checked refinement preserves the source effects, failures, ownership/evidence succession, authority, and observables.

Arithmetic also has Phil semantics.

A runtime `UInt[w]` literal must fit exactly in its width. Plain `+`, `-`, and `*` denote mathematical arithmetic together with the obligation that the result remains representable. They do not silently wrap, saturate, or gain a target-specific overflow trap.

If overflow is genuinely runtime-contingent, the program uses an explicit checked arithmetic operation with explicit success/failure outcomes.

This generalizes to target partiality.

A valid Phil transition may not turn into target UB, poison, an undeclared trap, OOM, stack exhaustion, gas exhaustion, queue overflow, device-capacity failure, or another realization-only failure simply because the backend picked a partial mechanism.

The target condition must instead be:

- mapped to a declared source outcome;
- proved satisfied or unreachable;
- covered by an accepted runtime enforcement relation;
- made dependent on an explicit admitted assumption;
- exported as a deployment requirement;
- or rejected as an invalid realization.

There are two related negative rules worth remembering.

First, legal affine weakening is just structural weakening. It does not secretly call a destructor, `close`, `free`, flush, finalizer, or provider operation. Effectful cleanup is an explicit resource-specific transition.

Second, time, randomness, environment variables, host/process/thread identity, scheduler state, and similar observations are not ambient Phil inputs. They enter only through explicit providers, entries, capabilities, protocols, boundaries, or assumptions.

> **Next executable example:** left-to-right evaluation with one visible effect, exact `UInt` boundary cases, checked-overflow branching, a hidden-finalizer rejection, and a clock/random/environment access that succeeds only through an explicit provider or boundary.

## 16. The two witnesses should look different

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

> **Future Tour structure:** once both canonical source witnesses exist, this section should become the spine of the executable half of the tutorial. Follow one small slice of upload and one small slice of Steve side by side, showing how the same generic concepts — contracts, authority, effects, identities, processes, providers, lowering, verification — express genuinely different programs.

## 17. Lowering is not where the compiler gets to improvise

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
- map processes to threads or an event loop;
- choose one of several qualified providers;
- use a runtime check or an accepted assurance carrier;
- choose a target-specific representation or placement.

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

> **Source/realization example to add later:** show one semantic source effect and one target-introduced staging operation, plus a process-to-worker mapping. Make clear that staging/threading are realization mechanisms with explicit authority/failure/cost/correspondence accounting, not retroactive source semantics.

## 18. Source effects and machine events are different things

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

## 19. Assurance follows the exact claim

Phase 1 does not invent a new assurance system for generics, providers, functions, protocols, processes, runtime checks, or effects.

They all use the same basic idea Phase 0 introduced: **obligations and evidence stay attached to exact claims**.

Suppose a generic body has been checked under requirements `R`.

A concrete instantiation should usually need to show that `R` holds for its exact parameters. It should not have to re-prove the generic body from scratch.

Suppose a provider implementation has evidence for one exact public contract revision.

That evidence does not automatically qualify it for a different revision.

Suppose a runtime check establishes a fact about one exact semantic subject.

That evidence cannot be retargeted merely because another subject currently has equal bytes or the same machine representation.

Suppose a target introduces a stronger ABI requirement than the source ever claimed.

The target cannot borrow authority from the more abstract source theorem. It needs an explicit derived obligation for the stronger fact.

Evidence reuse follows declared validity dimensions. An unrelated edit should not gratuitously invalidate independently scoped evidence, but a change to the relevant proposition, subject, context, revision, qualification, or other declared dependency does invalidate it.

Phil's assurance story therefore keeps asking the same questions:

- What exact proposition or relationship is being claimed?
- What exact semantic subject does it concern?
- What evidence establishes it?
- Under what assumptions and validity scope?
- Which later transformations depend on it?
- Where does the claim stop?

A certificate is useful only when those answers remain inspectable.

## 20. Verification is not the same thing as certification

Phase 1 makes the programmer-facing verification boundary explicit.

The first question is whether the program is intrinsically valid Phil.

Some failures are simply language errors:

- duplicating a linear owner;
- performing an illegal session action;
- using authority that is not possessed;
- giving one restricted occurrence to two processes;
- violating a required resource-state join.

Those failures are rejected by the competent semantic checker. A permissive assurance policy cannot turn them into assumptions, runtime checks, exports, or “proof obligations to solve later.”

Only claims that the language permits to remain live become **residual obligations**.

For an accepted source bundle, application verification constructs a deterministic exact obligation/dependency graph. The inspectable object that records the source revisions, intrinsic result, obligations, dependencies, selected policy, and evidence references is a **VerificationBundle**.

Proof discovery can then be replaceable. A prover, solver, test producer, or other automation may propose evidence. Its failure or timeout means only “no accepted evidence from this attempt.” It does not prove the proposition false and does not silently create an assumption.

Likewise, source-level `prove P` is an evidence-introduction form, not an assertion escape hatch. It succeeds only through a competent local mechanism: definitional reasoning, exact in-scope evidence, or a certificate-producing decision procedure whose certificate is checked.

Residual obligations may be closed only through dispositions the exact policy and architecture permit, such as:

- accepted static evidence;
- an exact runtime enforcement binding;
- an explicit admitted assumption;
- an explicit exported deployment/consumer obligation.

And even a completely closed source VerificationBundle is not yet a certified executable artifact.

A particular artifact also depends on its exact architecture realization, Systems representation, StageContract preservation relation, provider admissions, target-specific strengthenings, runtime carriers, deployment requirements, and any obligations introduced by lowering.

So Phil separates two stages:

```text
source verification
≠
artifact certification
```

Final certification composes source closure with realization/StageContract closure and produces a scoped **AssuranceManifest** naming the accepted dispositions and the remaining trusted computing base.

This prevents a common mistake: proving a good fact about the source and then silently assuming every compiler/backend choice preserved it.

> **Verification example to add once the generic path is runnable:** one source obligation closed by reusable evidence, followed by two realizations: one whose StageContract preserves the source result and one that introduces a new target obligation. The same source proof should remain reusable while the second artifact remains uncertified until the new obligation closes.

## 21. The checker is deliberately less powerful than the runtime language

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
- a process role was left implicitly external;
- a loop backedge failed its resource contract;
- an assumption disappeared during lowering.

It should not fail because theorem search wandered off indefinitely.

## 22. The grammar is normative; the front end now checks it

Phase 1 has one normative concrete-syntax authority:

```text
grammar/phase1-surface.ebnf
```

That file defines **Phase 1 Surface Grammar v1**.

It fixes the lexical and concrete structure of the current syntax epoch.

But grammar acceptance is only the first layer.

A Phase 1 compilation begins from more than raw text. The conceptual pipeline is now:

```text
SourceBundle
(source text + exact persisted lineage)
→ lexical + Grammar-v1 structure
→ located surface form
→ name/scope/lineage resolution
→ elaboration + Core/static checking
→ ArchitectureInstance + static process network
→ application VerificationBundle
→ ArchitectureRealization / Systems / StageContract
→ artifact AssuranceManifest
→ backend / target
```

Some implementations may fuse or reorganize those passes internally. The competence boundaries and checked relationships are what matter.

The canonical parser and elaborator agree against the exact Grammar-v1 revision rather than defining an accidental second language through parser-library behavior. Likewise, lineage comes from the SourceBundle rather than being reconstructed from Haskell object identity or mutable source positions.

That is why this edition can finally contain claimed Phase 1 `.phil` listings.

Every source listing in the finished Phase 1 Tour should still satisfy a stronger standard than “this looks plausible according to the EBNF.” It should be:

1. accepted by the canonical parser for the exact Grammar-v1 revision;
2. carried through the same source/SourceBundle competence boundaries used by ordinary programs where the example depends on them;
3. accepted by the semantic layer it is intended to demonstrate;
4. accompanied by a deliberately rejected companion where that distinction is pedagogically useful; and
5. traceable to CI coverage so documentation examples do not quietly become a second syntax dialect.

The examples introduced in this pass are therefore copied from named front-end tests or production-corpus fixtures, with those sources linked beside the explanation. Later passes can replace small routing fixtures with the final upload and Steve source witnesses where that makes the story clearer.

## 23. What this Tour will gain as Phase 1 closes

This Tour began semantic-first because the source front end was still moving. That constraint is gone. The remaining work is now to replace the most useful prose-only placeholders with compact executable witnesses and inspectable artifacts in roughly this order:

1. **Canonical declarations, roots, and SourceBundles** — now represented by initial executable examples above; expand them into the final ordinary upload/Steve roots and lineage fixtures.
2. **Generics and structural requirements** — the requirement surface is now shown; add the final identity/discard/duplicate body trio.
3. **Callables, effects, and authority** — callable and Effects source are now shown; add the smallest higher-order narrowing and missing-authority pairs.
4. **Protocol abstraction and message admissibility** — reusable family/instance identity, cross-instance rejection, and the boundary between movable values and legal messages.
5. **Static process networks** — process activation and explicit external participation are now shown; add one exact rendezvous and ProcessKey-generativity witness.
6. **Provider qualification/replacement** — the source declaration/implementation boundary is now shown; add the two realized/qualified Steve alternatives and unqualified rejection.
7. **Ordinary data, cyclic control, and deterministic execution** — structural mode source is now shown; add explicit join/backedge state, evaluation order, and checked arithmetic.
8. **Application verification** — one inspectable VerificationBundle with intrinsic rejection, residual obligations, policy dispositions, and reusable evidence.
9. **Upload and Steve source witnesses** — small end-to-end slices of both programs through the same front end and verification path.
10. **Systems/realization/assurance views** — show checked realization facts, derived obligations, process mappings, runtime carriers, exact evidence lineage, and the final AssuranceManifest.
11. **Runnable commands** — commands that exercise the canonical Phase 1 source path rather than a tutorial-only fixture.

At that point the Tour should receive the same readability pass as the Phase 0 edition: define jargon where it first becomes necessary, keep the main narrative concrete, and move implementation archaeology out of the reader's path.

## 24. Where Phase 1 stops

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
- dynamic process creation, term-level spawn/await, or scheduler-control syntax;
- asynchronous mailbox/buffer semantics or multiparty protocols;
- shared mutable-memory atomics as Phil source semantics;
- arbitrary effect handlers;
- unrestricted type-level theorem proving.

Those are later pressures.

But Phase 1 does have to leave Phase 2 a usable target.

A second implementation should not have to reverse-engineer Haskell constructors, witness tables, source-position-derived identities, traversal order, or private test setup to discover what Phil means.

The freeze handoff therefore needs portable, versioned artifacts sufficient to enumerate and replay the checked interfaces and conformance judgments: the exact Grammar-v1 corpus, SourceBundles and lineage, checked semantic/architecture outputs or reconstructible equivalents, VerificationBundles, evidence/policy inputs, realization/StageContract artifacts, final manifests, and positive/negative fixtures with their competent rejection layers.

That handoff format is test and transition infrastructure. Phase 1 does not need to standardize the permanent ecosystem interchange format before it can finish.

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

They are simply programs in Phil — and the specification/conformance handoff is precise enough that another implementation can agree about what those programs mean.

## 25. The ideas to keep

If you remember only a few things from this Phase 1 tour, remember these:

- **Phase 1 removes special cases.** The architecture must come from ordinary program declarations and checked contracts, not witness recognition inside the compiler.
- **Semantic identity is not representation identity.** Equal pointers, symbols, handles, addresses, or bytes do not silently merge distinct architectural subjects.
- **Stable lineage is explicit SourceBundle input.** Declaration, architecture-occurrence, and process identities are not recomputed from current names or source positions.
- **Generic code receives no secret privileges.** If it copies, drops, calls, writes, assumes, or depends on something, that requirement belongs in its checked interface.
- **Ownership survives abstraction.** Putting a linear thing inside a closure, record, generic, branch, process, or loop does not make the ownership obligation disappear.
- **Callables are semantic values, not just machine signatures.** Their contracts include resource, authority, effect, failure, and assurance boundaries.
- **Effects are may-effect bounds.** Implementations may narrow them but may not silently widen them.
- **Effects are not authority.** What a computation may do and what it is permitted to do are different facts.
- **Higher-order effects are latent.** Passing a function that may write does not perform the write.
- **An affordance is a kind of coeffect.** Contextual requirements describe what the surrounding world makes available; availability and permission still remain distinct.
- **Protocols are reusable but instances stay exact.** Two conversations following the same protocol are still different sessions.
- **Processes are semantic; threads are realization.** ProcessKey, ownership, rendezvous, causality, failure, and terminality must survive whatever execution mechanism the target chooses.
- **External participation is explicit.** Missing internal ownership never silently becomes `external`, and external failure does not synthesize Phil process terminality.
- **Providers are qualified against contracts.** Linkability and nominal resemblance do not establish semantic replacement.
- **Ordinary execution has Phil semantics.** Evaluation order, immutable initialized bindings, exact UInt arithmetic, explicit ambient observation, and target partiality do not inherit arbitrary host behavior.
- **Lowering is checked refinement.** It may choose representation and mechanism; it may not choose new source semantics.
- **Assurance follows exact claims and subjects.** Evidence cannot be retargeted because two things happen to look alike.
- **Intrinsic invalidity is not an assurance disposition.** A bad Phil program is rejected before proof/runtime/assumption/export choices are considered.
- **Source verification is not artifact certification.** The realization and StageContract must close their own preservation and target-derived obligations.
- **The runtime may be powerful without making the checker omniscient.** Automatic checking stays inside deliberately bounded competent procedures.
- **Grammar and static semantics are separate.** Grammar v1 says what source has Phil's concrete shape; the canonical front end establishes what that source means and whether it is allowed.

The shortest version is still the Phase 1 charter's:

> **Phase 0 proves the idea locally. Phase 1 removes the special cases.**
