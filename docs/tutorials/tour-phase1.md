# A Tour of Phil

## From a tiny component to a checked system

*Phase 1 edition. This is the beginner-facing introduction to the current Phil language. The examples use canonical Grammar-v1 source forms exercised by the Phase 1 front end and production corpus. A source form being shown here does not mean every later backend or realization path for it is complete; this tour introduces the language and its competence boundaries in the order a new reader needs them.*

Phil is a systems programming language built around a simple idea:

> **The important rules of a system should be part of the program, not folklore around the program.**

That includes ordinary things such as values and functions, but also things that many languages leave to comments, framework conventions, build files, or code review:

- who owns a resource;
- which conversations are legal;
- which authority a computation may use;
- what effects it may have;
- which implementation is allowed to stand behind an interface;
- which facts have actually been proved or checked;
- what a compiler backend must preserve.

You do not need formal logic, compiler theory, or security terminology to follow this tour. We will start with very small Phil programs and introduce each larger idea only when the previous one gives us a reason to need it.

## 1. A first Phil component

Here is about the smallest useful piece of canonical Phase 1 Phil:

```phil
component Worker provides Unit {
    return unit;
}
```

A **component** is an executable part of a Phil system.

This one is named `Worker`. It **provides** `Unit`, the simplest value type: there is only one ordinary value of that type, written `unit`.

So the body does exactly what it looks like it does:

```phil
return unit;
```

Nothing very exotic has happened yet. That is intentional. Phil still has ordinary values, expressions, functions, records, branches, loops, and so on.

What makes Phil unusual is what happens when ordinary computation meets resources, communication, authority, and claims about correctness.

We will add those one at a time.

## 2. Types say more than how many bits a value occupies

Phil has familiar scalar types such as:

```text
Bool
U8
U32
U64
Unit
```

It also has records, sums, tuples, byte sequences, refinements, evidence-bearing types, protocol/session types, and named architectural contracts.

A record can look ordinary:

```phil
record Point {
    x : U32,
    y : U32
}
```

But Phil asks another question about values that ordinary machine-layout types do not answer:

> **What are you allowed to do with this value structurally?**

Can you copy it? Can you ignore it? Must exactly one continuation receive it?

That question becomes important as soon as a value represents something scarce or stateful rather than just inert data.

## 3. Some values have ownership rules

Phil uses three structural modes:

- **unrestricted** — may be copied and discarded;
- **affine** — may be discarded, but not copied;
- **linear** — may be neither copied nor silently discarded.

A type can impose a stricter mode when that restriction is part of its meaning. This is real accepted Phase 1 syntax:

```phil
record FireOnceToken mode linear {
    id : U64
}
```

The field `id` is just a `U64`, but the record as a whole has a stronger contract: a `FireOnceToken` is linear.

Why would that be useful?

Imagine the value represented permission to fire a one-shot actuator, consume a cryptographic nonce, commit a transaction, or advance a protocol endpoint. Accidentally duplicating the value could mean doing the protected action twice.

A linear type lets the checker reject that structural mistake before it becomes a runtime convention.

The important point is not that everything in Phil is linear. Most ordinary values need not be. The point is that **ownership is part of the type discipline when it matters**.

That rule survives abstraction. Putting a linear value inside a record, closure, branch, loop, or generic does not make it stop being linear.

## 4. Functions can have public contracts

A machine-level function type usually tells you something like:

```text
(U32) -> U32
```

That is useful, but systems code often needs the caller to know more:

- what resources the call consumes;
- what it merely borrows;
- what authority it needs;
- what effects it may perform;
- which kinds of failure can occur;
- what remains true afterward.

Phil therefore has first-class **callable contracts**.

Here is a small one:

```phil
callable OneShot(x : U32) -> U32 {
    outcomes { success U32 };
    outcome success U32 {
        state ();
        callee consume;
    }
}
```

Read the first line just like a function signature: `OneShot` accepts a `U32` and returns a `U32` on success.

The rest tells us something a normal arrow type would not: this callable is consumed by the successful call. It is a one-shot callable.

A closure can explicitly satisfy that contract:

```phil
component Demo() {
    let f = closure mode linear (x : U32)
        satisfies OneShot captures () {
        return x;
    };
}
```

The closure is itself a value. `mode linear` says possession of that callable is linear: the program cannot silently duplicate it into two independent call sites.

This gives us a general Phil pattern:

> **An interface describes the semantic boundary a caller may rely on; an implementation has to fit inside that boundary.**

That idea will reappear for effects, providers, protocols, and lowering.

## 5. Effects say what a call may do

Suppose two functions both take `Unit` and return `Unit`.

One only computes locally. The other writes storage.

Those functions have the same ordinary input/output shape, but they are not interchangeable in every context.

Phil represents semantically observable actions as **effects**.

A callable can say, for example:

```phil
callable EffectCarrier() -> Unit {
    effects {IO, Audit};
}
```

An effect bound is a **may-effect upper bound**. It says what invocation is permitted to do, not what every execution must do.

So an implementation that performs only `Audit` may still fit a public contract allowing `{IO, Audit}`. An implementation that additionally performs some undeclared network effect does not silently fit.

Effects can also carry exact semantic subjects. Conceptually, these are different claims:

```text
Write(blob_store)
Write(log)
Send(endpoint)
Read(clock)
```

The names matter because Phil does not identify two semantic subjects merely because they happen to share a machine representation.

There is one more distinction we need before effects are useful for security reasoning.

## 6. Permission is not the same thing as an effect

Suppose a callable may have the effect:

```text
Write(blob_store)
```

That does **not** automatically mean it has permission to write the store.

Phil keeps two questions separate:

> **What may this computation do?** — effect

and

> **What is this computation permitted to do?** — authority

A callable contract can name authority separately from effects:

```phil
callable StoreOperation() -> Unit {
    authority {StoreWrite};
    effects {WriteStore};
}
```

The exact names here stand for ordinary static contracts in the surrounding program. The key point is the shape: authority and effects occupy different parts of the interface.

That lets Phil express useful negative facts. A component that has no path to delete authority is stronger than a component that merely happened not to call delete during testing.

It also keeps higher-order code honest. Merely possessing or passing around a callable that *could* write does not perform the write. Its invocation effect remains latent until the callable is actually invoked.

## 7. Protocols make conversations part of the program

Now imagine two parts of a system that communicate.

A comment might say:

```text
client sends one byte; server receives it
```

Phil can make that rule a checked language object instead:

```phil
protocol Ping {
    role Client = send (x : U8) then end Done;
    role Server = receive (x : U8) then end Done;
}
```

A **protocol** is the rulebook for a conversation.

It says which role may send or receive, what kind of message is involved, and what state follows the action.

The two roles above are dual descriptions of the same one-message conversation:

```text
Client: send U8 → done
Server: receive U8 → done
```

One actual use of `Ping` is a **protocol instance**. Two different instances of the same protocol family are still different conversations.

That matters because live endpoints carry state. An endpoint from conversation A cannot be substituted for the matching-looking endpoint from conversation B merely because both are waiting to send a `U8`.

Phil therefore treats the conversation state and instance identity as semantic information, not just runtime handles.

There is another boundary here too: a value being movable does not automatically make it an admissible protocol message. Live endpoints, scoped loans, or authority-bearing occurrences cannot be hidden inside an aggregate to acquire remote-transfer permission by accident.

## 8. Architecture says which parts actually exist

We now have executable pieces and protocol descriptions, but we have not said which concrete pieces make up a program.

That is the job of an **architecture**.

Here is a complete small Phase 1 source file from the production corpus:

```phil
component Worker provides Unit {
    return unit;
}

architecture Pair {
    instance left = Worker;
    instance right = Worker;
    process left_run = left;
    process right_run = right;
}

program main = instantiate Pair;
```

Read it from the middle outward.

The architecture `Pair` creates two occurrences of the reusable `Worker` component:

```phil
instance left = Worker;
instance right = Worker;
```

Then it activates each occurrence as a member of the program's static Phil process network:

```phil
process left_run = left;
process right_run = right;
```

Finally the root program selects that architecture:

```phil
program main = instantiate Pair;
```

Now we have enough vocabulary to state one of Phil's central ideas precisely:

> **Architecture is part of program meaning.**

The two `Worker` occurrences are not the same semantic object merely because they came from the same declaration and currently execute identical code.

## 9. Phil processes are not OS threads

The word **process** in the previous example is semantic.

A Phil process is a member of the architecture's static concurrent population. It has stable identity, local execution state, ownership, communication relationships, and terminal behavior.

It does not mean “create a POSIX process” or “create a thread.”

A target realization might run:

- one Phil process per host thread;
- several Phil processes on one event loop;
- one Phil process across several target stages.

Those are implementation choices.

The checked requirement is that the realization preserve the Phil-level facts that matter: process identity, ownership, causality, communication, effects, failures, and terminal behavior.

So:

> **Process identity belongs to the architecture. Thread identity belongs to the implementation.**

Phil's Phase 1 process network is deliberately bounded and static. There is no source-level `spawn`, scheduler directive, mailbox, or thread API hiding behind the `process` declaration.

## 10. Some protocol participants can be outside Phil

Not every peer has to be another Phil process.

Suppose our `Ping` client talks to a service implemented elsewhere.

The architecture can say so explicitly:

```phil
architecture ExternalPeer {
    instance client = ClientWorker;
    process client_run = client;
    protocol ping = Ping;
    role ping.Client = client;
    role ping.Server = external;
}
```

The first role is internal: it is bound to a Phil occurrence.

The second role is explicitly `external`.

That word is intentionally narrow. It does **not** mean:

- use TCP;
- trust the peer;
- choose a wire format;
- grant authority;
- assume the peer behaves correctly.

It means only:

> this role lies outside the Phil process population.

Those other questions have their own contracts and competence boundaries.

Likewise, a missing or invalid internal binding does not silently become external. Externality has to be stated.

## 11. Providers make implementation replacement explicit

Systems often depend on services whose implementation can vary: storage, clocks, hashing, randomness, transports, operating-system facilities, hardware devices, foreign libraries.

Phil calls an architectural implementation boundary of this kind a **provider**.

The source can declare a contract and implementations that intend to satisfy it:

```phil
provider Store {}

provider implementation MemoryStore satisfies Store {}

opaque provider implementation RemoteStore satisfies Store;
```

Why distinguish a provider from an ordinary concrete library?

Because Phil wants the architecture to depend on the public contract rather than accidentally depend on one implementation.

But the source word `satisfies` is not magic. It does not let an implementation certify itself.

A provider may need evidence about:

- operation behavior;
- resource transitions;
- authority confinement;
- state simulation;
- crash/lifecycle behavior;
- history-wide laws;
- assumptions or trust boundaries.

Only a **qualified** implementation is eligible to stand behind the contract for the claims being made.

This is the small-scale form of Phil's project slogan:

> **Architecture executable, implementation replaceable.**

## 12. Generic code must say what it needs

Reusable code introduces a subtle ownership problem.

Suppose `T` is an abstract type.

May generic code copy a `T`? Drop it? Serialize it? Send it over a protocol? Use some provider associated with it?

Phil's answer is: only if the generic contract provides the required fact or permission.

Here is canonical generic requirement syntax:

```phil
record Routed[T : Type] requires {
    structural T : duplicate;
    proposition true;
    provider P : ProviderContract;
} {
    value : T
}
```

The important line for ownership is:

```phil
structural T : duplicate;
```

That does not *grant* duplication to every `T`. It records that this generic abstraction requires contraction permission from the concrete actual.

A linear actual therefore cannot satisfy a generic body that genuinely duplicates its value unless some separate admitted rule justifies that duplication.

This is why genericity does not become an escape hatch around ownership:

> **Abstract code gets no secret privileges.**

## 13. Phil can carry checked facts in types and contracts

Sometimes a type needs to say more than “this is a `U32`.”

For example:

```phil
claim Positive(x : U32) = x > 0;

callable KeepPositive(x : {v : U32 | v > 0}) -> U32 {
    ensures x > 0;
}
```

The type:

```phil
{v : U32 | v > 0}
```

is a **refinement type**. It describes a `U32` together with the proposition that its value is greater than zero.

The `claim` declaration gives a proposition a reusable name. The `ensures` clause states a postcondition of the callable.

This does not mean Phil's type checker runs arbitrary theorem search until it feels convinced.

Phil deliberately distinguishes several ways a fact can become available:

- bounded definitional computation;
- already accepted evidence;
- certificate-checkable reasoning;
- an explicit runtime check;
- an explicit assumption when trust really is required.

The goal is to keep the competence boundary inspectable. A timeout from a proof search tool is not proof that a proposition is false, and a source assertion is not automatically evidence that it is true.

## 14. Bad Phil is rejected before assurance policy gets a vote

This distinction is important enough to state directly.

Some programs are intrinsically invalid Phil.

Examples include:

- duplicating a linear owner;
- performing a session action that is illegal in the current protocol state;
- using authority that the context does not possess;
- assigning one restricted occurrence to two processes;
- failing to re-establish the required resource state at a join or loop backedge.

Those are language errors.

They do not become “proof obligations for later” merely because a build policy is permissive.

Only claims that Phil permits to remain live become **residual obligations** that can be discharged by proof, runtime enforcement, an admitted assumption, or an explicit exported obligation when the architecture permits that disposition.

That separation prevents assurance machinery from becoming an escape hatch around the language itself.

## 15. Source verification is not artifact certification

Suppose the source is valid and all of its application-level obligations have been handled.

Are we done?

Not quite.

The compiler still has to choose a concrete realization:

- which qualified provider implementation to use;
- how to represent values;
- how to map processes onto runtime mechanisms;
- whether to stage or copy data;
- which target ABI or calling convention to use;
- which runtime checks or evidence carriers remain necessary.

Those choices can introduce new requirements that did not exist in the source.

Phil therefore separates:

```text
source verification
from
artifact certification
```

The source-side result is recorded in a **VerificationBundle**: an inspectable account of the exact source revisions, intrinsic result, obligations, dependencies, policy, and evidence references.

A particular artifact additionally needs its realization and preservation story checked.

The final **AssuranceManifest** says which claims and dispositions justify that artifact and what trusted boundary remains.

This is how Phil avoids a common failure mode in verified systems work: proving something useful about the source, then silently assuming that every compiler and deployment choice preserved it.

## 16. Lowering may choose representation, not meaning

Eventually Phil has to become machine code or some other executable target representation.

A backend may legitimately:

- inline a function;
- specialize a generic;
- choose a qualified provider;
- insert a staging buffer;
- map Phil processes onto threads or an event loop;
- use a runtime enforcement mechanism.

Phil does not require all correct implementations to look alike.

Instead, lowering is treated as a checked **refinement relation**.

The governing rule is:

> **Lowering may choose representation; it may not choose semantics.**

If a source-level fact is no longer represented directly, the later stage still has to account for what happened to it. It may have been preserved, realized by another mechanism, discharged by evidence, enforced at runtime, exported as an obligation, or strengthened into a new target-specific requirement.

It cannot simply vanish because the backend no longer finds it convenient.

## 17. Why stable identity appears at all

Only now do we need one of the more abstract-looking Phase 1 ideas.

Consider this architecture again:

```phil
architecture Pair {
    instance left = Worker;
    instance right = Worker;
    process left_run = left;
    process right_run = right;
}
```

`left` and `right` may have the same type and the same implementation. They are still different occurrences.

Likewise, renaming `left_run` should not necessarily mean “destroy this semantic process and create an unrelated one” if the edit is intentionally lineage-preserving.

Phil therefore carries stable lineage deliberately rather than deriving identity from mutable presentation details such as a path, display name, source offset, pointer, or target symbol.

A top-level declaration can carry an explicit key:

```phil
@key("decl:upload-id")
record UploadId {}
```

Other occurrence lineage can travel with the source in a **SourceBundle**.

This is not something a beginner has to write by hand for every ordinary edit. It is the identity substrate that lets later verification, evidence, realization, and independent implementations agree about which semantic object a claim concerns.

The rule to remember is simpler than the machinery:

> **Looking the same is not the same as being the same.**

## 18. A complete small source file

We can now read a complete canonical Phase 1 example without introducing new concepts halfway through it:

```phil
protocol Ping {
    role Client = send (x : U8) then end Done;
    role Server = receive (x : U8) then end Done;
}

component ClientWorker provides Unit {
    return unit;
}

architecture ExternalPeer {
    instance client = ClientWorker;
    process client_run = client;
    protocol ping = Ping;
    role ping.Client = client;
    role ping.Server = external;
}

program main = instantiate ExternalPeer;
```

From top to bottom:

1. `Ping` describes a legal one-byte conversation.
2. `ClientWorker` is an executable Phil component.
3. `ExternalPeer` creates one occurrence of that component.
4. `client_run` activates that occurrence in the Phil process population.
5. `ping` creates a protocol occurrence from the reusable family.
6. The client role is internal and belongs to `client`.
7. The server role is explicitly outside Phil.
8. `main` selects the architecture as the root program.

Notice how much of the system is now inspectable from source without choosing a physical implementation.

We have not said TCP or Unix sockets. We have not assigned an OS thread. We have not selected a serialization library. We have not smuggled in ambient network authority. Those are later competent choices.

That is what “building systems from the outside in” means in Phil: establish the semantic boundaries first, then choose implementations that satisfy them.

## 19. Where the bigger examples fit

The tiny examples in this tour are meant to establish vocabulary, not show the largest thing Phil can express.

The project has two important larger witnesses.

### The framed upload

The Phase 0 upload architecture is the historical end-to-end example. It exercises:

- a multi-step client/server protocol;
- frame recognition before receive commit;
- validation and evidence;
- explicit ownership transfer;
- branch-sensitive failure;
- native lowering and certification.

The [Phase 0 Tour](tour-phase0.md) remains the best place to follow that one system in detail.

### Steve

Steve is a content-addressed store used as a deliberately different Phase 1 pressure case. It exercises digest identity, exact evidence subjects, provider qualification, authority confinement, install-if-absent behavior, lifecycle rules, and storage failure.

The point of keeping both is that the compiler should not know either one by name. They should simply be different Phil programs using the same language machinery.

If you already understand Phase 0 and want the design delta rather than another introduction, read [From Phil Phase 0 to Phase 1](from-phase0-to-phase1.md).

## 20. The ideas to keep

If you remember only a few things from this tour, remember these:

- **Phil makes system rules part of the program.** Protocols, ownership, authority, effects, obligations, and architecture are checked objects rather than comments.
- **Ownership can be structural.** Unrestricted, affine, and linear values have different copy/drop permissions.
- **Contracts describe semantic boundaries.** A machine signature is often only one part of a callable or provider interface.
- **Effects are not authority.** What code may do and what it is permitted to do are separate facts.
- **Protocols are conversations with state.** Two instances of the same protocol are still different sessions.
- **Architecture says which semantic occurrences exist.** Equal-looking instances do not merge.
- **Phil processes are not threads.** Threads, event loops, and placement belong to realization.
- **External peers are explicit.** Missing bindings do not silently become external participants.
- **Provider replacement requires qualification.** Saying `satisfies` is not self-certification.
- **Generic code gets no secret privileges.** It has to state the structural and semantic requirements it actually uses.
- **Intrinsic invalidity comes before assurance policy.** A bad Phil program cannot be rescued by calling the error an assumption.
- **Source verification is not artifact certification.** Compiler and target choices need their own preservation story.
- **Lowering may choose representation, not meaning.**
- **Semantic identity is deliberate.** Looking the same does not make two resources, sessions, processes, or claims interchangeable.

The shortest summary of Phil is still:

> **Phil is a systems language in which architecture is executable and implementation is replaceable.**
