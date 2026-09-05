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

For a complete grouped lookup table of Phil's reserved words, see the [Phase 1 keyword lexicon](../reference/keywords-phase1.md). The Tour introduces those words in context; the lexicon is the place to look one up afterward.

## 1. A first Phil component

Here is about the smallest useful piece of canonical Phase 1 Phil:

```phil
component Worker provides Unit {
    return unit;
}
```

A **component** is an executable part of a Phil system.

This one is named `Worker`. The keyword `provides` names the value type the component presents at its public boundary. Here it provides `Unit`, the simplest value type: there is only one ordinary value of that type, written `unit`.

So the body does exactly what it looks like it does:

```phil
return unit;
```

The keyword `return` finishes this execution path with the value that follows it. Here that value is the literal `unit`.

Nothing very exotic has happened yet. That is intentional. Phil still has ordinary values, expressions, functions, records, branches, loops, and so on.

What makes Phil unusual is what happens when ordinary computation meets resources, communication, authority, and claims about correctness.

We will add those one at a time.

### Source files can name modules and imports

A larger Phil source file can begin by naming its module and importing declarations from another one:

```phil
module demo.basics;
import demo.geometry {Point};
```

The keyword `module` gives the current source module its qualified name. The keyword `import` makes declarations from another module available to this source file; the optional brace list restricts the imported names.

These are source-organization constructs. Importing a name does not create a runtime object, grant authority, or manufacture semantic identity.

## 2. Types say more than how many bits a value occupies

Phil has familiar scalar types such as:

```text
Bool
U8
U32
U64
Unit
```

`Bool` is the Boolean type. Its two literal values are the keywords `true` and `false`. `Unit` is the singleton type we already saw. Spellings such as `U8`, `U32`, and `U64` are unsigned-integer type tokens; the exact supported widths are checked semantically rather than being a fixed list baked into the lexer.

It also has records, sums, tuples, byte sequences, refinements, evidence-bearing types, protocol/session types, and named architectural contracts.

A record can look ordinary:

```phil
record Point {
    x : U32,
    y : U32
}
```

The keyword `record` declares a product-like named type with named fields.

Phil also has sum types. The keyword `data` declares a type whose values may come from different named variants:

```phil
data MaybeByte = None | Some(U8);
```

A `MaybeByte` is either `None` or `Some` carrying one `U8`.

When an existing type already says exactly what you mean, `type` declares an alias:

```phil
type Byte = U8;
```

The alias gives the type another source-level name; it does not create a new runtime representation merely because a new spelling exists.

### Values can be bound and constructed

The keyword `let` introduces a local binding from an expression result:

```phil
let answer = 42;
```

For a record-like value, `construct` explicitly names the constructor target and its field initializers:

```phil
let origin = construct Point {
    x = 0,
    y = 0,
};
```

`construct` does not bypass the type's ownership or refinement rules. It is simply the source form for building a value whose declared fields must check.

### Branches are ordinary source constructs too

Phil has ordinary conditional branching:

```phil
if true {
    return unit;
} else {
    return unit;
};
```

`if` evaluates its condition and executes only the selected branch. `else` introduces the false branch. Untaken branches do not secretly execute effects or consume resources.

For a sum type, `match` selects an arm by constructor shape and can bind the payload carried by that constructor:

```phil
component Inspect(value : MaybeByte) {
    match value {
        None => {
            return unit;
        }
        Some(byte) => {
            return unit;
        }
    };
}
```

Here `Some(byte)` binds the variant payload to the local name `byte` inside that arm. Arm-local names remain local to their arm.

Later we will see why Phil sometimes adds an explicit `join` state contract when multiple continuing branches have to reconverge with restricted resources. For unrestricted examples like these, the familiar branching intuition is enough to start.

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

The keyword `mode` introduces the record's structural-use contract; `linear` is the selected mode. The other two mode keywords are `unrestricted` and `affine`. The field `id` is just a `U64`, but the record as a whole therefore has a stronger contract: a `FireOnceToken` is linear.

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

The keyword `outcomes` declares the callable's public set of possible result classes. Here there is one: `success U32`, meaning ordinary successful completion carries a `U32`. Phil can also distinguish typed-negative, terminal, and fatal outcomes when a contract needs those cases to have different meanings.

The singular `outcome success U32 { ... }` block then gives details that apply specifically to that success branch. `state ();` says that this branch exposes no named successor-state slots. `callee consume;` says that taking this branch consumes the callable value itself instead of leaving it available for another call.

So the contract tells us something a normal arrow type would not: this callable is consumed by the successful call. It is a one-shot callable.

A named function uses the keyword `fn` and states which callable contract it satisfies:

```phil
callable Identity(x : U32) -> U32 {
    outcomes { success U32 };
}

fn identity(x : U32) -> U32 satisfies Identity {
    return x;
}
```

`fn` introduces the named executable function declaration. `satisfies Identity` is not optional documentation: it names the public callable contract against which the function body is checked. A named function that calls itself **must** be declared `recursive fn`; an unmarked self-recursive `fn` does not typecheck. Mutual recursion likewise has to be declared as an explicit recursive group so the public callable contracts can be stabilized before any member body is checked. Recursion therefore remains contract-visible rather than acquiring secret privileges from implementation bodies.

A closure can explicitly satisfy a callable contract too:

```phil
component Demo() {
    let f = closure mode linear (x : U32)
        satisfies OneShot captures () {
        return x;
    };
}
```

A **closure** is a function value that may carry values from the surrounding lexical environment with it. The keyword `satisfies` names the callable contract this closure claims to implement; the checker still has to verify that the closure really fits that contract. It is not a cast or a self-certification escape hatch.

The keyword `captures` makes the closure's captured environment explicit. `captures ()` means this closure carries no surrounding values. If it captured names, those captured values would remain subject to their ordinary ownership rules; putting a linear value inside a closure does not make it copyable.

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

The keyword `effects` introduces the callable's effect bound; the braces contain the effects that invocation is allowed to contribute.

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

The keyword `authority` lists authority that the caller must make available for a legal invocation. It does not say that the operation necessarily exercises all of that authority, just as `effects` does not say every allowed effect necessarily happens.

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

Each `role` gives the conversation as seen from one participant. `send (x : U8)` means that role is allowed and required to send a `U8` at this point in the session; `receive (x : U8)` is the dual receive state. `then` introduces the session state that follows the communication, and `end Done` says the conversation is locally finished with terminal label `Done`.

The two roles above are dual descriptions of the same one-message conversation:

```text
Client: send U8 → done
Server: receive U8 → done
```

There is an important distinction here: the `send` inside the **protocol declaration** describes a legal session transition. It does not itself execute a send.

Actual component code performs communication with the term-level `send ... on ...` operation. Here `send` is a Phil keyword, not a library function or a method supplied by the component. Its basic source form is:

```phil
send value on endpoint
```

Read that as: **send this value through this live session endpoint, and advance the endpoint to its next protocol state.** The checker verifies that the endpoint is currently at a `send` state and that the value has the required message type.

In a component, that looks like this:

```phil
component ClientWorker(endpoint : Client[Ping], payload : U8) {
    let done = send payload on endpoint;
    close done;
}
```

Here `endpoint` is a live client-side session endpoint and `payload` is the byte to send. `send payload on endpoint` consumes the current endpoint and produces the successor endpoint for the `end Done` state.

`close` is another Phil keyword. Its form is simply `close endpoint`; it consumes a live endpoint whose protocol state is terminal and closes that session endpoint. So `close done;` does not mean “close some arbitrary OS handle”: the checker requires `done` to be a session endpoint at an `end` state.

So there are already two separate layers:

```text
protocol declaration   says which send is legal
component body         actually performs the send
```

A surrounding architecture still has to supply the **exact** endpoint occurrence and payload to the component. Merely assigning a component to a protocol role does not synthesize the `send` expression or silently inject arbitrary runtime values into its body.

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

The keyword `instance` creates a concrete architecture occurrence from a reusable declaration. The architecture `Pair` creates two occurrences of `Worker`:

```phil
instance left = Worker;
instance right = Worker;
```

Those are two semantic occurrences even though they came from the same reusable component definition.

The keyword `process` activates an already-created executable occurrence as a member of the program's static Phil process network:

```phil
process left_run = left;
process right_run = right;
```

It does **not** instantiate `Worker` again, and it does not prescribe an OS process or thread.

Finally, `program` declares a root program and `instantiate Pair` selects a fresh root occurrence of the `Pair` architecture:

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

Inside an architecture, `protocol ping = Ping;` creates a protocol occurrence named `ping` from the reusable `Ping` family. The `role` bindings then say who is responsible for each side of that occurrence.

The first role is internal: it is assigned to the Phil occurrence `client`. That assignment does **not** execute the Client role and does not inject an endpoint into `ClientWorker` by magic; the component body still has to perform the appropriate `send`/`receive` operations using the exact endpoint values supplied at its execution boundary.

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

`provider Store {}` declares the public provider contract. `provider implementation ...` declares an implementation whose body is represented in ordinary Phil source. `opaque provider implementation ...;` declares an implementation whose internals are outside the ordinary source body and must therefore be justified through the relevant external/assurance boundary.

In both implementation forms, `satisfies Store` names the public provider contract the implementation is claiming to refine. As with `satisfies` on a closure, the keyword names the intended contract; it does not prove the claim by itself.

Why distinguish a provider from an ordinary concrete library?

Because Phil wants the architecture to depend on the public contract rather than accidentally depend on one implementation.

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

`[T : Type]` introduces a generic parameter named `T` whose kind is `Type`. The keyword `requires` opens the set of facts and capabilities that must be supplied when this generic declaration is instantiated.

Inside that block, the three lines are three different kinds of prerequisite:

- `structural T : duplicate;` requires a structural permission for values of `T`;
- `proposition true;` requires a logical proposition to hold;
- `provider P : ProviderContract;` requires an exact provider contract.

### Structural requirements

Here **structural** does not mean the fields or memory layout of `T`. It comes from structural logic: the rules for whether a value may be *discarded* or *duplicated*.

Phil currently exposes two such generic permissions:

```phil
structural T : discard;
structural T : duplicate;
```

`discard` and `duplicate` are language-defined permission names rather than reserved lexer keywords. `discard` means the generic body is allowed to use **weakening** on a `T`: it may decide not to use that value at all.

`duplicate` means the generic body is allowed to use **contraction** on a `T`: it may make the same value available to more than one use.

Those permissions line up with the structural modes from section 3:

| Actual mode of `T` | May satisfy `discard` | May satisfy `duplicate` |
| --- | --- | --- |
| unrestricted | yes | yes |
| affine | yes | no |
| linear | no | no |

So this requirement:

```phil
structural T : duplicate;
```

does **not** grant copying to an arbitrary `T`. It says that this generic declaration is only valid for actual types whose mode already permits duplication. A linear actual therefore fails that requirement; an unrestricted actual can satisfy it.

There is an important zero-requirement case too. If generic code merely transfers an abstract value from one place to another, without dropping or copying it, it needs neither structural permission. Phil's structural checker also compares what the generic body actually does with the public requirements it declares, so a body that duplicates `T` cannot publish an interface pretending that no duplication permission is needed.

### Proposition requirements

A **proposition** requirement is different. It is not about copy/drop permissions at all. It says:

> **This generic declaration may be used only in a context where this exact logical fact has been accounted for.**

The example says:

```phil
proposition true;
```

which is deliberately boring: `true` is a proposition that is trivially satisfied. It is present in this conformance fixture mainly to exercise the proposition-requirement path. A useful generic would normally require a nontrivial fact about the objects or contracts it depends on.

Writing `proposition P;` does not make `P` true, and it is not a runtime `Bool` test. The proposition is checked as a Phil logical proposition and becomes part of the generic's public requirement set. At a particular instantiation, that exact requirement must then have an accepted disposition—for example matching evidence, or an explicit assumption/export when the active policy permits one.

So the three requirement categories answer different questions:

```text
structural T : duplicate;       can values of T legally be copied here?
proposition P;                  has the logical fact P been established/accounted for?
provider P : ProviderContract;  is the required provider contract available here?
```

This is why genericity does not become an escape hatch around ownership or proof:

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

The keyword `claim` declares a reusable proposition. Here `Positive(x)` names the proposition `x > 0`.

The type:

```phil
{v : U32 | v > 0}
```

is a **refinement type**. It describes a `U32` together with the proposition that its value is greater than zero. The name `v` is the refinement-local name for the value while the proposition is being stated.

The keyword `ensures` introduces a postcondition: a proposition the callable contract promises on the relevant successful return boundary.

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

The `@key(...)` attribute supplies stable declaration lineage for this declaration. The quoted text is an identity carrier, not a display label and not evidence for any semantic claim. `key` is the admitted semantic attribute name, but it is not itself a reserved lexer keyword.

Other occurrence lineage can travel with the source in a **SourceBundle**.

This is not something a beginner has to write by hand for every ordinary edit. It is the identity substrate that lets later verification, evidence, realization, and independent implementations agree about which semantic object a claim concerns.

The rule to remember is simpler than the machinery:

> **Looking the same is not the same as being the same.**

## 18. How the Ping pieces fit

We now have enough vocabulary to put the three different responsibilities next to one another without pretending they are the same thing.

First, the protocol says what communication is legal:

```phil
protocol Ping {
    role Client = send (x : U8) then end Done;
    role Server = receive (x : U8) then end Done;
}
```

Second, executable component code performs the communication when it is given the appropriate runtime values:

```phil
component ClientWorker(endpoint : Client[Ping], payload : U8) {
    let done = send payload on endpoint;
    close done;
}
```

Third, the architecture says which semantic occurrence is responsible for which protocol role:

```phil
architecture ExternalPeer {
    instance client = ClientWorker;
    process client_run = client;
    protocol ping = Ping;
    role ping.Client = client;
    role ping.Server = external;
}

program main = instantiate ExternalPeer;
```

Read those as three separate statements of meaning:

```text
Ping                 says the Client role must send one U8
ClientWorker         contains code that actually performs a send
role ping.Client ... says the client occurrence is responsible for that role
```

The earlier version of this Tour accidentally collapsed the last two. It showed a `ClientWorker` that merely returned `unit`, then assigned that occurrence to `ping.Client`, which made it look as though role assignment automatically supplied behavior. It does not.

There is still one boundary this compact example intentionally leaves visible: **runtime provisioning**. `ClientWorker` needs the exact `Ping.Client` endpoint occurrence and a `U8` payload. The architecture/entry machinery has to supply those exact runtime values; the role declaration alone is not a constructor call, dependency injector, or hidden endpoint parameter.

The current Phase 1 production corpus checks the term-level `send value on endpoint` form and separately checks architecture process/role participation. Until the canonical whole-source path has a single small fixture that closes that runtime-provisioning seam end to end, this Tour should not pretend that the seam is implicit.

That distinction is useful in its own right:

> **The protocol constrains behavior. The component performs behavior. The architecture assigns responsibility and supplies the surrounding resources.**

Notice also what none of those layers has chosen yet. We have not said TCP or Unix sockets. We have not assigned an OS thread. We have not selected a serialization library. We have not smuggled in ambient network authority. Those are later competent choices.

That is what “building systems from the outside in” means in Phil: establish the semantic boundaries first, then choose implementations and runtime bindings that satisfy them.

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

- **Phil is still an ordinary programming language.** Modules, types, local bindings, construction, functions, branches, and pattern matches work alongside the systems contracts rather than being replaced by them.
- **Phil makes system rules part of the program.** Protocols, ownership, authority, effects, obligations, and architecture are checked objects rather than comments.
- **Ownership can be structural.** Unrestricted, affine, and linear values have different copy/drop permissions.
- **Contracts describe semantic boundaries.** A machine signature is often only one part of a callable or provider interface.
- **Effects are not authority.** What code may do and what it is permitted to do are separate facts.
- **Protocols constrain communication; component code performs it.** Assigning a process to a protocol role does not inject a `send` or `receive` into its body.
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