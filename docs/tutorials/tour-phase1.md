# A Tour of Phil

## From a tiny component to a checked system

*Phase 1 edition.*

Phil is a systems programming language for building systems from the outside in. Instead of starting with “what instructions should the computer run?”, Phil starts with questions like:

- What parts does this system have?
- What may those parts say to each other?
- What is each part allowed to do?
- What must be true before the program can take the next step?
- What happens when something goes wrong?

This tour builds up the answers one example at a time. Phil's central idea is:

> **The important rules of a system should be part of the program, not just comments about the program.**

A program might need to follow rules such as “use this permission only once,” “receive a request before sending a reply,” or “never write to this store without permission.” Phil lets you write those rules where its tools can check them.

We will start with a tiny piece of code, then build up to a system with several parts. You do not need formal logic or compiler theory. When we need a technical word, we will explain it beside an example.

### How to read the examples

A **compiler** translates source code into a form a computer can execute. Phil's **checker** checks whether the source follows the language's rules. Checking a declaration is not the same as running a complete program.

Most code blocks below introduce one declaration or show a fragment of a larger program. They are not one file to paste together: some reuse names, and some need declarations or inputs from their surroundings. We label interface sketches and incomplete wiring explicitly. Section 8 shows a complete small source file; the Ping discussion later explains which pieces it does and does not supply.

This tour uses Phase 1's canonical source syntax, called **Grammar v1**. The language has several implementation stages. Showing a source form here does not claim that every way of compiling or deploying it is finished.

The main path is values → ownership → contracts → communicating parts → checking the whole system. The closer looks at branch and loop state are optional on a first reading. For a word you want to look up later, use the [Phase 1 keyword lexicon](../reference/keywords-phase1.md).

## 1. A first Phil component

Here is a tiny component:

```phil
component Worker provides Unit {
    return unit;
}
```

A **component** is an executable part of a Phil system. This one is named `Worker`.

The keyword `provides` says what type of value it presents to its surroundings. A **type** describes what kind of value something is. Here the type is `Unit`, which has just one ordinary value, written `unit`. It is useful when finishing a computation matters but there is no information to return.

The braces `{ ... }` contain the component's body. Inside them, `return unit;` finishes this execution path with that value. The semicolon ends the statement.

Declaring `Worker` does not yet say how many workers a program will have or which ones will run. We will make those choices in section 8.

### Giving source files names

A larger source file can name its module and import declarations from another module:

```phil
module demo.basics;
import demo.geometry {Point};
```

A **module** is a named unit of source code. `module` names this one; `import` makes declarations from another one available here. The list `{Point}` limits this import to `Point`.

Importing a name does not run a component or grant permission to use a resource. It just makes the declaration available to the source file.

## 2. Types say more than how many bits a value occupies

Some Phil types describe familiar data:

| Type | What its values represent |
| --- | --- |
| `Bool` | Either `true` or `false`. |
| `U8`, `U32`, `U64` | Whole numbers without a minus sign, stored in 8, 32, or 64 bits. |
| `I8`, `I32`, `I64` | Whole numbers that can also be negative, in the corresponding widths. |
| `F32`, `F64` | Floating-point numbers, used to represent a range of fractional values. |
| `Unit` | The single value `unit`. |

A bit is a binary digit. The widths matter: for example, a `U8` can hold values from 0 to 255. Phil specifies the rules for its number types rather than silently borrowing whichever rules the target machine happens to use.

### Records group named fields

```phil
record Point {
    x : U32,
    y : U32
}
```

The keyword `record` declares a type with named fields. A `Point` contains both an `x` and a `y`. The colon in `x : U32` means “`x` has type `U32`.”

The keyword `let` gives a local name to the result of an expression. `construct` builds a value of a named type:

```phil
let origin = construct Point {
    x = 0,
    y = 0,
};
```

This fragment builds a `Point` whose two fields are zero, then names it `origin`. Building a value still has to obey the type's rules.

### Some types offer a choice

```phil
data MaybeByte = None | Some(U8);
```

The keyword `data` declares a type with named alternatives, also called **variants**. A `MaybeByte` is either `None`, carrying no extra value, or `Some`, carrying one `U8`. The vertical bar separates the alternatives. Such a type is called a **sum type**.

An alias gives an existing type another name:

```phil
type Byte = U8;
```

`Byte` is another source-level name for `U8`, not a different representation just because it has a different spelling.

### Branches choose what happens next

Inside a component, `if` chooses a branch using a `Bool`:

```phil
if true {
    return unit;
} else {
    return unit;
};
```

Only the selected branch runs. `else` introduces the branch for a false condition.

For a sum type, `match` chooses a branch by the variant it receives:

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

`value : MaybeByte` declares an input parameter. In the `Some` branch, `Some(byte)` gives the carried byte a local name. `=>` separates a pattern from the code to run when it matches. That name is available only in its branch.

The keyword `decide` is another form for handling decision-shaped results. For example:

```phil
data Decision = Yes(U32) | No(U32);

component ReadDecision(choice : Decision) provides U32 {
    decide choice {
        Yes(value) => return value;
        No(value) => return value;
    };
}
```

Both variants carry a number; each branch returns its number. Like `match`, `decide` must cover the possible cases and obey the ownership rules. Calling something a decision does not make it a proof.

So far, types have told us what a value contains. Next we need a different question:

> **May this value be copied or left unused?**

## 3. Some values have ownership rules

> **Phil asks: “Who is responsible for this thing?”**

Copying a number is usually harmless. Copying permission to perform a one-time action might not be.

Phil has three **structural modes**. “Structural” here means the rules for copying and discarding values, not their shape in memory.

| Mode | May be copied? | May be left unused? |
| --- | --- | --- |
| `unrestricted` | Yes. | Yes. |
| `affine` | No. | Yes. |
| `linear` | No. | No. |

For a linear value, the program must account for its use. It can transfer the value to code that consumes it, for example, but cannot secretly make another owner or forget the value.

A type can explicitly require a stricter mode:

```phil
record FireOnceToken mode linear {
    id : U64
}
```

`mode linear` applies to the whole `FireOnceToken`, even though its `id` field is an ordinary number. Think of the token as a one-use permission: two copies must not become two independent permissions.

That analogy describes the ownership rule. What using the token actually does is still determined by the rest of the program's contracts.

### A container inherits its contents' restrictions

What happens without a `mode` annotation?

Phil works out the required mode from the contents. The earlier `Point` is unrestricted because both of its fields are unrestricted. This record is different:

```phil
record ArmedAction {
    token : FireOnceToken
}
```

`ArmedAction` owns a linear token, so it must itself be linear. Otherwise, copying the container would copy the token inside it.

A sum type also has to allow for its most restricted variant. A variant that *might* contain a linear value cannot be treated as freely copyable. Pattern matching can reveal which variant is actually present.

An explicit mode can make a type stricter when its checked rules allow that, but cannot make it more permissive than its contents.

> **No mode annotation means “work out the mode,” not “allow copying.”**

The same principle applies to values kept inside functions, branches, loops, and generic code.

### Borrowing lets you inspect without taking ownership

A **borrow** gives temporary access to a value while its owner keeps ownership:

```phil
record Inspectable mode affine {
    id : U64
}

component ReadId(item : Inspectable) provides U64 {
    let id = borrow item as view {
        return view.id;
    };
    return id;
}
```

`borrow item as view` makes `view` a temporary way to inspect `item` inside the braces. `view.id` reads its `id` field.

The inner `return` supplies the result of the **borrow expression**. It does not end `ReadId` or return ownership of `item`. Since `U64` is unrestricted, the field's value may be copied out. The outer `return id;` then returns that number from the component.

The borrowed view itself cannot leave the borrow's scope. Replacing `return view.id;` with `return view;` would try to let that temporary access escape, and is rejected. Code also cannot consume or invalidate `item` while the view is in use.

When the borrow ends, the temporary view ends. The original owner still owns `item`. This example may leave it unused afterward because `Inspectable` is affine, not linear.

### A closer look: branches that continue

*This and the next subsection are optional on a first reading.*

Suppose two branches continue into the same later code. What values should that later code receive?

When Phil can infer one answer, no extra declaration is needed. When the programmer needs to specify the answer, a **join** gives the branches a shared contract:

```phil
component Joiner(condition : Bool, x : U32) provides U32 {
    if condition
        join state (x_next : U32)
        invariant x_next == x or x_next == 0
    {
        x;
    } else {
        0;
    };

    return x_next;
}
```

`join state (x_next : U32)` says that code after the branches will receive one `U32`, named `x_next`. The true branch supplies `x`; the false branch supplies `0`. Neither branch may read `x_next` before supplying it.

An **invariant** is a claim that must hold whenever execution reaches the point it describes. Here `==` means equality, so the claim says “`x_next` equals `x` or equals zero.” Both branches must establish that claim for the value they supply.

For example, with `x = 7`, the result is 7 when the condition is true and 0 when it is false. The shared claim covers both possibilities.

An invariant is not a hidden runtime `if`, and writing it does not make it true. A branch that cannot establish the join's requirements cannot legally continue through that join. A branch that finishes instead of continuing supplies no join state.

For restricted resources, every continuing branch must also account for the actual owners it carries forward. Writing a name in `state (...)` cannot recreate a resource that the branch already consumed.

### A closer look: loops carry values forward

A loop faces a similar question: what values should its next repetition receive?

Before the example, one new type notation: `{v : U32 | v > 0}` means “a `U32` whose value is greater than zero.” The name `v` stands for the value while stating that rule. Section 13 explains these **refinement types** in more detail.

```phil
component Countdown(n : {v : U32 | v > 0}) {
    loop state (i : U32 = n) invariant i > 0 {
        if i > 1 {
            continue(i - 1);
        } else {
            break;
        };
    };

    return unit;
}
```

`loop` starts the loop. `state (i : U32 = n)` declares the value passed from one repetition to the next: a `U32` named `i`, initially equal to `n`.

The invariant `i > 0` must hold on the first entry and every later entry. The input type establishes it initially.

Inside the loop, `if i > 1` makes a runtime choice. When true, `continue(i - 1)` starts the next repetition with a smaller value. This still satisfies the invariant. Otherwise, `break` leaves the loop.

Starting with `n = 3`, the values are:

```text
3 → 2 → 1 → leave the loop
```

The distinction matters: **the invariant says what must be true on entry; the `if` decides whether to repeat.** Failing an invariant does not secretly become a loop exit.

`continue(...)` explicitly supplies the next state, rather than assigning new values to mutable locals. Where an exit contract requires values, `break(...)` supplies those too. Bare `continue`, `continue()`, `break`, and `break()` supply zero values; they do not mean “reuse the current ones.”

For a linear resource to reach the next repetition, it must be passed through this checked state. A local variable with the same spelling is not enough.

## 4. Functions can have public contracts

A function's input and output types answer one question: what values go in, and what value comes back?

A **contract** records other rules that callers and implementations must follow. Phil uses the keyword `callable` to declare a contract for something that can be called.

Start with a familiar operation: return the input unchanged.

```phil
callable Identity(x : U32) -> U32 {
    outcomes { success U32 };
}

fn identity(x : U32) -> U32 satisfies Identity {
    return x;
}
```

`Identity(x : U32) -> U32` describes a call that accepts a `U32` and returns a `U32` on success. The arrow separates input from output.

> **Phil asks: “What happens when something goes wrong?”**

`outcomes` lists the possible **kinds of result**. This small example lists only `success`, carrying a `U32`. More detailed contracts can distinguish four different control classes:

```phil
outcomes {
    success Stored,
    negative Busy,
    terminal Closed,
    fatal Crashed
};
```

Read them this way:

- `success` means ordinary successful completion. The caller may continue.
- `negative` means a typed, expected non-success result that the caller may handle and continue from.
- `terminal` means a named normal end of the call path. There is no ordinary caller continuation after that branch.
- `fatal` means a named abnormal end of the call path. There is likewise no ordinary caller continuation, but Phil keeps the exact declared outcome identity instead of turning it into a generic failure bucket.

That last distinction is deliberate. A callable declaring `fatal Crashed` produces the exact fatal outcome `Crashed` at the checked caller boundary. It is **not** the same operation as writing `fail FailureClass(...) on resource` inside term code. The latter is an explicit fatal resource/control transition with its own failure class and detail. Keeping those forms separate lets later layers decide how to realize them without the checker inventing meaning that the source did not state.

Because `terminal` and `fatal` have no caller continuation, their dispatch arms cannot pretend to return a caller payload or continue with more statements. Their resources, live endpoints, and obligations must already satisfy terminal-closure rules before Phil accepts either branch as finished.

`fn` introduces the function implementation. `satisfies Identity` names the contract the checker must compare that implementation against. It is not just a comment, and it does not make the implementation correct by declaration.

### A callable can itself be used up

Some callable values are reusable; others represent a one-time action:

```phil
callable OneShot(x : U32) -> U32 {
    outcomes { success U32 };
    outcome success U32 {
        state ();
        callee consume;
    }
}
```

The plural `outcomes` lists the result kinds. The singular `outcome` gives extra rules for one listed result.

`state ();` says that this result exposes no named follow-on state values. `callee` means the callable being invoked. `callee consume;` says that the successful call uses up that callable value: it is not left available for another call.

That is information an input/output arrow alone would not tell the caller.

### Closures are function values

A **closure** is a function value that can carry values from its surroundings. Here is a closure declaration fragment using `OneShot`:

```phil
let f = closure mode linear (x : U32)
    satisfies OneShot captures () {
    return x;
};
```

`captures` lists the surrounding values it carries with it. `captures ()` means it carries none. If it did capture a linear value, that value would keep its ownership restrictions.

`mode linear` makes the closure value itself linear. Enclosing code must call or otherwise legally consume `f` before its scope ends. **This fragment is not a complete component:** putting it in a component and then silently dropping `f` would violate the rule we just introduced.

A function that calls itself must also make that intent explicit with `recursive fn`. A group of functions that call one another needs an explicitly declared recursive group. The checker uses their public contracts when checking those calls; it does not grant extra permissions because it can see their bodies.

The pattern to remember is:

> **The contract tells callers what they may rely on. The implementation must meet it.**

## 5. Effects say what a call may do

Two functions can both take `Unit` and return `Unit`, yet behave very differently. One might only calculate locally; another might write a file.

An **effect** describes an action that can be observed outside the local calculation. A callable's effect list limits which effects invoking it may contribute.

Here is an interface sketch, using effect names declared elsewhere:

```phil
callable EffectCarrier() -> Unit {
    effects {IO, Audit};
}
```

`effects` introduces that list. Think of it as a ceiling, not a to-do list. An implementation that only performs `Audit` may fit a contract allowing both `IO` and `Audit`. The contract does not permit an extra, undeclared effect.

Some effects also identify the particular resource they affect. In explanatory notation:

```text
Write(blob_store)
Write(log)
```

Writing the blob store and writing the log are different effects, even if both stores happen to use the same kind of machine handle.

Carrying a callable around does not perform its effects. Those effects belong to invoking it.

## 6. Permission is not the same thing as an effect

> **Phil asks: “What is each part allowed to do?”**

An effect declaration saying “this call may write the store” does not give the call permission to write it.

Phil keeps these questions separate:

| Question | Part of the contract |
| --- | --- |
| What observable actions might invocation perform? | **Effects**. |
| What permissions must be available for invocation to be legal? | **Authority**. |

Here is another interface sketch. The permission and effect names stand for contracts declared in the surrounding program:

```phil
callable StoreOperation() -> Unit {
    authority {StoreWrite};
    effects {WriteStore};
}
```

`authority` lists the authority the caller must make available. `effects` bounds what invocation may do. Neither list says that every listed permission or effect is exercised on every call.

This lets Phil check more than “our tests never saw a deletion.” A checked component with no access to delete authority cannot simply decide to acquire that permission. Passing it a callable also does not grant permission to invoke that callable without meeting its contract.

## 7. Protocols make conversations part of the program

> **Phil asks: “What may those parts say to each other?”**

Imagine a client that sends one byte to a server. A **protocol** is the rulebook for that conversation:

```phil
protocol Ping {
    role Client = send (x : U8) then end Done;
    role Server = receive (x : U8) then end Done;
}
```

Each `role` describes one participant's side. The Client sends a `U8`; the Server receives a `U8`. These are matching descriptions of the same exchange.

`then` introduces what comes next. `end Done` says that this side has reached its final state, named `Done`.

```text
Client: send one byte    → Done
Server: receive one byte → Done
```

Declaring the protocol does not send anything. In the declaration, `send` describes a legal step. Component code performs that step with `send ... on ...`.

A **session** is one particular conversation following a protocol. An **endpoint** is a value representing one participant's side of that session, including its current state.

```phil
component ClientWorker(endpoint : Client[Ping], payload : U8) {
    let done = send payload on endpoint;
    close done;
}
```

`Client[Ping]` describes the client-side endpoint type. This component needs both a live endpoint and the byte to send.

Read the body in two steps. First, `send payload on endpoint` sends the byte and consumes the old endpoint, producing the endpoint for the next state. `let done = ...` names that successor. Second, `close done;` consumes the terminal endpoint and closes that side of the session.

Both `send` and `close` are Phil keywords, not missing library functions. `close` requires an endpoint that has reached an `end` state; it cannot arbitrarily skip unfinished protocol steps.

This is a component declaration, **not yet a complete communicating program**. Something still has to supply its particular endpoint and payload. Assigning it to the Client role does not invent either value or insert a `send` into its body.

Two sessions using `Ping` remain two different conversations. An endpoint from one cannot replace a matching-looking endpoint from the other.

Also, permission to move a value locally is not automatically permission to send it as a message. Borrowed views, live endpoints, or authority-bearing values cannot gain that permission merely by being wrapped inside a record.

## 8. Architecture says which parts actually exist

> **Phil asks: “What parts does this system have?”**

A component declaration describes a reusable part. An **architecture** says which particular parts a system contains.

Here is a complete small Phase 1 source file:

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

The two `instance` declarations create two distinct uses of `Worker`, named `left` and `right`. We call each particular use an **occurrence**. Same definition, two occurrences.

The two `process` declarations activate those existing occurrences as members of the program's process network. They do not create another pair of workers.

Finally, `program main = instantiate Pair;` selects a fresh root occurrence of `Pair` as the program named `main`.

The declaration, its occurrences, and their activation are three different things:

```text
Worker definition → left occurrence  → left_run process
                  → right occurrence → right_run process
```

Even though the workers run identical code, the architecture still contains two workers. They do not merge just because they look alike.

## 9. Phil processes are not OS threads

A Phil **process** is one of the executing participants described by the architecture. It has its own identity, execution state, resources, and communication relationships.

An operating-system thread is a mechanism a computer might use to run it. They are not the same thing.

A target implementation might use one host thread per Phil process, or run several Phil processes on a shared event loop. An event loop takes turns handling work without requiring a separate thread for each participant. More elaborate implementations may split a process across target stages.

Those choices must preserve the Phil-level rules: who owns each resource, which communication is legal, which actions happen before others, and how the participants finish or fail.

> **The architecture identifies the participants. The implementation chooses how to run them.**

In Phase 1, the source process population is bounded and static: the architecture fixes it. `process` does not hide a source-level thread API or a command to create more processes while running.

## 10. Some protocol participants can be outside Phil

A Phil client may talk to a service implemented elsewhere. The architecture can mark that peer as `external`.

The following is a **role-assignment sketch** using the earlier declarations, not a fully supplied entry point:

```phil
architecture ExternalPeer {
    instance client = ClientWorker;
    process client_run = client;
    protocol ping = Ping;
    role ping.Client = client;
    role ping.Server = external;
}
```

Inside the architecture, `protocol ping = Ping;` creates one conversation occurrence named `ping` from the reusable `Ping` protocol. `role ping.Client = client;` assigns responsibility for its Client role to the `client` occurrence.

`role ping.Server = external;` says that the Server participant is outside the Phil process population.

It does not say how to contact that peer, select TCP, choose a message format, grant network authority, or guarantee the peer behaves correctly. Those need their own contracts. A missing internal participant does not silently become external either: the source has to say so.

Remember the remaining input requirement: `ClientWorker` needs its exact endpoint and payload. Role assignment does not supply them by itself. We will put these separate responsibilities side by side in section 18.

## 11. Providers make implementation replacement explicit

Suppose a system needs a storage service. Today it uses memory; tomorrow it may use a remote service. The rest of the system should depend on what the service promises, not on private details of one implementation.

Phil calls such an architectural implementation boundary a **provider**:

```phil
provider Store {}

provider implementation MemoryStore satisfies Store {}

opaque provider implementation RemoteStore satisfies Store;
```

These empty declarations show the forms, not a complete storage API. `provider Store {}` declares the public contract. `MemoryStore` supplies an implementation represented in Phil source.

`opaque` means the implementation's internals are not given as an ordinary Phil source body. For example, they might live in an external library. “Opaque” does not mean “automatically trusted.” Claims about those internals still need the appropriate evidence and explicit trust boundary.

In both forms, `satisfies Store` identifies the contract being claimed. The claim is not its own proof.

An implementation is **qualified** when it has met the requirements needed to stand behind that contract for the claims in question. Those may concern normal operation, permissions, ownership, failure, or behavior over several calls. Two services with the same operation names are not interchangeable unless the required rules match too.

> **Replacing an implementation must not quietly change the promises its callers rely on.**

## 12. Generic code must say what it needs

A **generic** declaration works with a type supplied later. It often names that type `T`.

But knowing only “this is a `T`” does not tell us whether it can be copied. It might turn out to be a number, or it might be a linear token.

Phil makes generic code state the extra permissions and facts it needs. This declaration sketch shows three kinds of requirement; `ProviderContract` stands for a provider contract declared elsewhere:

```phil
record Routed[T : Type] requires {
    structural T : duplicate;
    proposition true;
    provider P : ProviderContract;
} {
    value : T
}
```

`[T : Type]` means “accept a type parameter named `T`.” The final body declares a field of that type. `requires` lists prerequisites that must be met when a particular type and other arguments are supplied.

### `structural`: may this value be copied or discarded?

`structural T : duplicate;` requires permission to copy values of `T`. It does not give copying permission to a type that forbids it. Supplying a linear type therefore fails this requirement.

The two language-defined permission names are `duplicate` and `discard`. They are not reserved lexer keywords, but they have these specific meanings in a structural requirement:

| Actual mode of `T` | Satisfies `discard`? | Satisfies `duplicate`? |
| --- | --- | --- |
| unrestricted | Yes. | Yes. |
| affine | Yes. | No. |
| linear | No. | No. |

Here “structural” is the same word we met in ownership: it concerns copying and discarding, not the fields or memory layout of `T`.

Code that simply passes its `T` onward, without copying or dropping it, needs neither permission. Code that does copy it must not pretend otherwise in its public requirements.

### `proposition`: what fact must be accounted for?

A **proposition** is a statement that can be true or false. A proposition requirement asks for a logical fact, not a copy/drop permission.

`proposition true;` is deliberately trivial. It shows the syntax without adding another mathematical idea. A useful requirement would usually state something less automatic.

Writing `proposition P;` does not make `P` true. It also does not run an `if` test. The required fact must be accounted for when the generic is used: for example, by matching evidence. Where the selected policy permits an explicit assumption or an obligation passed onward, that choice must remain visible rather than masquerading as proof.

### `provider`: which service contract is required?

`provider P : ProviderContract;` names a required provider contract. It is a different prerequisite from either a logical fact or a structural permission.

The three lines ask three different questions:

```text
structural … : duplicate   Are values of this type allowed to be copied?
proposition …             Has this required fact been accounted for?
provider … : …            Is the required provider contract available?
```

Generic code gains no secret privileges from not yet knowing its arguments.

## 13. Phil can carry checked facts in types and contracts

> **Phil asks: “What must be true before the program can take the next step?”**

Sometimes “this is a number” is not enough. A calculation may need a number greater than zero.

```phil
claim Positive(x : U32) = x > 0;

callable KeepPositive(x : {v : U32 | v > 0}) -> U32 {
    ensures x > 0;
}
```

`claim` gives a reusable name to a proposition. Here `Positive(x)` names “`x` is greater than zero.” Naming the claim is not proving it.

The type `{v : U32 | v > 0}` is a **refinement type**. Read it as “a value `v` of type `U32`, such that `v > 0`.” The local name `v` is just a way to refer to the value while writing the condition.

`ensures` states a **postcondition**: a claim the contract promises at the relevant successful return. In this small example it refers to the input `x`; it does **not** say that the returned `U32` is positive. We have deliberately kept the example about one named value.

How does a claim become something the checker may rely on? Depending on the claim and the rules in force, Phil can use calculation within fixed limits, accepted evidence, a checked proof certificate, explicit runtime enforcement, or an explicit assumption.

A **proof certificate** is evidence that a checker can examine. An **assumption** is something the system relies on without establishing it itself. These must not be confused.

A runtime check can establish a condition on the path where it succeeds, but the failure path must also be handled. Merely asserting a condition does neither job.

The important boundary is simple: a claim is not automatically a fact, and a tool failing to prove a claim does not prove it false.

## 14. Bad Phil is rejected before assurance policy gets a vote

An **assurance policy** says how permitted outstanding claims may be handled. It does not rewrite the language's rules.

Copying a linear owner, sending at the wrong protocol step, or using authority that is not available are language errors. So is trying to pass a consumed resource into a later branch or loop state.

These errors cannot be relabeled “assumptions” to make the source valid.

After those language checks, some claims may legally remain to be resolved. Phil calls these **residual obligations**: requirements that still need an acceptable answer.

Depending on the obligation and policy, that answer may be a proof, runtime enforcement, an admitted assumption, or an explicit obligation passed to another boundary. Passing an obligation onward is not the same as proving it, and not every obligation permits every answer.

> **“Still needs evidence” and “not a valid Phil program” are different results.**

## 15. Source verification is not artifact certification

> **Phil asks: “What exactly do we know, why do we think we know it, and where does that claim stop?”**

Suppose the source follows Phil's rules and its application-level obligations have been handled. Why is that not the end?

Because the program still has to be turned into a particular executable artifact. That introduces choices: which provider implementation to use, how values are stored, and how processes are run. Those choices must not break the source's rules.

**Source verification** checks the source and records the basis for its claims. A **VerificationBundle** is the inspectable record: which exact source was checked, which obligations it had, and which evidence, dependencies, and policy were used.

**Artifact certification** concerns a particular compiled result and its implementation choices. It must account for how those choices preserve the required facts, including any new requirements they introduce.

An **AssuranceManifest** records the claims and justifications for that artifact, including what still has to be trusted. It is not a blanket statement that every imaginable property has been proved.

For example, a source-level storage contract might be sound, but the selected storage implementation must still meet it. Proof about the source does not automatically prove every possible implementation choice safe.

## 16. Lowering may choose representation, not meaning

**Lowering** translates a program into a form closer to its eventual execution. A compiler may perform several such steps.

It might replace a general function with a specialized one, choose a qualified provider, or map several Phil processes onto an event loop. Different correct implementations need not look alike.

Phil treats each such change as a checked **refinement**: the more concrete implementation must still meet the relevant rules of the less concrete one.

> **Lowering may choose representation; it may not choose semantics.**

“Semantics” means the program's meaning: the behavior and guarantees its contracts describe.

For example, putting two Phil processes on one thread must not merge their resource ownership or allow messages to be swapped between their sessions. Their machine representation changed; their responsibilities did not.

A fact need not remain as a literal annotation in machine code. It may be preserved by the chosen mechanism, justified by evidence, or enforced at runtime. Where a policy allows an obligation to be passed onward, that must be recorded. Later choices may also introduce stricter requirements.

What cannot happen is silently forgetting a source requirement because a later stage finds it inconvenient.

## 17. Why stable identity appears at all

Recall the two workers:

```phil
architecture Pair {
    instance left = Worker;
    instance right = Worker;
    process left_run = left;
    process right_run = right;
}
```

They have the same type and code but are different occurrences. Evidence about one is not automatically evidence about the other.

There is a second identity problem when source changes. Renaming a process should not necessarily turn it into an unrelated process. Yet reusing an old name should not accidentally reuse evidence about a different object.

Phil therefore tracks **lineage**: identity carried deliberately across revisions, rather than guessed from a file path, display name, or position in the source.

A declaration can carry an explicit key:

```phil
@key("decl:upload-id")
record UploadId {}
```

`@key(...)` is an attribute, extra information attached to the declaration. The quoted string carries its stable declaration identity. `key` is the language-defined attribute name, not a reserved lexer keyword.

The key is not evidence that the declaration is correct. Keeping identity across an edit also does not make old proofs automatically valid for the new body: the exact revision and its dependencies still matter.

Other occurrence identities can travel with the source in a **SourceBundle**. Beginners need not manually manage every such detail to understand ordinary code. The purpose is to let the tools agree on exactly which declaration, resource, process, or session a claim concerns.

> **Looking the same is not the same as being the same.**

## 18. How the Ping pieces fit

> **Phil asks: “Where does every running input actually come from?”**

The earlier Ping fragments can now be put together as one ordinary source path. This is the complete source wiring for an internal, one-shot Ping:

```phil
protocol Ping {
    role Client = send (x : U8) then end Done;
    role Server = receive (x : U8) then end Done;
}

component ClientWorker(endpoint : Client[Ping], payload : U8) {
    let done = send payload on endpoint;
    close done;
}

component ServerWorker(endpoint : Server[Ping]) {
    let (done, received) = receive U8 on endpoint;
    close done;
}

architecture LocalPing {
    instance client = ClientWorker;
    instance server = ServerWorker;
    process client_run = client;
    process server_run = server;
    protocol ping = Ping;
    role ping.Client = client;
    role ping.Server = server;
    entry payload : U8;
    bind client.endpoint = ping.Client;
    bind client.payload = payload;
    bind server.endpoint = ping.Server;
}

program main = instantiate LocalPing;
```

There are five different jobs here, and none of them secretly performs another one's job:

```text
Protocol      What conversation is legal?
Components    What code performs each side?
Architecture  Which exact occurrences and roles participate?
Entry/binds   Where do the running component inputs come from?
Program       Which architecture occurrence is the root program?
```

`protocol ping = Ping;` creates one particular Ping conversation. The two `role` lines assign its two sides to the two component occurrences. That still does not pass values into either component.

The `bind` lines do that wiring explicitly. `bind client.endpoint = ping.Client;` supplies the Client endpoint projected from this exact `ping` occurrence. `bind server.endpoint = ping.Server;` supplies the matching Server endpoint. `bind client.payload = payload;` supplies the client's byte from the architecture entry named `payload`.

An **entry** is a value supplied to the running architecture from its surrounding realization. `entry payload : U8;` therefore declares a runtime input; it does not quietly choose a constant. If the surrounding run supplies the value 42 for that exact entry, the checked path is:

```text
entry payload = 42
        |
        v
client.payload
        |
        | send on this exact ping.Client endpoint
        v
matching receive on this exact ping.Server endpoint
        |
        v
server local name received = 42
```

The byte and the endpoints obey different ownership rules. A `U8` is unrestricted, so carrying the same byte value through the send/receive does not require pretending that a unique owner moved from client to server. Session endpoints are linear: the send and receive consume their predecessor endpoints and produce exact successor endpoints. Both workers name those successors `done`, and `close done;` consumes the terminal endpoint on each side.

That distinction is useful. Phil checks both **which value participated in the message** and **which exact session occurrence advanced**. Matching types or matching source spellings are not enough to substitute some other entry or some other Ping session.

The Phase 1 integration corpus exercises this whole internal path: ordinary source is parsed, the architecture bind edges are resolved, both component occurrences are activated, a concrete root-entry byte participates in the matching send/receive, both endpoint successors close, and the process network reaches terminal closure.

The external-peer sketch from section 10 is still a different case. Marking `ping.Server = external` identifies responsibility outside the Phil process population, but it does not by itself choose TCP, a wire encoding, network authority, or a transport adapter. Those remain explicit realization boundaries rather than hidden behavior of role assignment.

## 19. Where the bigger examples fit

The small examples teach vocabulary. Two larger programs put the ideas together in different ways.

The **framed upload** is the historical Phase 0 example. It checks a multi-step client/server conversation, recognizes incoming frames before accepting them, validates data, transfers ownership, and handles failures. The [Phase 0 Tour](tour-phase0.md) follows that one system in detail, including its compilation and certification path. It uses the Phase 0 vocabulary, not interchangeable Phase 1 source syntax.

**Steve** is a content-addressed store: it names stored data using a digest computed from the data's contents. It makes Phil confront a different set of problems, such as matching evidence to the exact stored object, limiting storage permissions, and handling failed writes.

The compiler should not know either program by name. They should be ordinary programs that use the same language rules.

Readers who already know Phase 0 can instead follow [From Phil Phase 0 to Phase 1](from-phase0-to-phase1.md). For an unfamiliar reserved word, keep the [keyword lexicon](../reference/keywords-phase1.md) nearby.

## 20. The ideas to keep

You do not need to memorize every keyword from this tour. Keep asking the questions we started with:

- **What parts does this system have?** Components describe reusable parts. Architectures identify the particular participants and their responsibilities. Their real inputs still have to be supplied.
- **What may those parts say to each other?** Protocols describe the allowed conversations, including what may happen next. Components perform the actual communication.
- **What is each part allowed to do?** Contracts limit actions and state the permissions a call needs. Ownership rules say whether a value may be copied, discarded, or transferred.
- **What must be true before the program can take the next step?** Contracts make requirements explicit. A claim, a proof, a runtime check, and an assumption are different things; naming a claim does not prove it.
- **What happens when something goes wrong?** Contracts distinguish ordinary success, recoverable `negative` outcomes, normal `terminal` completion, declared `fatal` completion, and explicit term-level `fail`. Each path keeps its own exact control meaning and must still obey the rules for its resources, permissions, and conversations.

Those answers must still hold when the implementation changes. Evidence applies to particular objects and requirements, not to everything that looks similar. Checking the source and justifying a particular compiled artifact are connected but separate jobs.

That is the idea behind Phil's slogan:

> **Architecture executable, implementation replaceable.**
