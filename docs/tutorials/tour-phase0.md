# A Tour of Phil

## Building a safe upload conversation

*Phase 0 edition. This tutorial describes the frozen Phase 0 reference program. Later Phil versions may generalize or change parts of the surface language, but this document intentionally records what Phase 0 actually established.*

Phil is a programming language for building systems from the outside in. Instead of starting with “what instructions should the computer run?”, Phil starts with questions like:

- What parts does this system have?
- What may those parts say to each other?
- What is each part allowed to do?
- What must be true before the program can take the next step?
- What happens when something goes wrong?

This tour follows one small program all the way through: a client uploads some bytes to a server.

You do not need to know formal logic, compiler theory, or computer security jargon. We will give technical ideas names only after we have a reason to need them.

The code snippets are real frozen Phase 0 `.phil` syntax, shortened in a few places by leaving out surrounding branches.

## 1. Start with the conversation

Imagine two parts of a program:

- **Client** — has something to upload.
- **Server** — receives it.

The place where information passes from one part to another is a **boundary**. Boundaries matter because each side may know different things, trust different things, or have different permissions.

Before we write the details of either side, we can describe the allowed conversation:

1. Client → Server: `Hello`, listing the versions the client can speak.
2. Server → Client: select one of those versions, or select `unsupported`.
3. If a version was selected, Client → Server: `Begin`, describing the upload.
4. After checking `Begin`, Server → Client: select `proceed`, or reject it.
5. If the server selected `proceed`, Client → Server: select `payload` or `cancel`.
6. If `payload` was selected, the bytes are sent; Server → Client then selects `accepted` or `rejected`.

Those rules are a **protocol**.

A protocol says who may send what, when, and what can happen next. It is the rulebook for a conversation.

One actual conversation following that rulebook is a **session**.

Each side of a session has an **endpoint**: a handle that represents where that side currently is in the conversation.

That gives us our first important Phil idea: the conversation itself is part of the program. It is not just a comment beside the program.

## 2. The client says hello

Here is the beginning of the real Phase 0 client:

```phil
component UploadClient provides Client[Upload] {
    let versions = supported_versions()
    prove len(versions) > 0

    let hello = construct Hello {
        versions = versions
    }
    let session1 = send hello on session0

    ...
}
```

A **component** is one part of a Phil system. Here the component is called `UploadClient`.

The client first gets the versions it knows how to speak. Then this line appears:

```phil
prove len(versions) > 0
```

Phil is not asking the computer to print `true`. It is asking for a fact the rest of the program can rely on: there is at least one version to offer.

Next the client constructs a `Hello` message and sends it.

Notice the names `session0` and `session1`. Sending the message moves the conversation forward. The program gets a new endpoint for the new state of the session.

This becomes important on the server side.

## 3. Receiving bytes is not the same as receiving a message

Suppose the server expects a `Hello`.

A normal program might read some bytes, parse them, and then continue. Phil is more careful because “some bytes arrived” and “we successfully received a valid `Hello` message” are not the same fact.

The server begins like this:

```phil
let pendingHello = receive_frame(session0)
    or fail transport

let helloRecognition = borrow pendingHello as rawHello {
    recognize Hello from rawHello
}
```

The first line receives a **frame**.

A frame is one complete chunk of bytes that is supposed to contain one message.

But Phil does not move the session forward yet. The result is called `pendingHello`: the receive is still pending.

Why? Because the bytes have not yet been shown to be a `Hello`.

A **grammar** is a set of rules describing which byte sequences count as a particular kind of message. **Recognition** is the act of checking a complete frame against those rules.

For example, the `Hello` grammar says what fields must be present and how they are encoded. If the bytes are truncated, contain an invalid tag, or have extra trailing bytes, recognition fails.

Only the successful branch can continue:

```phil
decide helloRecognition {
    rejected(reason) => {
        fail recognition(reason) on pendingHello
    }

    accepted(parsedHello) => {
        let hello = parsedHello.value
        let session1 = commit_receive pendingHello using parsedHello
        ...
    }
}
```

`parsedHello` is **evidence** that these exact bytes were recognized as a `Hello`.

Evidence is something Phil can use to remember that a required fact has been established.

`commit_receive` uses that evidence to finish the receive and produce `session1`, the endpoint for the next step of the protocol.

This separation is deliberate:

```text
bytes arrived
→ the receive is pending
→ recognize the whole message
→ commit the receive
→ now the conversation may move on
```

A malformed message never produces the endpoint for the next protocol step.

## 4. Well-formed does not mean acceptable

Now suppose the `Begin` message is perfectly well formed.

It says the client wants to upload a 40-gigabyte object.

The bytes may match the grammar exactly, but the server may still have a rule saying “uploads may be at most 10 megabytes.”

That is a different question.

**Recognition** asks:

> Do these bytes form the kind of message we expected?

**Validation** asks:

> Does this already-recognized value satisfy an extra rule we care about here?

The Phase 0 server does both. After recognizing `Begin`, it does this:

```phil
decide validate BeginPolicy at policyContext on begin {
    rejected(reason) => {
        let session4 = select reject(reason) on session3
        close failure
    }

    accepted(beginPolicy) => {
        let session4 = select proceed on session3
            using beginPolicy
        ...
    }
}
```

`BeginPolicy` is a rule about things such as maximum payload size, allowed kinds of upload, and allowed digest algorithms.

If validation succeeds, the program receives `beginPolicy`: evidence that this particular `begin` value passed this particular policy check.

The server needs that evidence before it may select `proceed`.

This is a recurring Phil pattern:

```text
do the check
→ get evidence
→ use the evidence at the step that requires it
```

The checked value is still the same value. Validation does not secretly rewrite or “clean up” the message.

## 5. The protocol controls what can happen next

After the server selects `proceed`, the protocol says the client has two choices:

- `payload` — send the bytes.
- `cancel` — stop the upload.

The server therefore has to handle both:

```phil
offer session4 {
    payload => {
        ...
    }

    cancel => {
        close cancelled
    }
}
```

An **offer** means “the other side gets to choose one of these allowed paths, and I am ready for every allowed choice.”

Each allowed path is often called a **branch**.

Phil checks that the program handles every branch the protocol says the other side may choose. It also checks that the program does not invent a branch that is not in the protocol.

There is another important rule here. When a session takes a step, the old endpoint is finished. The next step uses the new endpoint.

That one-use rule is called **linear use**.

You do not need the mathematical theory behind linear logic to understand the programming rule:

> A live session endpoint cannot be copied, forgotten, or reused after the conversation has moved on.

That prevents bugs where two pieces of code both think they control the same conversation, or where code accidentally jumps backward to an old protocol state.

## 6. Ownership answers “who is responsible for this thing?”

The uploaded payload is also treated carefully.

The client **owns** its payload. Ownership means the program is responsible for that value and must eventually do something valid with it: transfer it, return it, or release it.

Sometimes code needs to look at owned data without giving it away. Phil calls that a **borrow**.

The client computes the payload’s SHA-256 digest like this:

```phil
let declaredDigest = borrow payload as payloadView {
    sha256(payloadView)
}
```

Inside the borrow, `payloadView` can be used to read the bytes. The client still owns `payload`.

When the borrow ends, the temporary view is gone, but ownership of the payload remains.

Later the client either sends the payload:

```phil
let session4 = send_exact payload on session3
```

or releases it on a path where it will not be sent:

```phil
release payload
```

Phil keeps track of this across the different branches.

That means “we forgot to clean up the payload when the user cancelled” is not merely a code-review suggestion. It can be a rejected program.

## 7. Phil also checks what you are not allowed to do

A language is partly defined by the programs it refuses to accept.

Here is a real rejected Phase 0 example:

```phil
component BadOrder {
    send Accepted(id) on s0
}
```

This is rejected because the current protocol state requires receiving `Hello`. The program is trying to send the final answer before the conversation has even begun.

Another rejected example is more subtle. Imagine the server receives the payload and stores it successfully, then immediately says `accepted`.

That is still wrong.

The protocol requires the server to establish that the payload matches the digest declared in `Begin`. Storage success does not prove that.

The rejected example looks like this:

```phil
decide store(payload) {
    failure(err) => fail internal(err) on s1
    success(id) => {
        select accepted(id) on s1
    }
}
```

The missing piece is digest evidence.

The correct program validates the digest first. Only the successful validation branch receives evidence that the bytes match, and that evidence is required when the server selects `accepted`.

Phil is not trying to guess that the programmer “probably meant” to check the digest. If the architecture says the evidence is required, the program must actually have it.

## 8. The implementation cannot invent new authority

**Authority** means permission to make something happen.

One of the most useful Phase 0 examples appears when storage fails.

The upload protocol has ordinary peer-visible messages for success and digest rejection. But storage failure is different: in the frozen source, it is a local terminal failure on the server. There is no normal protocol message that says “storage failed.”

When the final native demonstrator was built, it would have been convenient to invent such a message so both sides could finish neatly.

Phil does not allow convenience to silently change the architecture.

The demonstrator leaves storage failure locally terminal because that is what the source program says.

This is a small but important example of the phrase:

> **architecture is executable**

The architecture is not a diagram that the implementation may politely ignore. It limits the behavior the implementation is allowed to have.

## 9. From Phil source to a native program

So far we have mostly looked at the source language. Phase 0 also takes this exact reference program all the way to native code.

The path looks roughly like this:

```text
client.phil + server.phil
→ parse and check the Phil source
→ build a more explicit systems representation
→ check that representation
→ translate it to LLVM
→ link it with the runtime pieces
→ build a native executable
→ run it
```

A **systems representation** is a lower-level description where details needed for execution — resources, runtime operations, and other implementation decisions — are made explicit.

LLVM is a lower-level program format used by widely available compiler tools.

Turning a higher-level program into progressively lower-level forms is called **lowering**.

The important part is not the vocabulary. The important part is that Phil keeps checking the meaning as the program moves from one form to the next.

The frozen Phase 0 native executable runs three complete paths:

- **Accepted upload** — the payload is transferred exactly, its SHA-256 digest is checked, it is stored, and the client receives the same upload ID the server produced.
- **Digest rejection** — the bytes are transferred, the digest check fails, the payload is released, storage is not called, and the upload is rejected.
- **Cancellation** — negotiation succeeds, the client cancels, and no payload transfer or storage happens.

These are not simulations of the source program. They run the compiled `UploadClient` and `UploadServer` together as native code.

## 10. What does “certified” mean here?

Phil uses the word **obligation** for a requirement that must be dealt with before a particular claim can be accepted.

Different obligations can be handled in different ways.

Some facts can be proved before the program runs.

Some facts have to be checked while the program is running because they depend on runtime data.

Some facts still depend on trusted tools or outside assumptions.

Phil tries hard not to blur those together.

A **proof** is evidence established ahead of time by an accepted proof process.

A **runtime check** is a check that happens during execution and produces evidence only if it succeeds.

A **certificate** is a content-bound record of exactly what was checked, what evidence was accepted, and what exact artifacts the claim applies to. You can think of it as a very picky receipt.

At the end of Phase 0, the reference upload program has a closure certificate that combines two different kinds of support:

- the proof-backed path from the frozen source through the checked compiler stages; and
- the separately checked evidence that the exact native reference executable matched its runtime interface and completed the three expected scenarios.

The certificate does not mean “everything about this program is mathematically proven.”

It is much narrower and more useful than that.

For example, Phase 0 still relies on things such as the correctness of the LLVM and C toolchain, the operating system’s thread behavior, the C library and allocator, and the OpenSSL SHA-256 implementation used by the native fixture. It does not claim production networking, crash-proof storage, or a general Phil runtime.

Phil’s assurance story is meant to answer:

> **What exactly do we know, why do we think we know it, and where does that claim stop?**

## 11. Try the repository

The current command-line interface is still a bootstrap tool, so this is not yet the polished installation experience we want for later Phil releases.

You can build and test the Haskell implementation with:

```sh
cabal build all
cabal test all
```

You can also ask the bootstrap tool to parse the frozen client:

```sh
cabal run phil-core -- parse examples/upload/client.phil
```

If that succeeds, it means the file is syntactically valid Phil and source locations were recovered.

It does not mean the whole program has passed Phil’s semantic checks. The tool says this explicitly because parsing and proving that a program is acceptable are different jobs.

The repository also contains the complete checked, lowered, native, and certified Phase 0 reference path, but the friendly one-command user interface for that path belongs to later work.

## 12. Where Phase 0 stops

Phase 0 answers an important question:

> Can one nontrivial architecture be expressed precisely enough that its protocol, resources, checks, failures, lowering steps, native execution, and assurance story all agree?

For the frozen upload reference program, the answer is yes.

But Phase 0 does not yet claim that any arbitrary `.phil` program can travel through the same completely generic path.

Some of the source-to-systems work is deliberately specific to this reference architecture.

That is the next problem.

A useful short version is:

> **Phase 0: one architecture works.**  
> **Phase 1: the language works for architectures.**

Phase 1 generalizes the machinery that Phase 0 proved out. It also gives us room for very different programs — including Steve, a content-addressed store, and a Phil implementation of SHA-256 — to exercise the same language without special cases.

## 13. The ideas to keep

If you remember only a few things from this tour, remember these:

- A **boundary** is where information or control crosses from one part of a system to another.
- A **protocol** is the rulebook for a conversation.
- A **session** is one live conversation following a protocol.
- An **endpoint** is one side’s handle for its current place in that conversation.
- **Recognition** checks that received bytes really form the expected kind of message.
- **Validation** checks an extra rule about a value that has already been recognized.
- **Evidence** is something Phil can use to remember that a required fact has been established.
- **Ownership** says who is responsible for a value. A **borrow** lets code look at owned data temporarily without taking ownership away.
- An **obligation** is a requirement that must be dealt with before a claim can be accepted.
- **Authority** is permission to make something happen. Implementations do not get to invent authority merely because doing so would be convenient.

And the big idea behind all of them is this:

> **Phil is a systems language in which architecture is executable and implementation is replaceable.**

The architecture is part of the program.
