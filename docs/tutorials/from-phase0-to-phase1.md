# From Phil Phase 0 to Phase 1

## How one verified architecture became a general systems language

This document is for readers who already know the basic Phil vocabulary, especially the ideas introduced by the [Phase 0 framed-upload tour](tour-phase0.md): components, protocols and sessions, evidence, ownership, lowering, and certification.

If Phil is new to you, start with the current [A Tour of Phil](tour-phase1.md). That tour introduces the language from small source programs upward. This document answers a different question:

> **What had to change between Phase 0 and Phase 1 so that Phil stopped being the semantics of one demonstrator and became a language for architectures in general?**

The short version is:

> **Phase 0 — Establish: one architecture works.**  
> **Phase 1 — Generalize: no privileged program.**

Phase 0 proved the idea locally. Phase 1 removes the special cases.

## 1. The upload program stops being privileged

Phase 0 followed one architecture all the way from source through native execution and certification: the framed upload.

That was useful, but a first implementation can accidentally hide parts of the example inside the compiler. A rule that amounts to this is not yet a general language rule:

```text
if this is the upload program,
    create these components,
    install this provider,
    connect these protocol roles,
    and lower them this way
```

Phase 1 requires the upload program to enter through the same ordinary source and semantic machinery as a substantially different program.

The second pressure case is **Steve**, a small content-addressed store. Steve cares about digest identity, install-if-absent behavior, provider qualification, storage authority, and object lifecycle rather than the upload protocol's recognition and framing story.

That difference is the test. If upload and Steve can both travel through the same parser, elaborator, architecture machinery, verification boundary, Systems lowering, and assurance model, then those mechanisms describe Phil rather than either witness.

A root is therefore an ordinary source declaration:

```phil
program main = instantiate pkg.Arch {
  entry ingress : U32;
  assume true within trust.zone;
  export obligation proof.ready to audit.sink;
  observable metrics.bytes;
};
```

Nothing in that form says “upload” or “Steve.” The program selects an architecture and names its own source-visible boundary facts.

## 2. Architecture identity becomes explicit

Once architectures are reusable, names and machine representations stop being good enough as identity.

Two provider operations may lower to the same target symbol without becoming the same operation. Two architecture occurrences may have identical structure without becoming the same occurrence. Two equal byte strings may inhabit different ownership positions without their owners becoming interchangeable.

Phase 1 therefore separates:

```text
semantic identity
from
representation identity
```

It also separates stable lineage from the current checked revision:

```text
stable lineage identity
≠
current source spelling/location
≠
checked interface/definition/instance revision
```

A top-level declaration can carry stable lineage explicitly:

```phil
@key("decl:upload-id")
record UploadId {}
```

Architecture-instance and process-occurrence lineage is carried with the **SourceBundle** rather than reconstructed from a file path, source offset, pointer, or Haskell object identity.

That means an intentional rename or move can preserve lineage, while copying a genuinely new occurrence normally creates fresh identity.

This is one of the major Phase 1 changes that Phase 0 did not need to expose as strongly: once the same declaration can be instantiated, copied, refined, and independently realized, identity has to survive all of those operations deliberately.

## 3. Generic code receives no secret structural privileges

Phase 0 already had unrestricted, affine, and linear ownership behavior. Phase 1 has to preserve those rules through abstraction.

For an abstract value `T`:

- transferring it from input to output requires no copy/drop permission;
- discarding it requires weakening permission;
- duplicating it requires contraction permission.

The important rule is:

> **Generic code may rely only on the permissions and facts its contract actually provides.**

Grammar v1 can state such requirements explicitly:

```phil
record Routed[T : Type] requires {
  structural T : duplicate;
  proposition true;
  provider P : ProviderContract;
} {
  value : T
}
```

`structural T : duplicate;` is a requirement on an exact resolved generic parameter. It does not grant duplication merely because the source contains the word `duplicate`.

This avoids turning generic abstraction into an ownership-laundering mechanism.

## 4. Ownership survives closures, aggregates, joins, and loops

The same principle applies to compound values and control flow.

A closure that owns a linear capture is not freely duplicable. A record that owns a linear field does not become unrestricted because the field is hidden behind a record name. A loop carrying a linear owner must account for it at every backedge. Continuing branches have to agree about the resources that exist after reconvergence.

Phase 1 also makes intentionally stricter possession modes source-visible when the semantic contract calls for them:

```phil
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

The broad rule is unchanged from Phase 0 but applied much more generally:

> **Abstraction may hide representation. It may not hide ownership.**

## 5. Callables become semantic values

Phase 0 had functions and checked transitions, but Phase 1 needs first-class callable contracts that survive higher-order use and implementation replacement.

A callable contract may describe independently:

- parameter and result types;
- consumed and borrowed resources;
- required authority;
- possible effects;
- success, negative, terminal, and fatal outcomes;
- postconditions;
- residual obligations;
- assumptions;
- costs;
- callee-state transitions.

For example:

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
  ensures true;
  obligation true;
  cost 7;
  callee preserve;
}
```

A replacement callable is not judged merely by ABI shape. It must refine the semantic boundary the caller is prepared for.

An implementation may require less authority or perform fewer effects than its public contract permits. It may not silently demand new authority, widen the effect set, introduce a new fatal outcome, or change resource residue merely because the machine signature still matches.

## 6. Effects and authority become separate dimensions

Phase 1 makes a distinction that is easy to lose in conventional APIs:

```text
may perform Write(store)
≠
has authority to write store
```

Effects are may-effect upper bounds. Authority says what the context permits.

Possessing a callable whose invocation may write storage is not itself a write. Passing that callable, storing it, or returning it keeps the effect latent. A reachable invocation contributes the effect.

Similarly, possessing a capability does not imply that its permitted operation occurred.

This separation supports both positive and negative security claims. “This component did not happen to delete anything in our test” is weaker than “this component has no checked path to delete authority.” Phil aims for the latter kind of statement when that is the claim being made.

## 7. Protocols become reusable families with exact instances

Phase 0 had one important protocol. Phase 1 makes protocols ordinary reusable language objects.

A protocol family describes a conversation shape. Each actual use creates an exact protocol instance. Runtime endpoints are indexed by the exact instance, role, and current session state.

That means two simultaneous conversations following the same family are still different sessions. An endpoint from session A cannot be substituted for the corresponding endpoint from session B merely because the visible local state happens to look the same.

Phase 1 also separates “movable value” from “legal protocol message.” Message admissibility is its own boundary. A live endpoint, scoped loan, or authority-bearing occurrence cannot be hidden inside an aggregate to acquire remote-transfer semantics that Phil never granted.

## 8. Processes become architectural; threads remain realizations

Phase 1 introduces a bounded static process model: the architecture declares a finite Phil process network.

A process occurrence has stable semantic identity. It is not an OS process, thread, task, coroutine, event-loop callback, or GPU lane.

The source form is deliberately small:

```phil
process worker_run = worker;
```

The right-hand side refers to an already-created executable architecture occurrence. The process declaration activates that occurrence in the Phil process population; it does not clone or instantiate it.

An implementation may map Phil processes onto threads or other runtime mechanisms in different ways, provided the checked realization preserves process identity, ownership, causality, communication, failure, and terminal behavior.

So the governing distinction is:

> **Process identity belongs to the architecture. Thread identity belongs to the realization.**

Internal communication is synchronous rendezvous over exact dual endpoints. Fairness, deadlock freedom, eventual response, and scheduling policy are not silently granted by the concurrency model; they can become explicit obligations when needed.

## 9. External participants stop being inferred

Not every protocol participant has to be a Phil process. Phase 1 therefore makes externality explicit:

```phil
role ping.Client = client;
role ping.Server = external;
```

`external` means only that the role lies outside the Phil process population.

It does not choose a transport, representation, entry resource, authority source, assumption, deployment relation, or realization mechanism.

Conversely, an unresolved or inactive internal target does not silently become external. Missing classification is an error.

Failure remains local too. If an external peer disappears, the internal process does not magically become successfully terminal; it remains live or stuck until an explicit Phil failure/disposition path closes its own resource and obligation boundary.

## 10. Providers become replaceable contracts

Phase 0 used concrete system services. Phase 1 turns those implementation boundaries into ordinary provider contracts with qualification.

Source can declare the contract and candidate implementations:

```phil
provider Store {}
provider implementation MemoryStore satisfies Store {}
opaque provider implementation RemoteStore satisfies Store;
```

But `satisfies` is a claim about which contract an implementation intends to realize. It is not self-issued qualification evidence.

Qualification may depend on operation contracts, authority confinement, state simulation, lifecycle behavior, history-wide laws, tests, proofs, assumptions, or other accepted evidence.

This enables a small-scale version of Phil's central promise:

> **Architecture executable, implementation replaceable.**

The same architecture instance can admit materially different qualified provider realizations without changing its architectural identity.

## 11. Ordinary execution stops inheriting host accidents

Phase 1 also needs ordinary programming constructs to have Phil semantics rather than “whatever Haskell/LLVM happened to do.”

The language therefore fixes properties such as:

- strict sequential statement order;
- left-to-right strict expression and argument evaluation;
- lexical initialized bindings;
- explicit no-active-shadowing rules;
- exact-width `UInt` arithmetic rather than silent target wrapping;
- explicit checked handling of runtime-contingent overflow;
- explicit treatment of target partiality such as traps, UB, OOM, gas exhaustion, or device-capacity failure.

A realization cannot turn valid Phil behavior into undeclared target failure merely because a convenient backend operation is partial.

Likewise, dropping an affine value is just structural weakening. It does not secretly call `free`, `close`, flush, a finalizer, or some provider operation. Effectful cleanup remains an explicit semantic transition.

## 12. Source verification becomes distinct from artifact certification

Phase 0 already cared about evidence and certification. Phase 1 makes the programmer-facing boundary more explicit.

First, the source must be intrinsically valid Phil. Errors such as these are not residual proof obligations:

- duplicating a linear owner;
- taking an illegal session transition;
- using authority that is absent;
- assigning one restricted occurrence to two processes;
- failing a required resource-state join.

A permissive assurance policy cannot convert those language errors into assumptions or runtime checks.

Only claims that Phil permits to remain live become residual obligations.

For accepted source, application verification constructs a **VerificationBundle** recording the exact source revisions, obligations, dependencies, policy, and evidence references.

That still does not certify a particular executable artifact.

A realization introduces another boundary: provider choices, Systems representation, process mappings, StageContract preservation, target-specific strengthenings, runtime carriers, deployment requirements, and target-derived obligations.

So Phase 1 makes the separation explicit:

```text
source verification
≠
artifact certification
```

Final certification composes both sides and produces a scoped assurance manifest.

## 13. Lowering remains refinement, not authority

The backend is allowed to choose representation and mechanism. It is not allowed to choose new source semantics.

A target may inline, specialize, stage bytes through a buffer, map multiple Phil processes onto one worker, choose a qualified provider, or use a runtime enforcement mechanism.

Every live semantic fact still needs an explicit fate. It can be preserved, realized, discharged, enforced, exported, strengthened with a new obligation, or carried as an admitted assumption dependency.

It cannot simply disappear because the target IR no longer has a convenient field for it.

The concise rule remains:

> **Lowering may choose representation; it may not choose semantics.**

## 14. The two Phase 1 witnesses should look unlike each other

The framed upload remains the compatibility witness. It pressures:

- protocol progression;
- recognition before receive commit;
- policy and digest evidence;
- ownership transfer;
- branch-sensitive failure;
- bounded authority;
- assurance lineage.

Steve pressures a different set of abstractions:

- content-derived identity;
- exact evidence subjects;
- install-if-absent behavior;
- provider qualification;
- authority confinement;
- object lifecycle and storage failure.

If both are merely ordinary Phil programs crossing the same generic machinery, the differences between them become evidence that Phase 1's abstractions are real.

The compiler should not know either witness by name.

## 15. Where Phase 1 stops

Phase 1 removes the privileged program, not every privileged choice in the system.

It can still use one conventional compiler/checker implementation and one conventional host/backend profile. It does not require an independently written second Phil implementation, materially different machine targets, dynamic process creation, asynchronous mailboxes, shared-memory atomics as source semantics, a package ecosystem, or mature IDE tooling.

Those are later pressures:

```text
Phase 0 — Establish: one architecture works.
Phase 1 — Generalize: no privileged program.
Phase 2 — Replace: no privileged implementation.
Phase 3 — Retarget: no privileged machine model.
Phase 4 — Compose: no privileged monolith.
Phase 5 — Deploy: no privileged laboratory.
```

Phase 1 is done when upload and Steve are not special compiler-known objects. They are ordinary programs whose meaning is precise enough to hand to an independent Phase 2 implementation.

## The Phase 1 differences worth remembering

- Architecture comes from ordinary source and checked contracts, not witness recognition.
- Stable semantic lineage is explicit and survives representation changes.
- Generic code gets no hidden Copy/Drop privileges.
- Ownership survives abstraction, closures, data, branches, loops, and processes.
- Callables carry semantic contracts, not merely machine signatures.
- Effects, authority, contextual requirements, outcomes, and obligations remain separate dimensions.
- Protocol families are reusable while individual sessions remain exact.
- Phil processes are architecture; threads and schedulers are realization.
- External participation is explicit rather than inferred from missing bindings.
- Providers are qualified against contracts rather than trusted because they link.
- Ordinary evaluation and arithmetic have Phil semantics rather than host semantics.
- Intrinsic language errors are not assurance-policy choices.
- Source verification is not artifact certification.
- Lowering may choose mechanisms and representation, but not source meaning.

That is the conceptual transition from Phase 0 to Phase 1: **the rules that once made one carefully constructed system work become the ordinary rules of the language.**
