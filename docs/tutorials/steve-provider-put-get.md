# Steve provider put/get walkthrough

This tutorial follows one object through Steve in both directions: first into the
content-addressed store, then back out again.

It is the human-facing walkthrough for the current `INT-006` Steve provider
slice. The canonical Phil source is checked in under `examples/steve/`, and the
provider semantics are exercised by the existing Haskell conformance and native
bridge harnesses. This tutorial does **not** claim that the later public package,
trust/toolchain disclosure, or outside-implementor smoke-test slices are already
complete.

## What Steve is checking

Steve is a small content-addressed store. Its content ID is the SHA-256 digest of
the stored bytes. The useful round trip is therefore:

1. start with bytes `B`;
2. compute `id = SHA256(B)`;
3. install `B` under `id` without replacing an existing object;
4. read the object named by `id`;
5. accept the returned bytes only if their digest is still `id`.

The important Phil point is that this behavior is not defined by one privileged
implementation. The source names provider operations, and a concrete provider
may replace another only after satisfying the checked provider obligations.
Steve currently depends on `DigestProvider[SHA256]` and `BlobProvider`; their
qualification surface is documented in
[`../phase-1/steve-provider-qualifications-v1.md`](../phase-1/steve-provider-qualifications-v1.md).

## The four canonical source files

The application shell is split into two command-facing components and two
callable components:

- [`../../examples/steve/put-cli.phil`](../../examples/steve/put-cli.phil) — read a path, read its bytes, compute the content ID, and invoke `StevePut`;
- [`../../examples/steve/put.phil`](../../examples/steve/put.phil) — install the candidate bytes under their digest;
- [`../../examples/steve/get-cli.phil`](../../examples/steve/get-cli.phil) — read a content ID and output path, invoke `SteveGet`, then fetch and verify bytes before replacement;
- [`../../examples/steve/get.phil`](../../examples/steve/get.phil) — read an object by ID, verify it, and release the temporary owned bytes.

`test/Phase1INT006SteveApplicationShellMain.hs` parses and checks these exact
files. In particular, it checks the callable identities and signatures rather
than accepting a fixture that merely looks similar.

## PUT: from a file to the provider

The command-facing source starts this way:

```phil
let rawPath = console_read_line(stdin);
let candidatePath = path_parse(rawPath);
let candidate = fs_read(candidatePath);

let contentId = digest_compute(candidate);
invoke StevePut(candidate);
```

`fs_read` produces the owned candidate bytes. `digest_compute` observes those
bytes and produces the content ID without consuming the candidate. The
`invoke StevePut(candidate)` occurrence then transfers the candidate into the
callable according to the checked callable/resource semantics.

Inside `StevePut`, the digest is computed again and the blob provider performs
an install-if-absent operation:

```phil
component StevePut(candidate) {
    let id = digest_compute(candidate);
    branch {
      blob_install(id, candidate) -> { log_write("stored"); }
      otherwise -> { log_write("exists"); }
    }
}
```

The BlobProvider qualification requires install to preserve the candidate
borrow on all public outcomes; installing an object does not silently consume
Steve's owner. It also requires the public no-replace behavior: an already
present object is not overwritten by a second install.

Back in `StevePutCLI`, the content ID computed *before* the invocation remains
available for rendering:

```phil
let renderedId = digest_render_hex(contentId);
console_write(stdout, renderedId);
```

That separation is deliberate. The shell does not try to use `candidate` after
transferring it through the callable occurrence.

## GET: from a content ID to a checked output file

The command-facing GET path first parses the requested content ID and output
path, then invokes `SteveGet`:

```phil
let parsedContentId = digest_parse_hex(rawContentId);
...
let outputPath = path_parse(rawOutputPath);

invoke SteveGet(parsedContentId);
```

`SteveGet` reads the provider object, checks that the bytes still match the
requested digest, and releases its temporary owner on both branches:

```phil
component SteveGet(id) {
    let candidate = blob_read(id);
    branch {
      digest_check(id, candidate) -> { log_write("ok"); release(candidate); }
      otherwise -> { log_write("corrupt"); release(candidate); }
    }
}
```

There is an easy detail to miss here: **the current callable does not return the
bytes it checked**. `invoke SteveGet(parsedContentId)` establishes the callable
behavior, but it does not manufacture an `OwnedBytes` result for the caller.

For that reason, the shell explicitly performs its own provider read and digest
check before publishing anything to the requested output path:

```phil
let candidate = blob_read(parsedContentId);
let accepted = digest_check(parsedContentId, candidate);
branch {
  accepted -> {
    fs_replace(outputPath, candidate);
  }
  otherwise -> {
    release(candidate);
  }
}
```

Only the accepted branch reaches `fs_replace`. A corrupt object therefore cannot
be published merely because it was found under the requested content ID. The
rejected candidate is released instead.

The apparently redundant second read/check is consequently part of the current
source semantics, not tutorial boilerplate. If a future callable signature
returns checked bytes, this walkthrough should change only when the checked
source and conformance harness change with it.

## What provider replacement is allowed to change

Steve does not require every provider implementation to use the same filesystem
layout or Haskell code. It does require the replacement to preserve the checked
public semantics.

For the current witness, that includes at least:

- SHA-256 `compute`/`check` correspondence over the same stable byte-object subject;
- digest operations observing rather than consuming the candidate bytes;
- BlobProvider `read` and install-if-absent outcome behavior;
- no-replace publication;
- no client-visible partial object at the modeled publication boundary;
- explicit disposition of the backing store's broader overwrite/delete authority;
- the required qualification/evidence/admission identity and condition surfaces.

The qualification corpus includes negative controls for these obligations. A
substituted provider mode is therefore not accepted merely because it exports
operations with the right names.

The subsequent manifest-lineage slice binds the selected provider realization
and qualification evidence into the Steve assurance manifest. That means the
provider choice is part of the recorded assurance lineage rather than an
untracked runtime detail.

## Executable pressure already in the repository

Three existing harnesses cover complementary parts of this walkthrough:

- `test/Phase1INT006SteveApplicationShellMain.hs` checks the four canonical Phil source files, callable identities/signatures, operation ordering, resource behavior, and fail-closed provider substitution;
- `test/Phase1INT006SteveCASMain.hs` exercises the concrete content-addressed-store behavior, including install, duplicate install, read, tamper rejection, corrupt-object rejection, invalid IDs, and path failures;
- `runtime/phase1/SteveProviderBridgeSmokeMain.hs` drives the native `StevePut`/`SteveGet` bridge against a real temporary store and checks exact publication, idempotent reinstall, successful verified read, missing-ID failure, and corrupt-object rejection.

For the repository-wide check, use the normal Cabal gate from the repository
root:

```sh
cabal build all
cabal test all
```

Those checks are stronger evidence than copying a transcript into this tutorial:
the tutorial points at the same source and harnesses that continue to run as the
implementation changes.

## The round-trip invariant

For a successful round trip under one qualified provider realization:

```text
input bytes B
    |
    | digest_compute
    v
content id I = SHA256(B)
    |
    | blob_install(I, B)
    v
provider object named I
    |
    | blob_read(I)
    v
candidate B'
    |
    | digest_check(I, B')
    v
publish only when SHA256(B') = I
```

Steve's useful claim is not merely “a file came back.” It is that publication is
conditioned on the bytes still matching the requested content identity, while
the selected provider implementation remains replaceable only inside the
qualified boundary.

## What comes next

This walkthrough closes the documentation item in the current `INT-006` release
sequence. It intentionally stops short of the remaining release evidence:

1. a public Steve/toolchain package with explicit trust/toolchain disclosure;
2. an outside-implementor Linux smoke test performed from that documented package;
3. permanent closeout CI after those release-facing pieces are in place.

Those are separate evidence obligations. Keeping them separate prevents this
repository-level tutorial from being mistaken for proof that an external user
has already reproduced the full packaged path.
