# Phase 2 commitment: continuation-spine decision sugar

## Status

**Committed for Phase 2.**

This is a surface-language ergonomics commitment, not a Phase-1 freeze requirement. Phase 1 keeps the existing explicit `decide` semantics and grammar unchanged.

## Motivation

The Phase-1 Steve CLI examples expose a recurring readability failure mode in otherwise-correct Phil code. Operations such as console input, parsing, filesystem access, digest validation, and replacement return explicit multi-outcome decisions. When one outcome continues and the other outcomes immediately leave the current continuation, writing every step as a nested `decide` produces an Arrow AntiPattern: the ordinary successful path marches progressively to the right while the reader must retain an increasingly deep stack of already-established facts.

`examples/steve/put-cli.phil` and `examples/steve/get-cli.phil` are the motivating examples. The problem is not that Phil makes failure or resource handling explicit; that explicitness is desirable. The problem is that the current surface syntax makes the continuation spine visually subordinate to the exit arms.

Phase 1 already contains a narrow ergonomic precedent in `e or reject reason`: exhaustive checked control can have a flatter surface form without weakening its semantics.

## Commitment

Phase 2 will provide a surface form for **one-continuation decisions**: a decision whose source explicitly selects one outcome as the fall-through continuation while all remaining outcomes are written as explicit exit arms.

The exact syntax is intentionally not frozen by this commitment. A representative shape is:

```phil
let line(pathText) <- console_read_line()
else {
    end-of-input => return unit
    console-failure(reason) => return unit
}

let path(path) <- path_parse(pathText)
else {
    invalid-path(reason) => return unit
}

let found(candidate) <- fs_read(path)
else {
    not-found => return unit
    too-large => return unit
    file-failure(reason) => return unit
}
```

The source names the continuation constructor explicitly. The language must not guess which outcome is "success" from naming, declaration order, or outcome class.

## Required semantic properties

The sugar must elaborate to the same checked control structure as an equivalent exhaustive `decide`. It adds no new control effect and no new resource semantics.

In particular:

1. **Exhaustiveness remains mandatory.** Every non-continuing outcome admitted by the decision must be handled explicitly or by an already-defined exhaustive fallback construct.
2. **The continuation is explicit.** Source names the exact constructor/pattern that falls through; the compiler does not infer a preferred branch.
3. **Exit arms must actually leave the continuation.** An `else` arm may return, reject, fail, or otherwise perform a checked terminal transfer, but may not silently fall through into the continuation spine.
4. **Linear and affine obligations are unchanged.** Every exit arm must discharge, transfer, or otherwise satisfy every live resource obligation exactly as the corresponding nested `decide` arm would.
5. **Borrows and scopes are preserved exactly.** Desugaring must not extend or shorten a loan, resource lifetime, authority scope, protocol state, or callee state.
6. **Outcome identity is preserved.** The sugar may not collapse distinct negative, terminal, fatal, or successful outcomes merely because their source handling happens to be identical.
7. **Diagnostics should describe the flattened source.** Resource leaks, missing outcomes, impossible fall-through, and type mismatches should point at the continuation/exit syntax rather than exposing the elaborated nesting as the programmer-facing model.

## Resource-sensitive example

The construct must remain useful after a linear resource becomes live. For example, the deeply nested tail of Steve GET should be expressible in the style:

```phil
let accepted <- borrow bytes as bytesView {
    digest_check(contentId, bytesView)
}
else {
    rejected(reason) => {
        release bytes
        return unit
    }
}

let replaced <- borrow bytes as outputView {
    fs_replace(path, outputView)
}
else {
    file-failure(reason) => {
        release bytes
        return unit
    }
}

release bytes
return unit
```

This is only acceptable if it checks against exactly the same ownership and borrow obligations as the nested form.

## Non-goals

This commitment does **not** add exceptions, implicit propagation, a Rust-style `?` operator, hidden cleanup, inferred success conventions, automatic conversion of negative outcomes, or helper-function extraction as a substitute for explicit control flow.

It also does not require Phase 2 to adopt the representative `let ... <- ... else { ... }` spelling above. Grammar design should choose a form that composes cleanly with patterns, borrows, typed-negative control, callable outcomes, and the rest of the Phase-2 surface.

## Acceptance criterion

The Phase-2 surface should be able to rewrite the Steve Put/Get CLI continuation spines so that the ordinary path is approximately flat while preserving a mechanically checkable elaboration equivalence to the exhaustive Phase-1 decision tree, including identical resource, outcome, authority, and failure obligations.
